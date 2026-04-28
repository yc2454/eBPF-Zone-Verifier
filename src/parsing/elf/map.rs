use anyhow::Result;
use goblin::elf::Elf;
use std::fs;
use std::path::Path;

use super::types::BpfMapDef;
use crate::common::constants;
use crate::parsing::btf;
use log::{debug, warn};

/// Load data sections as synthetic maps
pub fn load_data_section_maps<P: AsRef<Path>>(path: P) -> Result<Vec<BpfMapDef>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    let mut maps = vec![];

    for sh in &elf.section_headers {
        let name = elf.shdr_strtab.get_at(sh.sh_name).unwrap_or("");

        let is_data_section = name == ".rodata"
            || name == ".data"
            || name == ".bss"
            || name.starts_with(".rodata.")
            || name.starts_with(".data.");

        if is_data_section && sh.sh_size > 0 {
            let initial_data = if sh.sh_type == constants::SHT_NOBITS {
                Some(vec![0u8; sh.sh_size as usize])
            } else {
                let start = sh.sh_offset as usize;
                let end = start + sh.sh_size as usize;
                if end <= buf.len() {
                    Some(buf[start..end].to_vec())
                } else {
                    None
                }
            };

            let extra_flags = if name.starts_with(".rodata") {
                constants::BPF_F_RDONLY_PROG
            } else {
                0
            };

            maps.push(BpfMapDef {
                type_: constants::BPF_MAP_TYPE_ARRAY,
                key_size: 4,
                value_size: sh.sh_size as u32,
                max_entries: 1,
                map_flags: extra_flags,
                name: name.to_string(),
                btf_val_type_id: None,
                initial_data,
                inner_map_idx: None,
            });
        }
    }

    Ok(maps)
}

pub fn load_maps<P: AsRef<Path>>(path: P) -> Result<Vec<BpfMapDef>> {
    let buf = fs::read(&path)?;
    let elf = Elf::parse(&buf)?;
    let mut maps = Vec::new();
    let mut btf_data = None;

    for (i, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            if name == "maps" || name == ".maps" {
                let start = sh.sh_offset as usize;
                let end = start + sh.sh_size as usize;

                if end > buf.len() {
                    warn!("'maps' section extends beyond file buffer");
                    continue;
                }

                let section_data = &buf[start..end];

                for sym in elf.syms.iter() {
                    if sym.st_shndx == i
                        && let Some(map_name) = elf.strtab.get_at(sym.st_name)
                    {
                        let offset = sym.st_value as usize;
                        let map_size = if sym.st_size > 0 {
                            sym.st_size as usize
                        } else {
                            28
                        };
                        if offset + 20 <= section_data.len() {
                            let read_len = std::cmp::min(map_size, section_data.len() - offset);
                            let b = &section_data[offset..offset + read_len];

                            let inner_map_idx = if read_len >= 24 {
                                Some(u32::from_le_bytes(b[20..24].try_into().unwrap()) as usize)
                            } else {
                                None
                            };

                            // Modern BTF-described maps may omit the
                            // tail fields of the legacy `bpf_map_def`.
                            // Read each field only if `read_len` covers it.
                            let read_u32 = |start: usize| {
                                if read_len >= start + 4 {
                                    u32::from_le_bytes(b[start..start + 4].try_into().unwrap())
                                } else {
                                    0
                                }
                            };
                            maps.push(BpfMapDef {
                                name: map_name.to_string(),
                                type_: read_u32(0),
                                key_size: read_u32(4),
                                value_size: read_u32(8),
                                max_entries: read_u32(12),
                                map_flags: read_u32(16),
                                btf_val_type_id: None,
                                initial_data: None,
                                inner_map_idx,
                            });
                        }
                    }
                }
            } else if name == ".BTF" {
                let start = sh.sh_offset as usize;
                let end = start + sh.sh_size as usize;
                if end <= buf.len() {
                    btf_data = Some(&buf[start..end]);
                }
            }
        }
    }

    let needs_btf = maps.is_empty() || maps.iter().any(|m| m.value_size == 0);
    if needs_btf
        && let Some(btf_bytes) = btf_data
        && let Ok(btf_maps) = btf::parse_btf_map_defs(btf_bytes)
    {
        if maps.is_empty() {
            maps = btf_maps;
        } else {
            for m in &mut maps {
                if let Some(btf_m) = btf_maps.iter().find(|bm| bm.name == m.name) {
                    // Always update type_ and max_entries from BTF when available
                    if m.value_size == 0 {
                        m.value_size = btf_m.value_size;
                        m.key_size = btf_m.key_size;
                    }
                    if m.type_ == 0 {
                        m.type_ = btf_m.type_;
                    }
                    if m.max_entries == 0 {
                        m.max_entries = btf_m.max_entries;
                    }
                    // The legacy `bpf_map_def` section can't carry a value
                    // type id, so the BTF-described copy is the only source
                    // for it. Without this, MapValueSpecial validators
                    // (spin_lock, timer, list_head, rb_root) reject every
                    // ARRAY/HASH map produced by libbpf-style `__type(value, …)`
                    // declarations with "no value-type BTF".
                    if m.btf_val_type_id.is_none() {
                        m.btf_val_type_id = btf_m.btf_val_type_id;
                    }
                    // BTF-described maps encode `__uint(map_flags, …)` in BTF;
                    // the legacy `bpf_map_def` slot in the .maps section reads
                    // as 0. Trust BTF when the section side is unset.
                    if m.map_flags == 0 {
                        m.map_flags = btf_m.map_flags;
                    }
                }
            }
        }
    }

    for m in &mut maps {
        if m.value_size == 0
            && matches!(
                m.type_,
                constants::BPF_MAP_TYPE_ARRAY_OF_MAPS | constants::BPF_MAP_TYPE_HASH_OF_MAPS
            )
        {
            // Legacy map of maps without inner map info. Fallback to 4 for basic analysis.
            m.value_size = 4;
        }
    }

    for (i, m) in maps.iter().enumerate() {
        debug!(
            "Map [{}]: name={}, type={}, key_size={}, value_size={}, max_entries={}",
            i, m.name, m.type_, m.key_size, m.value_size, m.max_entries
        );
    }

    Ok(maps)
}
