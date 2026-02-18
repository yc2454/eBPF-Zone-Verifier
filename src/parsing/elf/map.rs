use anyhow::Result;
use goblin::elf::Elf;
use std::fs;
use std::path::Path;

use super::types::BpfMapDef;
use crate::common::constants;
use crate::parsing::btf;
use log::warn;

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
                const MAP_DEF_SIZE: usize = 20;

                for sym in elf.syms.iter() {
                    if sym.st_shndx == i {
                        if let Some(map_name) = elf.strtab.get_at(sym.st_name) {
                            let offset = sym.st_value as usize;
                            if offset + MAP_DEF_SIZE <= section_data.len() {
                                let b = &section_data[offset..offset + MAP_DEF_SIZE];
                                maps.push(BpfMapDef {
                                    name: map_name.to_string(),
                                    type_: u32::from_le_bytes(b[0..4].try_into().unwrap()),
                                    key_size: u32::from_le_bytes(b[4..8].try_into().unwrap()),
                                    value_size: u32::from_le_bytes(b[8..12].try_into().unwrap()),
                                    max_entries: u32::from_le_bytes(b[12..16].try_into().unwrap()),
                                    map_flags: u32::from_le_bytes(b[16..20].try_into().unwrap()),
                                    btf_val_type_id: None,
                                    initial_data: None,
                                });
                            }
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
    if needs_btf {
        if let Some(btf_bytes) = btf_data {
            if let Ok(btf_maps) = btf::parse_btf_map_defs(btf_bytes) {
                if maps.is_empty() {
                    maps = btf_maps;
                } else {
                    for m in &mut maps {
                        if m.value_size == 0 {
                            if let Some(btf_m) = btf_maps.iter().find(|bm| bm.name == m.name) {
                                m.value_size = btf_m.value_size;
                                m.key_size = btf_m.key_size;
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(maps)
}
