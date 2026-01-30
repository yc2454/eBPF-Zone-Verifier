use std::fs;
use std::path::Path;

use goblin::elf::{Elf, sym};
use std::collections::HashMap;
use crate::parsing::btf;
use log::{info, debug, warn};
use crate::common::constants;
use anyhow::Result;


#[derive(Clone, Debug)]
pub struct BpfMapDef {
    pub type_: u32,
    pub key_size: u32,
    pub value_size: u32,
    pub max_entries: u32,
    pub map_flags: u32,
    pub name: String, 
    pub btf_val_type_id: Option<u32>,

    pub initial_data: Option<Vec<u8>>,
}

/// Represents a raw BPF program extracted from the ELF symbol table.
/// This corresponds to a single C function in the source code.
#[derive(Debug)]
pub struct RawBpfProgram {
    pub name: String,
    pub data: Vec<u8>,      // The raw bytecode slice
    pub section_idx: usize, // Which ELF section it lives in (e.g., .text)
    pub file_offset: u64,   // Absolute offset in the file (for debugging)
}

#[derive(Clone, Debug)]
pub struct RelocInfo {
    pub map_idx: usize,
    pub offset: i64,
}

/// Load data sections as synthetic maps
pub fn load_data_section_maps<P: AsRef<Path>>(path: P) -> Result<Vec<BpfMapDef>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;
    
    let mut maps = vec![];
    
    for sh in &elf.section_headers {
        let name = elf.shdr_strtab.get_at(sh.sh_name).unwrap_or("");
        
        let is_data_section = 
            name == ".rodata" ||
            name == ".data" ||
            name == ".bss" ||
            name.starts_with(".rodata.") ||
            name.starts_with(".data.");
        
        if is_data_section && sh.sh_size > 0 {
            let initial_data = 
                if sh.sh_type == constants::SHT_NOBITS { // SHT_NOBITS (e.g. .bss)
                    // .bss is zero-initialized memory, not stored in file.
                    // We create a vector of zeros.
                    Some(vec![0u8; sh.sh_size as usize])
                } else {
                    // .rodata / .data are stored in the file.
                    let start = sh.sh_offset as usize;
                    let end = start + sh.sh_size as usize;
                    // Bounds check to be safe
                    if end <= buf.len() {
                        Some(buf[start..end].to_vec())
                    } else {
                        None // Should typically return an error, but we'll stick to 'None' to be safe
                    }
                };

            // Set Read-Only flag for .rodata
            // This helps the verifier know writes are illegal.
            let extra_flags = if name.starts_with(".rodata") {
                constants::BPF_F_RDONLY_PROG 
            } else {
                0
            };
            // ---------------------------------------------------------------

            maps.push(BpfMapDef {
                type_: constants::BPF_MAP_TYPE_ARRAY,
                key_size: 4,
                value_size: sh.sh_size as u32,
                max_entries: 1,
                map_flags: 0 | extra_flags, // Extend flags
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

    // 1. First pass: Check for Legacy Maps and find BTF section
    for (_i, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            if name == "maps" || name == ".maps" {
                // 1. Get the raw bytes for this section
                let start = sh.sh_offset as usize;
                let end = start + sh.sh_size as usize;
                
                if end > buf.len() {
                    eprintln!("Warning: 'maps' section extends beyond file buffer");
                    continue;
                }
                
                let section_data = &buf[start..end];
                
                // Legacy bpf_map_def is 20 bytes (5 * u32)
                const MAP_DEF_SIZE: usize = 20;

                // 2. Iterate over symbols to find maps defined in this section
                for sym in elf.syms.iter() {
                    // Check if symbol belongs to this section index (_i)
                    if sym.st_shndx == _i {
                        if let Some(map_name) = elf.strtab.get_at(sym.st_name) {
                            let offset = sym.st_value as usize;

                            // Ensure we can read the full struct
                            if offset + MAP_DEF_SIZE <= section_data.len() {
                                let b = &section_data[offset..offset + MAP_DEF_SIZE];
                                
                                // Parse fields (Little Endian)
                                let type_ = u32::from_le_bytes(b[0..4].try_into().unwrap());
                                let key_size = u32::from_le_bytes(b[4..8].try_into().unwrap());
                                let value_size = u32::from_le_bytes(b[8..12].try_into().unwrap());
                                let max_entries = u32::from_le_bytes(b[12..16].try_into().unwrap());
                                let map_flags = u32::from_le_bytes(b[16..20].try_into().unwrap());
                                
                                maps.push(BpfMapDef {
                                    name: map_name.to_string(),
                                    type_,           // Matches your struct field
                                    key_size,
                                    value_size,
                                    max_entries,
                                    map_flags,       // Matches your struct field
                                    btf_val_type_id: None, // Legacy maps don't have BTF IDs here
                                    initial_data: None,    // Legacy maps don't support initial data
                                });
                            }
                        }
                    }
                }
            } 
            else if name == ".BTF" {
                let start = sh.sh_offset as usize;
                let end = start + sh.sh_size as usize;
                if end <= buf.len() {
                    btf_data = Some(&buf[start..end]);
                }
            }
        }
    }

    // 2. BTF Fallback strategy
    let needs_btf = maps.is_empty() || maps.iter().any(|m: &BpfMapDef| m.value_size == 0);

    if needs_btf {
        if let Some(btf_bytes) = btf_data {
            info!(target: "app", "Attempting to load maps from BTF section...");
            
            if let Ok(btf_maps) = btf::parse_btf_map_defs(btf_bytes) {
                if maps.is_empty() {
                    info!(target: "app", "Loaded {} maps directly from BTF", btf_maps.len());
                    maps = btf_maps;
                } else {
                    // Update size-0 maps with data from BTF
                    for m in &mut maps {
                        if m.value_size == 0 {
                            if let Some(btf_m) = btf_maps.iter().find(|bm| bm.name == m.name) {
                                m.value_size = btf_m.value_size;
                                m.key_size = btf_m.key_size;
                                debug!(target: "app", "Updated Map '{}' size to {} from BTF", m.name, m.value_size);
                            }
                        }
                    }
                }
            } else {
                warn!(target: "app", "Failed to parse BTF section, map definitions might be incomplete.");
            }
        }
    }

    Ok(maps)
}

pub fn load_relocations<P: AsRef<Path>>(
    path: P, 
    maps: &[BpfMapDef],
    target_section_name: &str,
) -> Result<HashMap<usize, RelocInfo>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    let mut pc_to_reloc = HashMap::new();
    
    // Build name -> index lookup
    let mut map_name_to_idx: HashMap<&str, usize> = HashMap::new();
    for (i, m) in maps.iter().enumerate() {
        map_name_to_idx.insert(m.name.as_str(), i);
    }
    
    // Build section_idx -> map_idx (for data section symbols)
    let mut section_idx_to_map_idx: HashMap<usize, usize> = HashMap::new();
    for (sec_idx, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            if let Some(&map_idx) = map_name_to_idx.get(name) {
                section_idx_to_map_idx.insert(sec_idx, map_idx);
            }
        }
    }

    // Find target section index
    let target_sec_idx = elf.section_headers.iter().enumerate()
        .find(|(_, sh)| {
            elf.shdr_strtab.get_at(sh.sh_name) == Some(target_section_name)
        })
        .map(|(i, _)| i)
        .ok_or_else(|| anyhow::anyhow!("Section '{}' not found", target_section_name))?;

    info!(target: "app", "Loading relocations for section '{}' (Index {})", target_section_name, target_sec_idx);

    // Iterate relocations
    for (reloc_sec_idx, section_relocs) in elf.shdr_relocs.iter() {
        let sh = &elf.section_headers[*reloc_sec_idx];
        
        if sh.sh_info as usize != target_sec_idx {
            continue;
        }
        
        debug!(target: "app", "Found relocation section at index {}", reloc_sec_idx);
        
        for reloc in section_relocs {
            let pc = (reloc.r_offset / 8) as usize;
            let sym_idx = reloc.r_sym;

            let sym = match elf.syms.get(sym_idx) {
                Some(s) => s,
                None => continue,
            };
            
            let name = match elf.strtab.get_at(sym.st_name) {
                Some(n) => n,
                None => continue,
            };
            
            // Using debug! to prevent spamming the console on successful loads
            debug!(target: "app", "  [Loader] Offset {} (PC {}) -> Symbol '{}'", reloc.r_offset, pc, name);

            // Try 1: Direct map name match
            if let Some(&map_idx) = map_name_to_idx.get(name) {
                debug!(target: "app", "      -> Direct match to Map Index {}", map_idx);
                pc_to_reloc.insert(pc, RelocInfo { map_idx, offset: 0 });
                continue;
            }
            
            // Try 2: Symbol in a data section
            if let Some(&map_idx) = section_idx_to_map_idx.get(&sym.st_shndx) {
                let offset = sym.st_value as i64;
                debug!(target: "app", "      -> Data section symbol, Map Index {}, Offset {}", map_idx, offset);
                pc_to_reloc.insert(pc, RelocInfo { map_idx, offset });
                continue;
            }
            
            warn!(target: "app", "      -> Unresolved relocation: Symbol '{}' not found in maps.", name);
        }
    }

    Ok(pc_to_reloc)
}

/// Return all section names in the ELF file (useful for discovery/debugging).
pub fn list_section_names<P: AsRef<Path>>(path: P) -> Result<Vec<String>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    let mut out = Vec::new();
    for sh in &elf.section_headers {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            out.push(name.to_string());
        }
    }
    Ok(out)
}

/// Load the raw bytes of a named section (e.g. "tc") from an ELF object.
/// This is the function you want for feeding the BPF decoder.
///
/// If `require_bpf` is true, we reject non-eBPF ELF objects (e_machine != EM_BPF).
pub fn load_section_bytes<P: AsRef<Path>>(
    path: P,
    section_name: &str,
    require_bpf: bool,
) -> Result<Vec<u8>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    if require_bpf {
        // EM_BPF is 247
        const EM_BPF: u16 = 247;
        if elf.header.e_machine != EM_BPF {
            return Err(anyhow::anyhow!("Not an eBPF ELF object: e_machine = {}", elf.header.e_machine));
        }
    }

    // Find the section header whose name matches.
    let mut found = None;
    for sh in &elf.section_headers {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            if name == section_name {
                found = Some(sh);
                break;
            }
        }
    }
    let sh = found.ok_or_else(|| anyhow::anyhow!("Section '{}' not found", section_name))?;

    let offset = sh.sh_offset as usize;
    let size = sh.sh_size as usize;

    // Bounds check (ELF can be malformed).
    let file_len = buf.len();
    if offset > file_len || offset + size > file_len {
        return Err(anyhow::anyhow!("Section '{}' out of bounds: offset {}, size {}, file length {}", section_name, offset, size, file_len));
    }

    Ok(buf[offset..offset + size].to_vec())
}

/// Convenience for eBPF: load a program section and assert it looks like an insn stream.
/// eBPF instructions are 8 bytes each; section size should be divisible by 8.
pub fn load_bpf_insn_stream_section<P: AsRef<Path>>(
    path: P,
    section_name: &str,
) -> Result<Vec<u8>> {
    let bytes = load_section_bytes(path, section_name, true)?;
    // Divisible-by-8 is a strong sanity check for a raw insn stream section.
    if bytes.len() % 8 != 0 {
        // Reuse SectionOutOfBounds style error to avoid adding another variant;
        // or feel free to add a dedicated error type.
        return Err(anyhow::anyhow!("Section '{}' size not divisible by 8: size {}", section_name, bytes.len()));
    }
    Ok(bytes)
}

/// Iterates over the ELF Symbol Table to find all BPF programs.
pub fn load_raw_programs<P: AsRef<Path>>(path: P) -> Result<Vec<RawBpfProgram>> {
    let bytes = fs::read(path)?;
    let elf = Elf::parse(&bytes)?;
    
    let mut programs = Vec::new();

    for sym in elf.syms.iter() {
        // Strict Check: Only load symbols explicitly marked as Functions.
        // This splits the .text section into individual programs.
        let is_func = sym.st_type() == sym::STT_FUNC;
        
        if is_func && sym.st_shndx < elf.section_headers.len() {
            let name = elf.strtab.get_at(sym.st_name)
                .unwrap_or("<unknown>")
                .to_string();

            let shdr = &elf.section_headers[sym.st_shndx];
            
            // In relocatable .o files, st_value is the offset from the start of the section
            let offset_in_section = sym.st_value as usize;
            let file_offset = shdr.sh_offset as usize + offset_in_section;
            let size = sym.st_size as usize;

            // Bounds sanity check
            if file_offset + size <= bytes.len() {
                programs.push(RawBpfProgram {
                    name,
                    data: bytes[file_offset..file_offset + size].to_vec(),
                    section_idx: sym.st_shndx,
                    file_offset: file_offset as u64,
                });
            }
        }
    }

    Ok(programs)
}
