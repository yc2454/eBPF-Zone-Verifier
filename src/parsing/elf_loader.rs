use std::fs;
use std::path::Path;

use goblin::elf::Elf;
use std::collections::HashMap;
use crate::parsing::btf; // Import the new module
#[derive(Clone, Debug)]
pub struct BpfMapDef {
    pub type_: u32,
    pub key_size: u32,
    pub value_size: u32,
    pub max_entries: u32,
    pub map_flags: u32,
    pub name: String, 
    pub btf_val_type_id: Option<u32>,
}

pub fn load_maps<P: AsRef<Path>>(path: P) -> Result<Vec<BpfMapDef>, ElfLoadError> {
    let buf = fs::read(&path)?;
    let elf = Elf::parse(&buf)?;
    let mut maps = Vec::new();
    let mut btf_data = None;

    // 1. First pass: Check for Legacy Maps and find BTF section
    for (_i, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            if name == "maps" || name == ".maps" {
                // ... (Existing Legacy Parsing Code) ...
                // Keep your existing code here! 
                // But if legacy map size is 0, we might want to overwrite it later.
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
    // If we found legacy maps but they have size 0, or if we found no maps, try BTF.
    let needs_btf = maps.is_empty() || maps.iter().any(|m: &BpfMapDef| m.value_size == 0);

    if needs_btf {
        if let Some(btf_bytes) = btf_data {
            println!("Attempting to load maps from BTF...");
            if let Ok(btf_maps) = btf::parse_btf_map_defs(btf_bytes) {
                // Merge strategy: 
                // If we have legacy maps (names), verify sizes against BTF.
                // If we have nothing, just use BTF.
                
                if maps.is_empty() {
                    println!("Loaded {} maps from BTF", btf_maps.len());
                    maps = btf_maps;
                } else {
                    // Update size-0 maps with data from BTF
                    for m in &mut maps {
                        if m.value_size == 0 {
                            if let Some(btf_m) = btf_maps.iter().find(|bm| bm.name == m.name) {
                                m.value_size = btf_m.value_size;
                                m.key_size = btf_m.key_size;
                                println!("Updated Map '{}' size to {} from BTF", m.name, m.value_size);
                            }
                        }
                    }
                }
            } else {
                println!("Failed to parse BTF section");
            }
        }
    }

    Ok(maps)
}

/// Build a map of Instruction Index -> Map ID
/// Returns: HashMap<PC, MapIndex>
pub fn load_relocations<P: AsRef<Path>>(
    path: P, 
    maps: &[BpfMapDef],
    target_section_name: &str // NEW ARGUMENT
) -> Result<HashMap<usize, usize>, ElfLoadError> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    let mut pc_to_map = HashMap::new();
    let mut sym_name_to_map_idx = HashMap::new();
    
    // Build symbol map
    for (i, m) in maps.iter().enumerate() {
        sym_name_to_map_idx.insert(m.name.as_str(), i);
    }

    // 1. Find the index of the target section (e.g., "tc")
    let target_sec_idx = elf.section_headers.iter().enumerate()
        .find(|(_, sh)| {
            if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
                return name == target_section_name;
            }
            false
        })
        .map(|(i, _)| i)
        .ok_or_else(|| ElfLoadError::SectionNotFound { name: target_section_name.to_string() })?;

    println!("Loading relocations for section '{}' (Index {})", target_section_name, target_sec_idx);

    // 2. Iterate Relocations, but FILTER by target section
    for (reloc_sec_idx, section_relocs) in elf.shdr_relocs.iter() {
        let sh = &elf.section_headers[*reloc_sec_idx];
        
        // sh_info contains the section index these relocations apply to
        if sh.sh_info as usize == target_sec_idx {
            println!("Found matching relocation section index {}", reloc_sec_idx);
            
            for reloc in section_relocs {
                let offset = reloc.r_offset;
                let sym_idx = reloc.r_sym;
                let pc = (offset / 8) as usize;

                if let Some(sym) = elf.syms.get(sym_idx) {
                    if let Some(name) = elf.strtab.get_at(sym.st_name) {
                        // ADD THIS PRINT:
                        println!("  [Loader] Offset {} (PC {}) -> Symbol '{}'", offset, pc, name);

                        if let Some(&map_idx) = sym_name_to_map_idx.get(name) {
                            println!("      -> Mapped to Map Index {}", map_idx); // ADD THIS
                            pc_to_map.insert(pc, map_idx);
                        }
                    }
                }
            }
        }
    }

    Ok(pc_to_map)
}

#[derive(Debug)]
pub enum ElfLoadError {
    Io(std::io::Error),
    Parse(goblin::error::Error),
    NotElf,
    NotBpf { e_machine: u16 },
    SectionNotFound { name: String },
    SectionOutOfBounds { name: String, offset: usize, size: usize, file_len: usize },
}

impl From<std::io::Error> for ElfLoadError {
    fn from(e: std::io::Error) -> Self { ElfLoadError::Io(e) }
}

impl From<goblin::error::Error> for ElfLoadError {
    fn from(e: goblin::error::Error) -> Self { ElfLoadError::Parse(e) }
}

/// Return all section names in the ELF file (useful for discovery/debugging).
pub fn list_section_names<P: AsRef<Path>>(path: P) -> Result<Vec<String>, ElfLoadError> {
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
) -> Result<Vec<u8>, ElfLoadError> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    if require_bpf {
        // EM_BPF is 247
        const EM_BPF: u16 = 247;
        if elf.header.e_machine != EM_BPF {
            return Err(ElfLoadError::NotBpf { e_machine: elf.header.e_machine });
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
    let sh = found.ok_or_else(|| ElfLoadError::SectionNotFound {
        name: section_name.to_string(),
    })?;

    let offset = sh.sh_offset as usize;
    let size = sh.sh_size as usize;

    // Bounds check (ELF can be malformed).
    let file_len = buf.len();
    if offset > file_len || offset + size > file_len {
        return Err(ElfLoadError::SectionOutOfBounds {
            name: section_name.to_string(),
            offset,
            size,
            file_len,
        });
    }

    Ok(buf[offset..offset + size].to_vec())
}

/// Convenience for eBPF: load a program section and assert it looks like an insn stream.
/// eBPF instructions are 8 bytes each; section size should be divisible by 8.
pub fn load_bpf_insn_stream_section<P: AsRef<Path>>(
    path: P,
    section_name: &str,
) -> Result<Vec<u8>, ElfLoadError> {
    let bytes = load_section_bytes(path, section_name, true)?;
    // Divisible-by-8 is a strong sanity check for a raw insn stream section.
    if bytes.len() % 8 != 0 {
        // Reuse SectionOutOfBounds style error to avoid adding another variant;
        // or feel free to add a dedicated error type.
        return Err(ElfLoadError::SectionOutOfBounds {
            name: format!("{section_name} (size not divisible by 8)"),
            offset: 0,
            size: bytes.len(),
            file_len: bytes.len(),
        });
    }
    Ok(bytes)
}
