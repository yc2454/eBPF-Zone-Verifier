use std::fs;
use std::path::Path;

use goblin::elf::Elf;
use std::collections::HashMap;
use crate::domain::BpfMapDef;

/// Parse the "maps" section into a vector of definitions.
/// Assumes standard "struct bpf_map_def" layout (20-28 bytes depending on padding).
pub fn load_maps<P: AsRef<Path>>(path: P) -> Result<Vec<BpfMapDef>, ElfLoadError> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    let mut maps = Vec::new();

    // 1. Find the "maps" section
    for (i, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            if name == "maps" {
                let start = sh.sh_offset as usize;
                let end = start + sh.sh_size as usize;
                let data = &buf[start..end];
                
                // 2. Iterate chunks. standard bpf_map_def is 24 or 28 bytes.
                // Let's assume 28 bytes (u32 type, key, val, max, flags, inner_idx/padding).
                // Or 24 bytes (older). Calico usually uses standard sizes.
                // Let's try to parse based on symbol sizes or fixed stride.
                
                // Better strategy: Use the Symbol Table. 
                // Symbols in the "maps" section point to the start of each definition.
                for sym in &elf.syms {
                    if sym.st_shndx == i {
                        // This symbol is in the maps section.
                        let offset = sym.st_value as usize; // Offset within the section data? 
                        // Note: st_value for relocatable files is offset within section.
                        
                        if offset + 20 <= data.len() {
                            // Manual parsing of C struct (Little Endian)
                            let d = &data[offset..];
                            let type_ = u32::from_le_bytes(d[0..4].try_into().unwrap());
                            let key = u32::from_le_bytes(d[4..8].try_into().unwrap());
                            let val = u32::from_le_bytes(d[8..12].try_into().unwrap());
                            let max = u32::from_le_bytes(d[12..16].try_into().unwrap());
                            let flags = u32::from_le_bytes(d[16..20].try_into().unwrap());
                            
                            let name = elf.strtab.get_at(sym.st_name).unwrap_or("<unknown>").to_string();

                            maps.push(BpfMapDef {
                                type_,
                                key_size: key,
                                value_size: val,
                                max_entries: max,
                                map_flags: flags,
                                name,
                            });
                        }
                    }
                }
            }
        }
    }
    
    // Sort maps by the order they appear? Actually, relocations refer to Symbols.
    // We need to return a map of SymbolIndex -> MapDef
    // But for simplicity, let's just return the list and we'll resolve via symbols later.
    Ok(maps)
}

/// Build a map of Instruction Index -> Map ID
/// Returns: HashMap<PC, MapIndex>
pub fn load_relocations<P: AsRef<Path>>(path: P, maps: &[BpfMapDef]) -> Result<HashMap<usize, usize>, ElfLoadError> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    let mut pc_to_map = HashMap::new();

    // Find the symbol indices that correspond to our maps
    // We map "Symbol Name" to "Index in `maps` vector"
    let mut sym_name_to_map_idx = HashMap::new();
    for (i, m) in maps.iter().enumerate() {
        sym_name_to_map_idx.insert(m.name.as_str(), i);
    }

    // Find .rel.text or .rel<section_name>
    // For simplicity, let's scan all Relocation Sections
    for sh in &elf.section_headers {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            // Check if this is a relocation section for our code
            // (You might need to be more specific, e.g., ".rel.text")
            if name.starts_with(".rel") {
                // Parse relocations
                let start = sh.sh_offset as usize;
                let end = start + sh.sh_size as usize;
                // Goblin provides an iterator if we just used sh_type, but let's assume we use the data:
                // Actually goblin `elf.shdr_relocs` iterates all.
            }
        }
    }

    // Goblin exposes relocations directly on the section if we iterate them.
    // But simplest way with Goblin:
    for (sec_idx, section_relocs) in elf.shdr_relocs.iter() {
         // Is this section modifying the text section?
         // We'd need to check if section `sec_idx` target is the text section.
         // Let's assume yes for the main code.
         
         for reloc in section_relocs {
             let offset = reloc.r_offset; // Byte offset in code
             let sym_idx = reloc.r_sym;   // Symbol table index
             
             // Calculate PC: offset / 8
             let pc = (offset / 8) as usize;

             // Resolve symbol
             if let Some(sym) = elf.syms.get(sym_idx) {
                 if let Some(name) = elf.strtab.get_at(sym.st_name) {
                     if let Some(&map_idx) = sym_name_to_map_idx.get(name) {
                         // Found it! This instruction loads this map.
                         pc_to_map.insert(pc, map_idx);
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
