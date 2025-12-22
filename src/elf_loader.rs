use std::fs;
use std::path::Path;

use goblin::elf::Elf;

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
