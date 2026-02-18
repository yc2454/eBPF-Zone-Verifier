use anyhow::Result;
use goblin::elf::{Elf, sym};
use std::fs;
use std::path::Path;

use super::types::RawBpfProgram;

pub fn load_section_bytes<P: AsRef<Path>>(
    path: P,
    section_name: &str,
    require_bpf: bool,
) -> Result<Vec<u8>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;

    if require_bpf {
        const EM_BPF: u16 = 247;
        if elf.header.e_machine != EM_BPF {
            return Err(anyhow::anyhow!("Not an eBPF ELF object"));
        }
    }

    let sh = elf
        .section_headers
        .iter()
        .find(|sh| elf.shdr_strtab.get_at(sh.sh_name) == Some(section_name))
        .ok_or_else(|| anyhow::anyhow!("Section '{}' not found", section_name))?;

    let offset = sh.sh_offset as usize;
    let size = sh.sh_size as usize;

    if offset + size > buf.len() {
        return Err(anyhow::anyhow!("Section out of bounds"));
    }

    Ok(buf[offset..offset + size].to_vec())
}

pub fn load_bpf_insn_stream_section<P: AsRef<Path>>(
    path: P,
    section_name: &str,
) -> Result<Vec<u8>> {
    load_section_bytes(path, section_name, true)
}

pub fn load_raw_programs<P: AsRef<Path>>(path: P) -> Result<Vec<RawBpfProgram>> {
    let bytes = fs::read(path)?;
    let elf = Elf::parse(&bytes)?;
    let mut programs = Vec::new();

    for sym in elf.syms.iter() {
        if sym.st_type() == sym::STT_FUNC && sym.st_shndx < elf.section_headers.len() {
            let name = elf
                .strtab
                .get_at(sym.st_name)
                .unwrap_or("<unknown>")
                .to_string();
            let shdr = &elf.section_headers[sym.st_shndx];
            let file_offset = shdr.sh_offset as usize + sym.st_value as usize;
            let size = sym.st_size as usize;

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

pub fn list_section_names<P: AsRef<Path>>(path: P) -> Result<Vec<String>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;
    Ok(elf
        .section_headers
        .iter()
        .filter_map(|sh| elf.shdr_strtab.get_at(sh.sh_name))
        .map(|s| s.to_string())
        .collect())
}
