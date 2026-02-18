use anyhow::Result;
use goblin::elf::Elf;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

use super::types::{BpfMapDef, RelocInfo, RelocKind};
use crate::parsing::bpf_insn::RawBpfInsn;

pub fn load_relocations<P: AsRef<Path>>(
    path: P,
    maps: &[BpfMapDef],
    target_section_name: &str,
) -> Result<HashMap<usize, RelocInfo>> {
    let buf = fs::read(path)?;
    let elf = Elf::parse(&buf)?;
    let mut pc_to_reloc = HashMap::new();

    let mut map_name_to_idx: HashMap<&str, usize> = HashMap::new();
    for (i, m) in maps.iter().enumerate() {
        map_name_to_idx.insert(m.name.as_str(), i);
    }

    let mut section_idx_to_map_idx: HashMap<usize, usize> = HashMap::new();
    for (sec_idx, sh) in elf.section_headers.iter().enumerate() {
        if let Some(name) = elf.shdr_strtab.get_at(sh.sh_name) {
            if let Some(&map_idx) = map_name_to_idx.get(name) {
                section_idx_to_map_idx.insert(sec_idx, map_idx);
            }
        }
    }

    let target_sec_idx = elf
        .section_headers
        .iter()
        .enumerate()
        .find(|(_, sh)| elf.shdr_strtab.get_at(sh.sh_name) == Some(target_section_name))
        .map(|(i, _)| i)
        .ok_or_else(|| anyhow::anyhow!("Section '{}' not found", target_section_name))?;

    for (reloc_sec_idx, section_relocs) in elf.shdr_relocs.iter() {
        let sh = &elf.section_headers[*reloc_sec_idx];
        if sh.sh_info as usize != target_sec_idx {
            continue;
        }

        for reloc in section_relocs {
            let pc = (reloc.r_offset / 8) as usize;
            let sym = match elf.syms.get(reloc.r_sym) {
                Some(s) => s,
                None => continue,
            };
            let name = elf.strtab.get_at(sym.st_name).unwrap_or("");

            if let Some(&map_idx) = map_name_to_idx.get(name) {
                pc_to_reloc.insert(
                    pc,
                    RelocInfo {
                        map_idx,
                        offset: 0,
                        kind: RelocKind::MapPtr,
                    },
                );
            } else if let Some(&map_idx) = section_idx_to_map_idx.get(&sym.st_shndx) {
                pc_to_reloc.insert(
                    pc,
                    RelocInfo {
                        map_idx,
                        offset: sym.st_value as i64,
                        kind: RelocKind::MapValue,
                    },
                );
            }
        }
    }
    Ok(pc_to_reloc)
}

/// Patch raw BPF instructions with relocation info.
/// This allows the lowerer (bpf_to_ast) to identify map pointers/values correctly.
pub fn apply_relocs(insns: &mut [RawBpfInsn], pc_to_reloc: &HashMap<usize, RelocInfo>) {
    for (&pc, reloc) in pc_to_reloc {
        if pc < insns.len() {
            let insn = &mut insns[pc];
            // Identify if this is a BPF_LD_IMM64 instruction (0x18)
            if insn.code == 0x18 {
                // For map pointers, we set src_reg = 1 and imm = map_idx
                // For map values, we set src_reg = 2 and imm = map_idx
                // The continuation instruction (pc + 1) will hold the offset.
                match reloc.kind {
                    RelocKind::MapPtr => {
                        insn.src = 1;
                        insn.imm = reloc.map_idx as i32;
                    }
                    RelocKind::MapValue => {
                        insn.src = 2;
                        insn.imm = reloc.map_idx as i32;
                        // The offset should be put in the continuation instruction's imm field
                        if pc + 1 < insns.len() {
                            insns[pc + 1].imm = reloc.offset as i32;
                        }
                    }
                }
            }
        }
    }
}
