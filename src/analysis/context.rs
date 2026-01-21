// src/analysis/context.rs
use crate::zone::domain::{Reg};
use crate::parsing::elf_loader::{BpfMapDef, RelocInfo};
use std::collections::HashMap;
use crate::parsing::btf::BtfContext;
use crate::ast::ProgramKind;

#[derive(Clone)]
pub struct ExecContext {
    pub map_defs: Vec<BpfMapDef>,
    pub pc_to_reloc: HashMap<usize, RelocInfo>,
    pub btf: BtfContext,
    pub prog_kind: ProgramKind,
}

pub fn default_exec_ctx() -> ExecContext {
    ExecContext {
        map_defs: Vec::new(),
        pc_to_reloc: HashMap::new(),
        btf: BtfContext::new(),
        prog_kind: ProgramKind::Unknown,
    }
}
