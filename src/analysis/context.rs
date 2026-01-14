// src/analysis/context.rs
use crate::zone::domain::{Reg};
use crate::elf_loader::BpfMapDef;
use std::collections::HashMap;
use crate::btf::BtfContext;
use crate::ast::ProgramKind;

#[derive(Clone)]
pub struct ExecContext {
    pub zero: Reg,
    pub r10: Reg,
    pub stack_min: i64,
    pub stack_max: i64,
    pub map_defs: Vec<BpfMapDef>,
    pub pc_to_map_idx: HashMap<usize, usize>,
    pub btf: BtfContext,
    pub prog_kind: ProgramKind,
}

pub fn default_exec_ctx() -> ExecContext {
    ExecContext {
        zero: Reg::Zero,
        r10: Reg::R10,
        stack_min: -512,
        stack_max: 0,
        map_defs: Vec::new(),
        pc_to_map_idx: HashMap::new(),
        btf: BtfContext::new(),
        prog_kind: ProgramKind::Tc,
    }
}
