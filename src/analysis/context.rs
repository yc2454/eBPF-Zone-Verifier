// src/analysis/context.rs
use crate::domain::{Reg, BpfMapDef};
use std::collections::HashMap;
use crate::btf::BtfContext;

#[derive(Clone)]
pub struct ExecContext {
    pub zero: Reg,
    pub r10: Reg,
    pub stack_min: i64,
    pub stack_max: i64,
    pub map_defs: Vec<BpfMapDef>,
    pub pc_to_map_idx: HashMap<usize, usize>,
    pub btf: BtfContext,
}

pub fn default_exec_ctx() -> ExecContext {
    ExecContext {
        zero: Reg::Zero,
        r10: Reg::R10,
        stack_min: -512,
        stack_max: -1,
        map_defs: Vec::new(),
        pc_to_map_idx: HashMap::new(),
        btf: BtfContext::new(),
    }
}
