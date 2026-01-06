// src/analysis/context.rs
use crate::domain::{Reg, REG_ENV, BpfMapDef};
use crate::dbm::Dbm;
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

/// Helper: Is v provably in [0, 0xffffffff]?
pub fn proven_u32_range(dbm: &Dbm, v: Reg, zero: Reg) -> bool {
    let vi = REG_ENV.index(v);
    let zi = REG_ENV.index(zero);
    let ub = dbm.raw(vi, zi);
    let lb = dbm.raw(zi, vi);
    // 0 <= v <= u32::MAX
    ub <= 0xffff_ffff && lb <= 0
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
