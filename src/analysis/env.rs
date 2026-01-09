// src/analysis/env.rs
use crate::ast::Program;
use crate::analysis::state::State;
use crate::analysis::context::ExecContext;
use std::collections::{HashMap, HashSet};
use crate::domain::Reg;

/// Mirrors `struct bpf_insn_aux_data`.
#[derive(Clone, Default, Debug)]
pub struct InsnAuxData {
    pub prune_point: bool,        // Should we check history here?
    pub seen: bool,               // Has analysis reached this instruction?
    pub live_regs: HashSet<Reg>,  // Which registers are live here?
}

/// The God Object.
/// Holds the Immutable Config (ctx) + Mutable Verification History.
pub struct VerifierEnv<'a> {
    // --- Static Context ---
    /// Access to Maps, BTF, R10/Zero constants, etc.
    pub ctx: &'a ExecContext, 
    pub prog: &'a Program,

    // --- Dynamic Verification State ---
    pub insn_processed: usize,
    pub explored_states: HashMap<usize, Vec<State>>,
    pub insn_aux_data: Vec<InsnAuxData>,
}

impl<'a> VerifierEnv<'a> {
    pub fn new(ctx: &'a ExecContext, prog: &'a Program) -> Self {
        VerifierEnv {
            ctx,
            prog,
            insn_processed: 0,
            explored_states: HashMap::new(),
            insn_aux_data: vec![InsnAuxData::default(); prog.instrs.len()],
        }
    }
}
