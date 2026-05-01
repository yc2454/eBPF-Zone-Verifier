use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::history::History;
// src/analysis/env.rs
use crate::analysis::machine::context::ExecContext;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::Program;
use crate::pcc::ProgramCertificate;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default, Debug)]
pub struct InsnAuxData {
    pub prune_point: bool,
    pub seen: bool,
    /// Registers that are live (read before next write) at this PC.
    pub live_regs: HashSet<Reg>,
    /// Stack slot offsets (byte-granularity, relative to R10) that are live at this PC.
    pub live_slots: HashSet<i16>,
}

pub struct VerifierEnv<'a> {
    pub ctx: &'a ExecContext,
    pub explored_states: HashMap<usize, Vec<State>>,
    pub insn_aux_data: Vec<InsnAuxData>,
    pub invalid_pc_set: HashSet<usize>,
    pub addr_space_cast_to_arena_pcs: HashSet<usize>,

    // --- Dynamic State ---
    pub insn_processed: usize,
    /// Holds the FIRST critical failure encountered.
    /// If this is Some, the analysis should halt immediately.
    pub error: Option<VerificationError>,
    // Path execution history
    pub history: History,
    // Optional PCC certificate loaded from CLI.
    pub certificate: Option<ProgramCertificate>,
    /// True while `analyze_exception_cb` is running. Mirrors the kernel's
    /// `frame->in_exception_callback_fn`: switches the main-frame exit
    /// check to the exception-cb-specific rule (R0 ∈ [0, 0] for fentry/
    /// fexit) without affecting ordinary main-program exits.
    pub analyzing_exception_cb: bool,
}

impl<'a> VerifierEnv<'a> {
    pub fn new(
        ctx: &'a ExecContext,
        prog: &'a Program,
        certificate: Option<ProgramCertificate>,
    ) -> Self {
        VerifierEnv {
            ctx,
            explored_states: HashMap::new(),
            insn_aux_data: vec![InsnAuxData::default(); prog.instrs.len()],
            invalid_pc_set: prog.invalid_pc_set.clone(),
            addr_space_cast_to_arena_pcs: prog.addr_space_cast_to_arena_pcs.clone(),
            insn_processed: 0,
            error: None,
            history: History::new(),
            certificate,
            analyzing_exception_cb: false,
        }
    }

    /// Report a failure. Only the first failure is recorded.
    pub fn fail(&mut self, err: VerificationError) {
        if self.error.is_none() {
            self.error = Some(err);
        }
    }

    pub fn failed(&self) -> bool {
        self.error.is_some()
    }
}
