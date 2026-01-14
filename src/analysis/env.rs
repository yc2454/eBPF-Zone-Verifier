// src/analysis/env.rs
use crate::ast::{Program, MemSize};
use crate::analysis::state::State;
use crate::analysis::context::ExecContext;
use std::collections::{HashMap, HashSet};
use crate::zone::domain::Reg;

#[derive(Clone, Debug)]
pub enum VerificationError {
    UnsafeStackLoad { pc: usize, off: i16, size: MemSize },
    UnsafeStackStore { pc: usize, off: i16, size: MemSize },
    UnsafePacketLoad { pc: usize, off: i16, size: MemSize, range: u64 },
    UnsafePacketStore { pc: usize, off: i16, size: MemSize },
    UnsafeMapLoad { pc: usize, off: i64, size: MemSize, limit: i64 },
    UnsafeMapStore { pc: usize, off: i64, size: MemSize, limit: i64 },
    UnsafeGenericLoad { pc: usize, base: Reg, off: i16 },
    UnsafeGenericStore { pc: usize, base: Reg, off: i16 },
    DbmInconsistent { pc: usize },
    ComplexityLimitExceeded { limit: usize },
    CfgError(String),
    DivideByZero { pc: usize },
}

impl VerificationError {
    pub fn description(&self) -> String {
        match self {
            VerificationError::UnsafeStackLoad { pc, off, size } => {
                format!("Unsafe stack load at pc {}: offset {}, size {:?}", pc, off, size)
            }
            VerificationError::UnsafeStackStore { pc, off, size } => {
                format!("Unsafe stack store at pc {}: offset {}, size {:?}", pc, off, size)
            }
            VerificationError::UnsafePacketLoad { pc, off, size, range } => {
                format!("Unsafe packet load at pc {}: offset {}, size {:?}, range {}", pc, off, size, range)
            }
            VerificationError::UnsafePacketStore { pc, off, size } => {
                format!("Unsafe packet store at pc {}: offset {}, size {:?}", pc, off, size)
            }
            VerificationError::UnsafeMapLoad { pc, off, size, limit } => {
                format!("Unsafe map load at pc {}: offset {}, size {:?}, limit {}", pc, off, size, limit)
            }
            VerificationError::UnsafeMapStore { pc, off, size, limit } => {
                format!("Unsafe map store at pc {}: offset {}, size {:?}, limit {}", pc, off, size, limit)
            }
            VerificationError::UnsafeGenericLoad { pc, base, off } => {
                format!("Unsafe generic load at pc {}: base {:?}, offset {}", pc, base, off)
            }
            VerificationError::UnsafeGenericStore { pc, base, off } => {
                format!("Unsafe generic store at pc {}: base {:?}, offset {}", pc, base, off)
            }
            VerificationError::DbmInconsistent { pc } => {
                format!("DBM inconsistent at pc {}", pc)
            }
            VerificationError::ComplexityLimitExceeded { limit } => {
                format!("Complexity limit of {} exceeded", limit)
            }
            VerificationError::CfgError(msg) => {
                format!("CFG error: {}", msg)
            }
            VerificationError::DivideByZero { pc } => {
                format!("Potential divide by zero at pc {}", pc)
            }
        }
    }
}

#[derive(Clone, Default, Debug)]
pub struct InsnAuxData {
    pub prune_point: bool,
    pub seen: bool,
    pub live_regs: HashSet<Reg>,
}

pub struct VerifierEnv<'a> {
    pub ctx: &'a ExecContext, 
    pub prog: &'a Program,
    pub explored_states: HashMap<usize, Vec<State>>,
    pub insn_aux_data: Vec<InsnAuxData>,

    // --- Dynamic State ---
    pub insn_processed: usize,
    /// Holds the FIRST critical failure encountered. 
    /// If this is Some, the analysis should halt immediately.
    pub error: Option<VerificationError>, 
}

impl<'a> VerifierEnv<'a> {
    pub fn new(ctx: &'a ExecContext, prog: &'a Program) -> Self {
        VerifierEnv {
            ctx,
            prog,
            explored_states: HashMap::new(),
            insn_aux_data: vec![InsnAuxData::default(); prog.instrs.len()],
            insn_processed: 0,
            error: None,
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
