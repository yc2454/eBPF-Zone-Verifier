use crate::analysis::history::History;
// src/analysis/env.rs
use crate::ast::{Program};
use crate::analysis::state::State;
use crate::analysis::context::ExecContext;
use std::collections::{HashMap, HashSet};
use crate::zone::domain::Reg;

#[derive(Clone, Debug)]
pub enum VerificationError {
    StackOutOfBounds { pc: usize, off: i64, size: i64 },
    PointerOutOfBounds { pc: usize },
    UninitializedStackRead { pc: usize, offset: i64 },
    InvalidStackRead { pc: usize, offset: i64 },
    UnsafePacketLoad { pc: usize, off: i16, size: i64 },
    UnsafePacketStore { pc: usize, off: i16, size: i64 },
    IllegalPacketStore { pc: usize, off: i16, size: i64 },
    UnsafeMapLoad { pc: usize, off: i64, size: i64, limit: i64 },
    UnsafeMapStore { pc: usize, off: i64, size: i64, limit: i64 },
    MapStoreForbidden { pc: usize, map_idx: usize },
    MapLoadForbidden { pc: usize, map_idx: usize },
    UnsafeGenericLoad { pc: usize, base: Reg, off: i16 },
    UnsafeMemoryRegionLoad { pc: usize, base: Reg, off: i16 },
    UnsafeCtxAccess { pc: usize, off: i16, size: i64 },
    UnsafeGenericStore { pc: usize, base: Reg, off: i16 },
    UnsafeSocketAccess { pc: usize, off: i16, size: i64 },
    DbmInconsistent { pc: usize },
    ComplexityLimitExceeded { limit: usize },
    RegisterNotReadable { pc: usize, reg: Reg },
    RegisterNotWritable { pc: usize, reg: Reg },
    CfgError(String),
    DivideByZero { pc: usize },
    InvalidArgType { pc: usize, reg: Reg },
    InvalidPointerArithmetic { pc: usize },
    InvalidBPFLoadImmInsn { pc: usize },
    MapNotFound { pc: usize, map_idx: usize },
    BackEdge { pc: usize, target: usize },
    MaxCallDepthExceeded { pc: usize },
    MisalignedAccess { pc: usize, off: i64 },
    InvalidReturnCode { pc: usize },
    MisalignedPacketAccess { pc: usize, off: i16, size: i64 },
    InvalidRegisterTypeState { pc: usize },
    RegisterTypeConflict { pc: usize },
    UnreleasedReference,
}

impl VerificationError {
    pub fn description(&self) -> String {
        match self {
            VerificationError::StackOutOfBounds { pc, off, size } => {
                format!("Stack out of bounds at pc {}: offset {}, size {}", pc, off, size)
            }
            VerificationError::PointerOutOfBounds { pc,  } => {
                format!("Stack out of bounds at pc {}", pc)
            }
            VerificationError::UninitializedStackRead { pc, offset} => {
                format!("Reading uninitialized stack slot at pc {}: offset {}", pc, offset)
            }
            VerificationError::UnsafePacketLoad { pc, off, size } => {
                format!("Unsafe packet load at pc {}: offset {}, size {:?}", pc, off, size)
            }
            VerificationError::UnsafePacketStore { pc, off, size } => {
                format!("Unsafe packet store at pc {}: offset {}, size {:?}", pc, off, size)
            }
            VerificationError::IllegalPacketStore { pc, off, size } => {
                format!("Illegal packet store at pc {}: offset {}, size {:?}", pc, off, size)
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
            VerificationError::UnsafeCtxAccess { pc, off, size } => {
                format!("Unsafe ctx access at pc {}: offset {}, size {:?}", pc, off, size)
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
            VerificationError::UnsafeSocketAccess { pc, off, size } => {
                format!("Unsafe socket access at pc {}: offset {}, size {:?}", pc, off, size)
            }
            VerificationError::UnsafeMemoryRegionLoad { pc, base, off } => {
                format!("Unsafe memory region load at pc {}: base {:?}, offset {}", pc, base, off)
            }
            VerificationError::InvalidArgType { pc, reg } => {
                format!("Invalid argument type at pc {}: register: {}", pc, reg.name())
            }
            VerificationError::InvalidPointerArithmetic { pc } => {
                format!("Invalid pointer arithmetic at pc {}", pc)
            }
            VerificationError::InvalidStackRead { pc, offset } => {
                format!("Invalid stack read at pc {} offset {}", pc, offset)
            }
            VerificationError::RegisterNotReadable { pc, reg } => {
                format!("pc {}: {:?} !read_ok", pc, reg)
            }
            VerificationError::RegisterNotWritable { pc, reg } => {
                format!("pc {}: {:?} !write_ok", pc, reg)
            }
            VerificationError::InvalidBPFLoadImmInsn { pc } => {
                format!("Invalid BPF_LD_IMM instruction at pc {}", pc)
            }
            VerificationError::MapNotFound { pc, map_idx } => {
                format!("Map with ID {} not found at pc {}", map_idx, pc)
            }
            VerificationError::BackEdge { pc, target } => {
                format!("Attempting to jump back to {} at pc {}", target, pc)
            }
            VerificationError::MaxCallDepthExceeded { pc } => {
                format!("Max call depth exceeded at pc {}", pc)
            }
            VerificationError::MisalignedAccess { pc, off } => {
                format!("Misaligned offset with offset {} at pc {}", off, pc)
            }
            VerificationError::InvalidReturnCode { pc } => {
                format!("Invalid return code at pc {}", pc)
            }
            VerificationError::MisalignedPacketAccess { pc, off, size } => {
                format!("Misaligned packet access at pc {}: offset {}, size {:?}", pc, off, size)
            }
            VerificationError::InvalidRegisterTypeState { pc } => {
                format!("Invalid register type state at pc {}", pc)
            }
            VerificationError::MapStoreForbidden { pc, map_idx } => {
                format!("Attemp to write to read-only map {} at pc {}", map_idx, pc)
            }
            VerificationError::MapLoadForbidden { pc, map_idx } => {
                format!("Attemp to read from write-only map {} at pc {}", map_idx, pc)
            }
            VerificationError::RegisterTypeConflict { pc } => {
                format!("Register type conflict at pc {}", pc)
            }
            VerificationError::UnreleasedReference  => {
                format!("Unreleased reference in program")
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
    pub explored_states: HashMap<usize, Vec<State>>,
    pub insn_aux_data: Vec<InsnAuxData>,

    // --- Dynamic State ---
    pub insn_processed: usize,
    /// Holds the FIRST critical failure encountered. 
    /// If this is Some, the analysis should halt immediately.
    pub error: Option<VerificationError>, 
    // Path execution history
    pub history: History
}

impl<'a> VerifierEnv<'a> {
    pub fn new(ctx: &'a ExecContext, prog: &'a Program) -> Self {
        VerifierEnv {
            ctx,
            explored_states: HashMap::new(),
            insn_aux_data: vec![InsnAuxData::default(); prog.instrs.len()],
            insn_processed: 0,
            error: None,
            history: History::new()
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
