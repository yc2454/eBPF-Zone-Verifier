// src/analysis/state.rs
use crate::zone::dbm::Dbm;
use crate::analysis::reg_types::TypeState;
use crate::zone::tnum::Tnum;
use crate::zone::domain::Reg;

/// Mirrors `struct bpf_verifier_state` (partially).
/// Holds the snapshot of execution at a specific PC.
#[derive(Clone, Debug)]
pub struct State {
    /// 1. Register and Stack Types
    /// Mirrors `bpf_reg_state.type`
    pub types: TypeState,

    /// 2. Numerical Domain (Values)
    /// Mirrors `bpf_reg_state.{smin_value, umax_value, var_off}`
    pub dbm: Dbm,
    
    /// Current Program Counter
    pub pc: usize,

    /// History Index (for history tracking, optional)
    pub history_idx: Option<usize>,

    pub tnums: [Tnum; 11], // tnum info for R0-R10
}

impl State {
    pub fn new(dbm: Dbm, pc: usize) -> Self {
        State {
            types: TypeState::new_not_init(),
            dbm,
            pc,
            history_idx: None,
            tnums: [Tnum::unknown(); 11],
        }
    }

    // Helper methods
    pub fn get_tnum(&self, r: Reg) -> Tnum {
        match r {
            Reg::Zero => Tnum::constant(0),
            _ => self.tnums[r.idx() - 1],  // R0 is idx 1, stored at [0]
        }
    }
    
    pub fn set_tnum(&mut self, r: Reg, t: Tnum) {
        if r != Reg::Zero {
            self.tnums[r.idx() - 1] = t;
        }
    }
}