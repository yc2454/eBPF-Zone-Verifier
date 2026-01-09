// src/analysis/state.rs
use crate::dbm::Dbm;
use crate::analysis::reg_types::TypeState;

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
}

impl State {
    pub fn new(dbm: Dbm, pc: usize) -> Self {
        State {
            types: TypeState::new_not_init(),
            dbm,
            pc,
        }
    }

    /// Access to the underlying DBM
    pub fn dbm(&self) -> &Dbm {
        &self.dbm
    }

    pub fn dbm_mut(&mut self) -> &mut Dbm {
        &mut self.dbm
    }
}