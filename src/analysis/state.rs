// src/analysis/state.rs
use crate::zone::dbm::Dbm;
use crate::analysis::reg_types::TypeState;
use crate::zone::tnum::Tnum;
use crate::zone::domain::Reg;
use std::collections::HashMap;

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

    pub tnums: HashMap<Reg, Tnum>, // tnum info for R0-R10

    /// Call stack for BPF-to-BPF function calls.
    /// Stores return addresses (PC + 1 of CallRel instructions).
    /// Empty for main function; populated when entering subfunctions.
    pub call_stack: Vec<usize>,
}

impl State {
    pub fn new(dbm: Dbm, pc: usize) -> Self {
        let mut tnums = HashMap::new();
        tnums.insert(Reg::Zero, Tnum::constant(0));
        for r in Reg::ALL {
            if r != Reg::Zero {
                tnums.insert(r, Tnum::unknown());
            }
        }
        State {
            types: TypeState::new_not_init(),
            dbm,
            pc,
            history_idx: None,
            tnums: tnums.clone(),
            call_stack: Vec::new()
        }
    }

    // Helper methods
    pub fn get_tnum(&self, r: Reg) -> Tnum {
        match r {
            Reg::Zero => Tnum::constant(0),
            _ => {
                let t_op = self.tnums.get(&r);
                match t_op {
                    Some(t) => *t,
                    None => Tnum::unknown()
                }
            }
        }
    }
    
    pub fn set_tnum(&mut self, r: Reg, t: Tnum) {
        if r != Reg::Zero {
            self.tnums.insert(r, t);
        }
    }
}