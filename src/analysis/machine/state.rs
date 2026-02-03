// src/analysis/state.rs
use crate::zone::dbm::Dbm;
use crate::analysis::machine::reg_types::TypeState;
use crate::zone::tnum::Tnum;
use crate::zone::domain::{self, Reg, get_simple_bounds};
use crate::analysis::machine::stack_state::{StackState, SpilledReg, ScalarBounds};
use crate::ast::MemSize;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockState {
    pub ptr_id: u32,      // which pointer instance
    pub lock_offset: u32,   // offset of spin_lock within value (e.g., 4)
}

/// Mirrors `struct bpf_verifier_state` (partially).
/// Holds the snapshot of execution at a specific PC.
#[derive(Clone, Debug)]
pub struct State {
    /// 1. Register and Stack Types
    /// Mirrors `bpf_reg_state.type`
    pub types: TypeState,

    // Stack state for spilled registers
    pub stack: StackState,

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

    /// Active references that must be released before exit
    pub active_refs: HashSet<u32>,

    // Active lock that is being held
    pub active_lock: Option<LockState>,
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
            stack: StackState::new(),
            dbm,
            pc,
            history_idx: None,
            tnums: tnums.clone(),
            call_stack: Vec::new(),
            active_refs: HashSet::new(),
            active_lock: None,
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

    /// Acquire a new reference, returns the ref_id
    pub fn acquire_ref(&mut self) -> u32 {
        let id = crate::analysis::machine::reg_types::new_ref_id();
        self.active_refs.insert(id);
        id
    }

    /// Release a reference by id
    pub fn release_ref(&mut self, id: u32) -> bool {
        self.active_refs.remove(&id)
    }

    /// Check if all references have been released
    pub fn has_unreleased_refs(&self) -> bool {
        !self.active_refs.is_empty()
    }

    /// Invalidate all registers (and stack slots) holding a given ref_id
    pub fn invalidate_ref(&mut self, id: u32) {
        use crate::analysis::machine::reg_types::RegType;
        
        // Invalidate registers
        for i in 0..self.types.regs.len() {
            if self.types.regs[i].get_ref_id() == Some(id) {
                self.types.regs[i] = RegType::ScalarValue;
            }
        }
        
        // Invalidate stack slots
        self.stack.invalidate_ref(id);
    }

    /// Acquire a spin lock
    pub fn acquire_lock(&mut self, ptr_id: u32, lock_offset: u32) {
        self.active_lock = Some(LockState { ptr_id, lock_offset });
    }

    /// Release the spin lock
    pub fn release_lock(&mut self) {
        self.active_lock = None;
    }

    /// Check if currently holding a lock
    pub fn has_active_lock(&self) -> bool {
        self.active_lock.is_some()
    }

    /// Get the currently held lock, if any
    pub fn get_active_lock(&self) -> Option<&LockState> {
        self.active_lock.as_ref()
    }

    // Spill a register onto stack at given offset
    pub fn spill(&mut self, reg: Reg, offset: i16) {
        let (min, max) = get_simple_bounds(&self.dbm, reg);
        self.stack.insert(
            offset, 
            SpilledReg {
                reg_type: self.types.get(reg),
                tnum: self.tnums.get(&reg).cloned().unwrap_or(Tnum::unknown()),
                bounds: ScalarBounds { min, max }
            }
        );
    }
    
    /// Attempts to reload a spilled register from the stack.
    /// Returns true if successful (state was updated from the spill snapshot).
    pub fn try_reload(
        &mut self,
        dst: Reg,
        base: Reg,
        off: i16,
        size: MemSize,
    ) -> bool {
        // Only 64-bit loads from stack pointer can restore spilled state
        if base != Reg::R10 || size != MemSize::U64 {
            return false;
        }

        if let Some(spilled) = self.stack.get_slot(off) {
            // Restore the full abstract state from the snapshot
            self.types.set(dst, spilled.reg_type);
            self.tnums.insert(dst, spilled.tnum.clone());
            domain::set_bounds(&mut self.dbm, dst, spilled.bounds.min, spilled.bounds.max);
            true
        } else {
            false
        }
    }
     
}