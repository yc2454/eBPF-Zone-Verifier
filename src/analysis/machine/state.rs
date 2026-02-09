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

/// A saved call frame (caller's state when entering a subfunction)
#[derive(Clone, Debug, Default)]
pub struct CallFrame {
    pub return_pc: usize,
    pub stack: StackState,
    pub frame_depth: u16,  // max bytes used in this frame
}

impl std::fmt::Display for CallFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CallFrame(return_pc={}, frame_depth={})", self.return_pc, self.frame_depth)
    }
}

/// Mirrors `struct bpf_verifier_state` (partially).
/// Holds the snapshot of execution at a specific PC.
#[derive(Clone, Debug)]
pub struct State {
    /// Register and Stack Types
    /// Mirrors `bpf_reg_state.type`
    pub types: TypeState,

    /// Numerical Domain (Values)
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
    pub call_stack: Vec<CallFrame>,

    /// Current frame's max stack depth (positive, e.g., 300 means accessed R10-300)
    pub frame_depth: u16,

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
            dbm,
            pc,
            history_idx: None,
            tnums: tnums.clone(),
            call_stack: vec![CallFrame::default()],
            frame_depth: 0,
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
        self.stack_mut().invalidate_ref(id);
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

    /// Spill into current frame (common case, e.g. store to R10+off)
    pub fn spill(&mut self, reg: Reg, offset: i16) {
        self.spill_at(self.current_frame_level(), reg, offset);
    }

    /// Spill into a specific frame (cross-frame, e.g. store via PtrToStack)
    pub fn spill_at(&mut self, frame_level: usize, reg: Reg, offset: i16) {
        let (min, max) = get_simple_bounds(&self.dbm, reg);
        println!("At spilling, {} bounds: [{}, {}]", reg.name(), min, max);
        self.call_stack[frame_level].stack.insert(
            offset,
            SpilledReg {
                reg_type: self.types.get(reg),
                tnum: self.tnums.get(&reg).cloned().unwrap_or(Tnum::unknown()),
                bounds: ScalarBounds { min, max },
            },
        );
    }

    /// Reload from current frame
    pub fn try_reload(&mut self, dst: Reg, offset: i16, size: MemSize) -> bool {
        self.try_reload_at(self.current_frame_level(), dst, offset, size)
    }

    /// Reload from a specific frame (cross-frame)
    pub fn try_reload_at(&mut self, frame_level: usize, dst: Reg, offset: i16, size: MemSize) -> bool {
        if size != MemSize::U64 {
            return false;
        }
        if let Some(spilled) = self.call_stack[frame_level].stack.get_slot(offset) {
            domain::forget(&mut self.dbm, dst);
            self.types.set(dst, spilled.reg_type);
            self.tnums.insert(dst, spilled.tnum);
            domain::set_bounds(&mut self.dbm, dst, spilled.bounds.min, spilled.bounds.max);
            true
        } else {
            false
        }
    }

    /// Called on every stack access to track depth
    pub fn update_frame_depth(&mut self, off: i16) {
        if off < 0 {
            let depth = (-off) as u16;
            self.frame_depth = self.frame_depth.max(depth);
        } else {
            // Positive offsets do not affect frame depth
        }
    }

    pub fn stack_frame_count(&self) -> usize {
        self.call_stack.len()
    }

    pub fn at_last_call_frame(&self) -> bool {
        self.stack_frame_count() == 1
    }

    // === Current frame (most common case, no frame level needed) ===
    
    pub fn stack(&self) -> &StackState {
        &self.call_stack.last().unwrap().stack
    }

    pub fn stack_mut(&mut self) -> &mut StackState {
        &mut self.call_stack.last_mut().unwrap().stack
    }

    pub fn frame_depth(&self) -> u16 {
        self.call_stack.last().unwrap().frame_depth
    }

    pub fn set_frame_depth(&mut self, depth: u16) {
        self.call_stack.last_mut().unwrap().frame_depth = depth;
    }

    // === Cross-frame access (rare, explicit frame level) ===

    pub fn stack_at(&self, frame_level: usize) -> &StackState {
        &self.call_stack[frame_level].stack
    }

    pub fn stack_at_mut(&mut self, frame_level: usize) -> &mut StackState {
        &mut self.call_stack[frame_level].stack
    }

    // === Frame management ===

    pub fn current_frame_level(&self) -> usize {
        self.call_stack.len() - 1
    }

    pub fn push_frame(&mut self, return_pc: usize) {
        self.call_stack.last_mut().unwrap().return_pc = return_pc;
        self.call_stack.push(CallFrame::default());
    }

    pub fn pop_frame(&mut self) -> Option<usize> {
        if self.call_stack.len() <= 1 { return None; }
        self.call_stack.pop();
        Some(self.call_stack.last().unwrap().return_pc)
    }

    pub fn total_stack_depth(&self) -> u16 {
        self.call_stack.iter().map(|f| f.frame_depth).sum()
    }

    pub fn num_frames(&self) -> usize {
        self.call_stack.len()
    }

    pub fn tnums_to_string(&self) -> String {
        let mut parts = Vec::new();
        for r in Reg::ALL {
            let tnum = self.get_tnum(r);
            if tnum.is_unknown() {
                continue;
            }
            parts.push(format!("{:?}: {}", r, tnum.to_string()));
        }
        parts.join(", ")
    }
     
}