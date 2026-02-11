// src/analysis/state.rs
use crate::zone::dbm::Dbm;
use crate::analysis::machine::reg_types::{TypeState, RegType};
use crate::zone::tnum::Tnum;
use crate::zone::domain::{self, Reg, get_simple_bounds};
use crate::analysis::machine::stack_state::{StackState, SpilledReg, ScalarBounds};
use crate::analysis::machine::frame_stack::{FrameStack, FrameLevel, CallFrame};
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
    /// Always has at least one frame (main). The current frame is
    /// always the last element; caller frames sit below it.
    pub frames: FrameStack,

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
            frames: FrameStack::new(),
            frame_depth: 0,
            active_refs: HashSet::new(),
            active_lock: None,
        }
    }

    // ── Tnum helpers ────────────────────────────────────────────

    pub fn get_tnum(&self, r: Reg) -> Tnum {
        match r {
            Reg::Zero => Tnum::constant(0),
            _ => self.tnums.get(&r).copied().unwrap_or(Tnum::unknown()),
        }
    }
    
    pub fn set_tnum(&mut self, r: Reg, t: Tnum) {
        if r != Reg::Zero {
            self.tnums.insert(r, t);
        }
    }

    // ── Reference tracking ──────────────────────────────────────

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
        // Invalidate registers
        for i in 0..self.types.regs.len() {
            if self.types.regs[i].get_ref_id() == Some(id) {
                self.types.regs[i] = RegType::ScalarValue;
            }
        }
        // Invalidate stack slots
        self.stack_mut().invalidate_ref(id);
    }

    // ── Lock tracking ───────────────────────────────────────────

    pub fn acquire_lock(&mut self, ptr_id: u32, lock_offset: u32) {
        self.active_lock = Some(LockState { ptr_id, lock_offset });
    }

    pub fn release_lock(&mut self) {
        self.active_lock = None;
    }

    pub fn has_active_lock(&self) -> bool {
        self.active_lock.is_some()
    }

    pub fn get_active_lock(&self) -> Option<&LockState> {
        self.active_lock.as_ref()
    }

    // ── Stack spill/reload (current frame) ──────────────────────

    /// Spill into current frame (common case, e.g. store to R10+off)
    pub fn spill(&mut self, reg: Reg, offset: i16) {
        let level = self.frames.current_level();
        self.spill_at(level, reg, offset);
    }

    /// Spill into a specific frame (cross-frame, e.g. store via PtrToStack)
    pub fn spill_at(&mut self, level: FrameLevel, reg: Reg, offset: i16) {
        let (min, max) = get_simple_bounds(&self.dbm, reg);
        println!("At spilling, {} bounds: [{}, {}]", reg.name(), min, max);
        let spilled = SpilledReg {
            source_reg: Some(reg),
            reg_type: self.types.get(reg),
            tnum: self.tnums.get(&reg).cloned().unwrap_or(Tnum::unknown()),
            bounds: ScalarBounds { min, max },
        };
        let stack = &mut self.frames.get_mut(level).stack;
        for i in 0..8 {
            let current_byte = offset + i;
            if i == 0 {
                stack.insert(current_byte, spilled.clone());
            } else {
                stack.insert(current_byte, SpilledReg {
                    source_reg: None,
                    reg_type: RegType::ScalarValue,
                    tnum: Tnum::unknown(),
                    bounds: ScalarBounds { min: i64::MIN, max: i64::MAX },
                });
            }
        }
    }

    pub fn store_imm_to_stack(&mut self, imm: i64, offset: i16) {
        let level = self.frames.current_level();
        self.store_imm_to_stack_at(level, imm, offset);
    }

    pub fn store_imm_to_stack_at(&mut self, level: FrameLevel, imm: i64, offset: i16) {
        let slot_content = SpilledReg {
            source_reg: None,
            reg_type: RegType::ScalarValue,
            tnum: Tnum::constant(imm as u64),
            bounds: ScalarBounds { min: imm, max: imm },
        };
        let stack = &mut self.frames.get_mut(level).stack;
        for i in 0..8 {
            let current_byte = offset + i;
            if i == 0 {
                stack.insert(current_byte, slot_content.clone());
            } else {
                stack.insert(current_byte, SpilledReg {
                    source_reg: None,
                    reg_type: RegType::ScalarValue,
                    tnum: Tnum::unknown(),
                    bounds: ScalarBounds { min: i64::MIN, max: i64::MAX },
                });
            }
        }
    }

    /// Reload from current frame
    pub fn try_reload(&mut self, dst: Reg, offset: i16, size: MemSize) -> bool {
        let level = self.frames.current_level();
        self.try_reload_at(level, dst, offset, size)
    }

    /// Reload from a specific frame (cross-frame)
    pub fn try_reload_at(&mut self, level: FrameLevel, dst: Reg, offset: i16, size: MemSize) -> bool {
        if size != MemSize::U64 {
            return false;
        }
        if let Some(spilled) = self.frames.get(level).stack.get_slot(offset) {
            domain::forget(&mut self.dbm, dst);
            self.types.set(dst, spilled.reg_type);
            self.tnums.insert(dst, spilled.tnum);
            domain::set_bounds(&mut self.dbm, dst, spilled.bounds.min, spilled.bounds.max);
            true
        } else {
            false
        }
    }

    // ── Frame depth tracking ────────────────────────────────────

    /// Called on every stack access to track depth
    pub fn update_frame_depth(&mut self, off: i16) {
        if off < 0 && off > i16::MIN {
            let depth = (-off) as u16;
            self.frame_depth = self.frame_depth.max(depth);
        }
    }

    // ── Current frame convenience accessors ─────────────────────

    pub fn stack(&self) -> &StackState {
        &self.frames.current().stack
    }

    pub fn stack_mut(&mut self) -> &mut StackState {
        &mut self.frames.current_mut().stack
    }

    pub fn frame_depth(&self) -> u16 {
        self.frames.current().frame_depth
    }

    pub fn set_frame_depth(&mut self, depth: u16) {
        self.frames.current_mut().frame_depth = depth;
    }

    // ── Cross-frame access (for PtrToStack with different frame_level) ──

    pub fn stack_at(&self, level: FrameLevel) -> &StackState {
        &self.frames.get(level).stack
    }

    pub fn stack_at_mut(&mut self, level: FrameLevel) -> &mut StackState {
        &mut self.frames.get_mut(level).stack
    }

    // ── Frame management (delegated to FrameStack) ──────────────

    pub fn current_frame_level(&self) -> FrameLevel {
        self.frames.current_level()
    }

    pub fn push_frame(&mut self, return_pc: usize) {
        self.frames.push(
            return_pc,
            self.types.clone(),
            self.dbm.clone(),
            self.tnums.clone(),
        );
    }

    /// Pop the current frame, returning it owned. Returns None at main.
    pub fn pop_frame(&mut self) -> Option<CallFrame> {
        self.frames.pop()
    }

    pub fn at_main_frame(&self) -> bool {
        self.frames.at_main()
    }

    pub fn num_frames(&self) -> usize {
        self.frames.depth()
    }

    pub fn total_stack_depth(&self) -> u16 {
        self.frames.total_stack_depth()
    }

    // ── Display helpers ─────────────────────────────────────────

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
