// src/analysis/machine/frame_stack.rs

use crate::analysis::machine::reg_types::{TypeState, RegType};
use crate::analysis::machine::stack_state::StackState;
use crate::zone::dbm::Dbm;
use crate::zone::tnum::Tnum;
use crate::analysis::machine::reg::Reg;
use std::collections::HashMap;

/// A type-safe handle to a specific frame in the call stack.
/// Can only be created by FrameStack, preventing out-of-bounds access.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrameLevel(usize);

impl FrameLevel {
    /// The main function frame (always valid).
    pub const MAIN: FrameLevel = FrameLevel(0);
}

impl std::fmt::Display for FrameLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "frame[{}]", self.0)
    }
}

/// A saved call frame (caller's state when entering a subfunction).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CallFrame {
    pub return_pc: usize,
    pub stack: StackState,
    pub frame_depth: u16,

    // Caller's register state, captured at CallRel time.
    // Used to restore state on return and to compare caller
    // contexts during cross-frame pruning.
    pub caller_types: TypeState,
    pub caller_dbm: Dbm,
    pub caller_tnums: HashMap<Reg, Tnum>,
}

impl std::fmt::Display for CallFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CallFrame(return_pc={}, frame_depth={})", self.return_pc, self.frame_depth)
    }
}

/// A call stack that always has at least one frame (main).
///
/// The last element is always the "current" frame. Caller frames
/// sit below it. The main frame at index 0 can never be popped.
///
/// ```text
///   frames[0]       = main frame (always present)
///   frames[1]       = first callee frame (if in a subfunction)
///   ...
///   frames.last()   = current frame
/// ```
#[derive(Clone, Debug)]
pub struct FrameStack {
    // Invariant: never empty. frames[0] is always main.
    frames: Vec<CallFrame>,
}

impl FrameStack {
    /// Create a new frame stack with the main frame.
    pub fn new() -> Self {
        FrameStack {
            frames: vec![CallFrame::default()],
        }
    }

    // ── Current frame (most common operations) ──────────────────

    /// The level of the currently executing frame.
    pub fn current_level(&self) -> FrameLevel {
        FrameLevel(self.frames.len() - 1)
    }

    /// Immutable access to the current frame.
    pub fn current(&self) -> &CallFrame {
        // SAFETY: invariant guarantees non-empty
        self.frames.last().unwrap()
    }

    /// Mutable access to the current frame.
    pub fn current_mut(&mut self) -> &mut CallFrame {
        self.frames.last_mut().unwrap()
    }

    // ── Indexed access (for cross-frame spill/reload) ───────────

    /// Access a frame by level. Panics if level is invalid (bug in caller).
    pub fn get(&self, level: FrameLevel) -> &CallFrame {
        &self.frames[level.0]
    }

    /// Mutable access to a frame by level.
    pub fn get_mut(&mut self, level: FrameLevel) -> &mut CallFrame {
        &mut self.frames[level.0]
    }

    // ── Push / Pop ──────────────────────────────────────────────

    /// Enter a subfunction. Saves caller state into a new frame and pushes it.
    /// Returns the FrameLevel of the new (callee) frame.
    pub fn push(
        &mut self,
        return_pc: usize,
        caller_types: TypeState,
        caller_dbm: Dbm,
        caller_tnums: HashMap<Reg, Tnum>,
    ) -> FrameLevel {
        let frame = CallFrame {
            return_pc,
            stack: StackState::default(),
            frame_depth: 0,
            caller_types,
            caller_dbm,
            caller_tnums,
        };
        self.frames.push(frame);
        self.current_level()
    }

    /// Return from a subfunction. Pops the current frame and returns
    /// it (owned) so the caller can restore register state.
    /// Returns None if already at main (nothing to pop).
    pub fn pop(&mut self) -> Option<CallFrame> {
        if self.frames.len() <= 1 {
            None
        } else {
            self.frames.pop()
        }
    }

    /// Whether we're in the main function (no active calls).
    pub fn at_main(&self) -> bool {
        self.frames.len() == 1
    }

    // ── Iteration (for pruning, subsumption checks) ─────────────

    /// Number of frames (always >= 1).
    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    /// Iterate over all frames (main first, current last).
    pub fn iter(&self) -> impl Iterator<Item = &CallFrame> {
        self.frames.iter()
    }

    /// Total stack depth across all frames.
    pub fn total_stack_depth(&self) -> u16 {
        self.frames.iter().map(|f| f.frame_depth).sum()
    }

    /// Mutable iteration over all frames.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut CallFrame> {
        self.frames.iter_mut()
    }

    /// Invalidate all registers of a given type across all caller frames.
    /// Used when helpers like bpf_redirect invalidate packet pointers globally.
    pub fn invalidate_caller_reg_type(
        &mut self,
        should_invalidate: impl Fn(&RegType) -> bool,
        replacement: RegType,
    ) {
        for frame in self.frames.iter_mut() {
            for r in Reg::ALL {
                if should_invalidate(&frame.caller_types.get(r)) {
                    frame.caller_types.set(r, replacement.clone());
                }
            }
        }
    }
}

impl Default for FrameStack {
    fn default() -> Self {
        Self::new()
    }
}
