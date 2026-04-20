// src/analysis/machine/frame_stack.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::stack_state::StackState;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;
use std::collections::HashMap;

/// A type-safe handle to a specific frame in the call stack.
/// Can only be created by FrameStack, preventing out-of-bounds access.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FrameLevel(usize);

impl FrameLevel {
    /// The main function frame (always valid).
    pub const MAIN: FrameLevel = FrameLevel(0);

    /// Create a FrameLevel from an index.
    /// Use with caution - only valid if index < num_frames.
    pub fn from_index(idx: usize) -> Self {
        FrameLevel(idx)
    }
}

impl std::fmt::Display for FrameLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "frame[{}]", self.0)
    }
}

/// A saved call frame (caller's state when entering a subfunction).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallFrame {
    pub return_pc: usize,
    pub stack: StackState,
    pub frame_depth: u16,

    // Caller's register state, captured at CallRel time.
    // Used to restore state on return and to compare caller
    // contexts during cross-frame pruning.
    pub caller_types: TypeState,
    pub caller_domain: NumericDomain,
    pub caller_tnums: HashMap<Reg, Tnum>,

    /// Innermost exception callback entry PC set on this frame (W3.3a).
    /// `bpf_throw` unwinds to the nearest enclosing frame with a handler;
    /// if none is set on any frame, the state's program-default handler
    /// is used (see [`State::program_exception_cb`]). Plumbing only in
    /// W3.3a — transfer semantics land in W3.3b. Read through
    /// [`CallFrame::exception_cb`] rather than touching the field.
    exception_cb: Option<usize>,
}

impl Default for CallFrame {
    fn default() -> Self {
        CallFrame {
            return_pc: 0,
            stack: StackState::default(),
            frame_depth: 0,
            caller_types: TypeState::default(),
            caller_domain: NumericDomain::default(),
            caller_tnums: HashMap::new(),
            exception_cb: None,
        }
    }
}

impl CallFrame {
    /// Exception callback registered on this frame, if any.
    pub fn exception_cb(&self) -> Option<usize> {
        self.exception_cb
    }

    /// Register an exception callback entry PC on this frame. Overwrites
    /// any prior handler (matches kernel semantics: the most recent
    /// `bpf_set_exception_callback` wins).
    pub fn set_exception_cb(&mut self, pc: usize) {
        self.exception_cb = Some(pc);
    }

    /// Drop any exception callback on this frame.
    #[allow(dead_code)]
    pub fn clear_exception_cb(&mut self) {
        self.exception_cb = None;
    }
}

impl std::fmt::Display for CallFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CallFrame(return_pc={}, frame_depth={})",
            self.return_pc, self.frame_depth
        )
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
        caller_domain: NumericDomain,
        caller_tnums: HashMap<Reg, Tnum>,
    ) -> FrameLevel {
        let frame = CallFrame {
            return_pc,
            stack: StackState::default(),
            frame_depth: 0,
            caller_types,
            caller_domain,
            caller_tnums,
            exception_cb: None,
        };
        self.frames.push(frame);
        self.current_level()
    }

    /// Return from a subfunction. Pops the current frame and returns
    /// it (owned) so the caller can restore register state.
    /// NOTE: We do NOT restore the caller frames' stacks. If the callee
    /// modified the caller's stack (via a passed pointer), those modifications
    /// persist. This matches kernel verifier behavior where stack state is
    /// not saved/restored on call/return.
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
                    frame.caller_types.set(r, replacement);
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
