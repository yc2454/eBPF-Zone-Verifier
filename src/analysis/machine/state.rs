// src/analysis/state.rs
use crate::analysis::machine::frame_stack::{CallFrame, FrameLevel, FrameStack};
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::stack_state::{ScalarBounds, SpilledReg, StackState};
use crate::ast::MemSize;
use crate::common::config::DomainMode;
use crate::domains::dbm::INF;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;
use log::trace;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockState {
    pub ptr_id: u32,      // which pointer instance
    pub lock_offset: u32, // offset of spin_lock within value (e.g., 4)
}

/// Per-program `may_goto` iteration budget. Mirrors the kernel's
/// `BPF_MAY_GOTO_LIMIT` (see `kernel/bpf/verifier.c`). Each time the
/// verifier takes a `may_goto` back-edge it decrements this counter; the
/// back-edge becomes infeasible once the counter hits zero, which is what
/// lets the analysis terminate on unbounded-looking loops. Plumbing only in
/// W3.1a — transfer semantics land in W3.1b, subsumption in W3.1c.
pub const BPF_MAY_GOTO_LIMIT: u32 = 8_388_608;

/// Mirrors `struct bpf_verifier_state` (partially).
/// Holds the snapshot of execution at a specific PC.
#[derive(Clone, Debug)]
pub struct State {
    /// Register and Stack Types
    /// Mirrors `bpf_reg_state.type`
    pub types: TypeState,

    /// Numerical Domain (Values)
    /// Mirrors `bpf_reg_state.{smin_value, umax_value, var_off}`
    /// Can be either Zone (DBM) or Interval domain based on config
    pub domain: NumericDomain,

    /// Current Program Counter
    pub pc: usize,

    /// History Index (for history tracking, optional)
    pub history_idx: Option<usize>,

    pub tnums: HashMap<Reg, Tnum>, // tnum info for R0-R10

    /// Identity tokens for scalar values. Two registers (or a register and
    /// a stack slot via `SpilledReg::scalar_id`) that share an id are the
    /// same underlying unknown scalar; refining one propagates to the
    /// others. See `new_scalar_id` / `alloc_scalar_id` / `link_scalar_id`.
    /// Sparse: absent entry = unlinked. Phase-2 W2.1b wires assignment;
    /// W2.1c consumes it in branch refinement.
    pub scalar_ids: HashMap<Reg, u32>,

    /// Registers whose exact scalar bounds are "precision-critical" — i.e. a
    /// safety check downstream depends on the tight value rather than a
    /// coarser widened bound. Populated by
    /// [`State::mark_reg_precise`] at branch comparisons and at
    /// variable-offset memory accesses. Propagated forward through ALU
    /// (W2.2) and persisted across spills via [`SpilledReg::precise`].
    /// Consumed in W2.3 to block state pruning from over-generalising
    /// across precision-marked registers.
    pub precise_regs: HashSet<Reg>,

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

    /// RCU read-side critical section nesting depth (W5.2). Incremented
    /// by `bpf_rcu_read_lock`, decremented by `bpf_rcu_read_unlock`.
    /// Helpers/kfuncs marked with `CallFlags::RCU` require depth > 0.
    /// Program exit rejects if depth > 0 (`UnreleasedRcuRead`).
    pub rcu_read_depth: u32,

    /// Remaining `may_goto` iterations on this path. Initialised to
    /// [`BPF_MAY_GOTO_LIMIT`] at entry. Decremented by the `may_goto`
    /// transfer function on the taken branch (W3.1b); once zero the
    /// taken edge is infeasible. Subsumption will require the pruned
    /// state's budget to be ≥ the candidate's (W3.1c).
    pub goto_budget: u32,

    /// Program-default exception callback entry PC (W3.3a plumbing).
    /// Used when `bpf_throw` unwinds past every frame without finding a
    /// frame-local `exception_cb` (see [`CallFrame::exception_cb`]). A
    /// modern BPF program registers this via `bpf_set_exception_callback`
    /// at a well-known point; unset means an unhandled throw exits the
    /// program with the throw value in R0. Read through
    /// [`State::effective_exception_cb`] rather than touching the field.
    program_exception_cb: Option<usize>,
}

impl State {
    /// Create a new State with the specified domain and program counter
    pub fn new(domain: NumericDomain, pc: usize) -> Self {
        let mut tnums = HashMap::new();
        tnums.insert(Reg::Zero, Tnum::constant(0));
        for r in Reg::ALL {
            if r != Reg::Zero {
                tnums.insert(r, Tnum::unknown());
            }
        }
        State {
            types: TypeState::new_not_init(),
            domain,
            pc,
            history_idx: None,
            tnums: tnums.clone(),
            scalar_ids: HashMap::new(),
            precise_regs: HashSet::new(),
            frames: FrameStack::new(),
            frame_depth: 0,
            active_refs: HashSet::new(),
            active_lock: None,
            rcu_read_depth: 0,
            goto_budget: BPF_MAY_GOTO_LIMIT,
            program_exception_cb: None,
        }
    }

    // ── Exception handler (W3.3a plumbing) ──────────────────────
    //
    // Handler resolution mirrors the kernel: `bpf_throw` walks the frame
    // stack from innermost outward looking for a frame-local
    // `exception_cb`; if none is set, fall back to the program-default
    // slot. Call sites go through these helpers rather than touching
    // `program_exception_cb` / `CallFrame::exception_cb` directly.
    // Semantics (throw/unwind, callback frame push) land in W3.3b.

    /// Program-default exception callback, if registered.
    #[allow(dead_code)]
    pub fn program_exception_cb(&self) -> Option<usize> {
        self.program_exception_cb
    }

    /// Register the program-default exception callback. Overwrites any
    /// prior default (kernel: last registration wins).
    #[allow(dead_code)]
    pub fn set_program_exception_cb(&mut self, pc: usize) {
        self.program_exception_cb = Some(pc);
    }

    /// Resolve the handler that a `bpf_throw` from the current frame
    /// would unwind to: innermost frame-local `exception_cb`, else the
    /// program-default, else `None` (unhandled → program exit).
    #[allow(dead_code)]
    pub fn effective_exception_cb(&self) -> Option<usize> {
        let depth = self.frames.depth();
        for i in (0..depth).rev() {
            if let Some(pc) = self.frames.get(FrameLevel::from_index(i)).exception_cb() {
                return Some(pc);
            }
        }
        self.program_exception_cb
    }

    /// Install an exception callback on the current frame.
    #[allow(dead_code)]
    pub fn set_current_frame_exception_cb(&mut self, pc: usize) {
        self.frames.current_mut().set_exception_cb(pc);
    }

    // ── may_goto budget (W3.1a plumbing) ───────────────────────
    //
    // Helpers mirror the spin_lock / ref_id conventions: call sites go
    // through these methods rather than touching `goto_budget` directly.
    // Semantics (decrement on taken edge, reject on empty must-take) land
    // in W3.1b.

    pub fn goto_budget(&self) -> u32 {
        self.goto_budget
    }

    /// Returns `false` if the budget is already exhausted (caller should
    /// treat the taken edge as infeasible); otherwise decrements and
    /// returns `true`.
    pub fn consume_goto_budget(&mut self) -> bool {
        if self.goto_budget == 0 {
            return false;
        }
        self.goto_budget -= 1;
        true
    }

    /// Create a new State with Zone domain (for backwards compatibility)
    #[allow(dead_code)]
    pub fn new_zone(pc: usize) -> Self {
        Self::new(NumericDomain::new_zone(), pc)
    }

    /// Create a new State with Interval domain
    #[allow(dead_code)]
    pub fn new_interval(pc: usize) -> Self {
        Self::new(NumericDomain::new_interval(), pc)
    }

    /// Create a new State based on domain mode config
    #[allow(dead_code)]
    pub fn new_with_mode(mode: DomainMode, pc: usize) -> Self {
        let domain = match mode {
            DomainMode::Zone => NumericDomain::new_zone(),
            DomainMode::Interval => NumericDomain::new_interval(),
        };
        Self::new(domain, pc)
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

    // ── Scalar id helpers ──────────────────────────────────────
    //
    // Identity tokens for unknown scalars. Call sites use these helpers
    // instead of touching `scalar_ids` / `SpilledReg::scalar_id` directly
    // (encapsulation). Semantics are wired in W2.1b/c; today these are
    // plumbing only and the maps stay empty during verification.

    /// Current scalar id of register `r`, or None if unlinked / not a scalar.
    pub fn scalar_id(&self, r: Reg) -> Option<u32> {
        if r == Reg::Zero {
            return None;
        }
        self.scalar_ids.get(&r).copied()
    }

    /// Allocate a fresh scalar id for `r` and return it. Any previous id on
    /// `r` is replaced (the old value is now unrelated to the new one).
    pub fn alloc_scalar_id(&mut self, r: Reg) -> u32 {
        let id = crate::analysis::machine::reg_types::new_scalar_id();
        self.scalar_ids.insert(r, id);
        id
    }

    /// Make `dst` share `src`'s scalar id (copy edge). If `src` has no id,
    /// one is allocated first so both registers end up linked.
    pub fn link_scalar_id(&mut self, dst: Reg, src: Reg) {
        if dst == Reg::Zero || src == Reg::Zero {
            return;
        }
        let id = match self.scalar_ids.get(&src).copied() {
            Some(id) => id,
            None => {
                let id = crate::analysis::machine::reg_types::new_scalar_id();
                self.scalar_ids.insert(src, id);
                id
            }
        };
        self.scalar_ids.insert(dst, id);
    }

    /// Drop any scalar id on `r` (e.g. constant assignment or value-mutating ALU).
    pub fn clear_scalar_id(&mut self, r: Reg) {
        self.scalar_ids.remove(&r);
    }

    // ── Precision marking (W2.2) ───────────────────────────────
    //
    // `mark_reg_precise` is the entry point for callers that recognise a
    // register's exact bounds matter for safety (e.g. a branch comparison
    // that will refine bounds, or a variable offset feeding a memory
    // access). Marks propagate along scalar-id equivalence classes and
    // forward through arithmetic; the field is consumed in W2.3 to block
    // pruning that would generalise the marked register.

    /// Mark `r` as precision-critical. Also marks any other register
    /// currently sharing `r`'s scalar id, so spills and copies keep the
    /// mark. Safe to call on registers of any type; no-op for `Zero`.
    pub fn mark_reg_precise(&mut self, r: Reg) {
        if r == Reg::Zero {
            return;
        }
        self.precise_regs.insert(r);
        if let Some(id) = self.scalar_ids.get(&r).copied() {
            let linked: Vec<Reg> = self
                .scalar_ids
                .iter()
                .filter_map(|(&other, &oid)| if oid == id { Some(other) } else { None })
                .collect();
            for other in linked {
                self.precise_regs.insert(other);
            }
        }
    }

    /// Whether `r` has been marked precise on the current path.
    pub fn is_reg_precise(&self, r: Reg) -> bool {
        r != Reg::Zero && self.precise_regs.contains(&r)
    }

    /// Drop any precision mark on `r` (e.g. overwritten by an immediate
    /// or a load that introduces a fresh unknown scalar).
    pub fn clear_reg_precise(&mut self, r: Reg) {
        self.precise_regs.remove(&r);
    }

    /// All registers currently carrying `id`. Useful for refinement fan-out.
    pub fn regs_with_scalar_id(&self, id: u32) -> Vec<Reg> {
        self.scalar_ids
            .iter()
            .filter_map(|(&r, &rid)| if rid == id { Some(r) } else { None })
            .collect()
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
        self.active_lock = Some(LockState {
            ptr_id,
            lock_offset,
        });
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

    // ── RCU read-side tracking (W5.2) ───────────────────────────

    pub fn rcu_read_lock(&mut self) {
        self.rcu_read_depth = self.rcu_read_depth.saturating_add(1);
    }

    /// Decrement RCU read-side nesting depth. Returns `false` if no
    /// section is active (caller must reject).
    pub fn rcu_read_unlock(&mut self) -> bool {
        if self.rcu_read_depth == 0 {
            return false;
        }
        self.rcu_read_depth -= 1;
        true
    }

    pub fn in_rcu_read_section(&self) -> bool {
        self.rcu_read_depth > 0
    }

    // ── Stack spill/reload (current frame) ──────────────────────

    /// Spill into a specific frame (cross-frame, e.g. store via PtrToStack)
    pub fn spill_at(&mut self, level: FrameLevel, reg: Reg, offset: i16, size: MemSize) {
        let is_aligned = (offset % 8) == 0;
        let reg_type = self.types.get(reg);

        // Only U64 stores at aligned offsets can preserve pointer types
        let preserved_type = if size == MemSize::U64 && is_aligned {
            reg_type
        } else {
            RegType::ScalarValue
        };

        // Save pointer bounds if applicable
        let ptr_bounds = if size == MemSize::U64 && is_aligned {
            use crate::analysis::machine::stack_state::PointerBounds;
            let (i_off, i_var, i_range) = self.save_interval_ptr_offset(reg);
            if i_off.is_some() || i_var.is_some() || i_range.is_some() {
                Some(PointerBounds::Interval {
                    off: i_off,
                    var_off: i_var,
                    range: i_range,
                })
            } else {
                let (a, lo, hi) = self.save_anchor_info(reg);
                if a.is_some() || lo.is_some() || hi.is_some() {
                    Some(PointerBounds::Zone {
                        anchor: a,
                        anchor_lo: lo,
                        anchor_hi: hi,
                    })
                } else {
                    None
                }
            }
        } else {
            None
        };

        let (min, max) = self.domain.get_interval(reg);
        trace!("At spilling, {} bounds: [{}, {}]", reg.name(), min, max);

        // Only track as proper spill if 8-byte aligned
        let source_reg = if is_aligned { Some(reg) } else { None };

        // Allocate (or reuse) a scalar id for any aligned scalar spill so
        // the slot — and any same-width fill — joins the source's scalar
        // equivalence class. Mirrors kernel's `assign_scalar_id_before_mov`
        // at spill time. Without this, post-spill branch refinements on
        // the source can't fan out to slot/fill, which leaves dead
        // branches reachable in the verifier_spill_fill::*_ok tests.
        let slot_scalar_id = if is_aligned
            && size.bytes() <= 8
            && matches!(preserved_type, RegType::ScalarValue)
        {
            let id = match self.scalar_ids.get(&reg).copied() {
                Some(id) => id,
                None => {
                    let new_id = crate::analysis::machine::reg_types::new_scalar_id();
                    self.scalar_ids.insert(reg, new_id);
                    new_id
                }
            };
            Some(id)
        } else if size == MemSize::U64 && is_aligned {
            self.scalar_ids.get(&reg).copied()
        } else {
            None
        };

        let spilled = SpilledReg {
            source_reg,
            reg_type: preserved_type,
            tnum: self.tnums.get(&reg).cloned().unwrap_or(Tnum::unknown()),
            bounds: ScalarBounds { min, max },
            size,
            ptr_bounds,
            scalar_id: slot_scalar_id,
            precise: is_aligned && size == MemSize::U64 && self.precise_regs.contains(&reg),
            iterator: None,
            dynptr: None,
        };

        let stack = &mut self.frames.get_mut(level).stack;
        for i in 0..size.bytes() {
            let current_byte = offset + i as i16;
            if i == 0 {
                stack.insert(current_byte, spilled.clone());
            } else {
                stack.insert(
                    current_byte,
                    SpilledReg {
                        source_reg: None,
                        reg_type: RegType::ScalarValue,
                        tnum: Tnum::unknown(),
                        bounds: ScalarBounds {
                            min: i64::MIN,
                            max: i64::MAX,
                        },
                        size,
                        ptr_bounds: None,
                        scalar_id: None,
                        precise: false,
                        iterator: None,
                        dynptr: None,
                    },
                );
            }
        }
    }

    pub fn store_imm_to_stack_at(
        &mut self,
        level: FrameLevel,
        imm: i64,
        offset: i16,
        size: MemSize,
    ) {
        let is_aligned = (offset % 8) == 0;

        // Mask the immediate value to the store size
        let masked_imm = match size {
            MemSize::U8 => (imm as u8) as i64,
            MemSize::U16 => (imm as u16) as i64,
            MemSize::U32 => (imm as u32) as i64,
            MemSize::U64 => imm,
        };

        // For immediate stores, always track exact bounds since we know the value.
        // The alignment check only affects whether we can reliably fill/restore,
        // but we should still track the bounds for validation purposes.
        let (tnum, bounds, _source_reg) = (
            Tnum::constant(masked_imm as u64),
            ScalarBounds {
                min: masked_imm,
                max: masked_imm,
            },
            if is_aligned { Some(Reg::R0) } else { None },
        );

        let slot_content = SpilledReg {
            source_reg: if is_aligned { Some(Reg::R0) } else { None }, // Use dummy reg to indicate "trackable"
            reg_type: RegType::ScalarValue,
            tnum,
            bounds,
            size,
            ptr_bounds: None,
            scalar_id: None,
            precise: false,
            iterator: None,
            dynptr: None,
        };

        let stack = &mut self.frames.get_mut(level).stack;
        for i in 0..size.bytes() {
            let current_byte = offset + i as i16;
            if i == 0 {
                stack.insert(current_byte, slot_content.clone());
            } else {
                stack.insert(
                    current_byte,
                    SpilledReg {
                        source_reg: None,
                        reg_type: RegType::ScalarValue,
                        tnum: Tnum::unknown(),
                        bounds: ScalarBounds {
                            min: i64::MIN,
                            max: i64::MAX,
                        },
                        size,
                        ptr_bounds: None,
                        scalar_id: None,
                        precise: false,
                        iterator: None,
                        dynptr: None,
                    },
                );
            }
        }
    }

    /// Reload from current frame
    pub fn fill(&mut self, dst: Reg, offset: i16, size: MemSize) -> bool {
        let level = self.frames.current_level();
        self.fill_at(level, dst, offset, size)
    }

    /// Reload from a specific frame (cross-frame)
    pub fn fill_at(&mut self, level: FrameLevel, dst: Reg, offset: i16, size: MemSize) -> bool {
        let stack = &self.frames.get(level).stack;

        // Check all bytes we're reading are initialized
        for i in 0..size.bytes() {
            let current_byte = offset + i as i16;
            if stack.get_slot(current_byte).is_none() {
                return false; // Reading uninitialized memory
            }
        }

        // Get the slot at base offset
        let spilled = match stack.get_slot(offset).cloned() {
            Some(s) => s,
            None => return false,
        };

        self.domain.forget(dst);

        // Check if we can preserve type/bounds:
        // 1. Must be reading from start of a spilled value (source_reg.is_some())
        // 2. Load size must match store size
        // 3. Offset must be 8-byte aligned
        let is_aligned = (offset % 8) == 0;
        let sizes_match = spilled.source_reg.is_some() && spilled.size == size;

        // Try to extract a precise (sub-)value when reading a narrower
        // (or unaligned) slice of a wider spill whose enclosing tnum
        // pins enough bits. Walk back up to 7 bytes to find the slot
        // holding the actual spilled value. Placeholder bytes have
        // tnum=unknown (mask=u64::MAX) and large size, so the
        // alignment+const gates below let real spills win the search.
        let narrowed_tnum: Option<Tnum> = if !sizes_match && size.bytes() <= 8 {
            let mut found: Option<Tnum> = None;
            for back in 0..8i16 {
                let base = offset - back;
                if let Some(s) = stack.get_slot(base) {
                    // Aligned-base aligned-width spills are the only
                    // ones we trust beyond the simple zero (STACK_ZERO)
                    // case — kernel marks unaligned register spills
                    // STACK_MISC. We treat constant-zero stores as
                    // safe at any alignment to model STACK_ZERO.
                    let base_aligned = base % 8 == 0;
                    let covers = (back as usize) + size.bytes() <= s.size.bytes();
                    if !covers {
                        continue;
                    }
                    let trustable = base_aligned || (s.tnum.is_const() && s.tnum.value == 0);
                    if !trustable {
                        continue;
                    }
                    let shift = (back as u64) * 8;
                    let v = s.tnum.value >> shift;
                    let m = s.tnum.mask >> shift;
                    let mask: u64 = match size {
                        MemSize::U8 => 0xff,
                        MemSize::U16 => 0xffff,
                        MemSize::U32 => 0xffff_ffff,
                        MemSize::U64 => u64::MAX,
                    };
                    let nm = m & mask;
                    // Nothing pinned within the fill width → no info beyond
                    // the existing unbounded fallback. Skip to avoid spurious
                    // bounds (e.g. signed-overflow at U64) and pointless work.
                    if nm == mask {
                        break;
                    }
                    found = Some(Tnum {
                        value: v & mask,
                        mask: nm,
                    });
                    break;
                }
            }
            found
        } else {
            None
        };

        // Special case: u32 LE-low fill of an aligned u64 scalar spill
        // whose high 32 bits are known zero. The low half carries the
        // full spilled value, so preserve tnum, bounds AND scalar_id —
        // matching kernel's u32-fill-after-u64-spill-preserve-id rule.
        // (Counterpart `_clear_id` test fails the high-bits-zero check.)
        if !sizes_match
            && size == MemSize::U32
            && spilled.size == MemSize::U64
            && is_aligned
            && spilled.source_reg.is_some()
            && matches!(spilled.reg_type, RegType::ScalarValue)
            && (spilled.tnum.mask & 0xFFFFFFFF_00000000) == 0
            && (spilled.tnum.value >> 32) == 0
        {
            self.types.set(dst, RegType::ScalarValue);
            self.tnums.insert(dst, spilled.tnum.clone());
            self.domain
                .assign_interval(dst, spilled.bounds.min, spilled.bounds.max);
            if let Some(id) = spilled.scalar_id {
                self.scalar_ids.insert(dst, id);
            } else {
                self.scalar_ids.remove(&dst);
            }
            if spilled.precise {
                self.precise_regs.insert(dst);
            } else {
                self.precise_regs.remove(&dst);
            }
            return true;
        }

        if sizes_match && is_aligned {
            // Preserve type and bounds
            self.types.set(dst, spilled.reg_type);
            self.tnums.insert(dst, spilled.tnum);
            self.domain
                .assign_interval(dst, spilled.bounds.min, spilled.bounds.max);

            // Restore scalar id so the filled register remains part of any
            // existing copy chain (e.g. a spilled then reloaded r1 shares the
            // same id as copies of it that stayed in registers).
            if let Some(id) = spilled.scalar_id {
                self.scalar_ids.insert(dst, id);
            } else {
                self.scalar_ids.remove(&dst);
            }

            // Restore precision mark carried at spill time (W2.2).
            if spilled.precise {
                self.precise_regs.insert(dst);
            } else {
                self.precise_regs.remove(&dst);
            }

            // Only restore anchors for U64 (pointers need full 64-bit)
            if size == MemSize::U64 {
                self.restore_anchor_info(dst, &spilled);
            }
        } else if let Some(tn) = narrowed_tnum {
            // Narrowing read of a wider spill whose tnum pins (some of)
            // the bits we're loading (any byte offset within the wider
            // value, LE byte order).
            self.types.set(dst, RegType::ScalarValue);
            let v = tn.value;
            let m = tn.mask;
            // Bounds derived from the narrowed tnum: low = pinned bits,
            // high = pinned | unknown bits. For partial-knowledge tnums
            // this is the tightest interval we can claim without the
            // spill-time bounds.
            let lo = v as i64;
            let hi = (v | m) as i64;
            self.tnums.insert(dst, tn);
            self.domain.assign_interval(dst, lo, hi);
            self.scalar_ids.remove(&dst);
            self.precise_regs.remove(&dst);
        } else {
            // Size mismatch or unaligned - return unbounded scalar for the load size
            self.types.set(dst, RegType::ScalarValue);
            let (min, max) = size.unbounded_scalar_bounds();
            self.tnums.insert(dst, Tnum::unknown());
            self.domain.assign_interval(dst, min, max);
            self.scalar_ids.remove(&dst);
            self.precise_regs.remove(&dst);
        }

        true
    }

    pub fn save_anchor_info(&self, reg: Reg) -> (Option<Reg>, Option<i64>, Option<i64>) {
        let anchor = match self.types.get(reg) {
            RegType::PtrToPacket => Some(Reg::AnchorData),
            RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
            RegType::PtrToPacketEnd => Some(Reg::AnchorDataEnd),
            _ => None,
        };

        if let Some(a) = anchor {
            let hi = self.domain.get(reg, a); // reg - anchor <= hi
            let lo = self.domain.get(a, reg); // anchor - reg <= lo  (i.e., reg - anchor >= -lo)
            let hi = if hi >= INF { None } else { Some(hi) };
            let lo = if lo >= INF { None } else { Some(lo) };
            (Some(a), lo, hi)
        } else {
            (None, None, None)
        }
    }

    /// Save interval mode PtrOffset info for a register
    pub fn save_interval_ptr_offset(&self, reg: Reg) -> (Option<i64>, Option<u64>, Option<i64>) {
        use crate::domains::numeric::NumericDomain;

        if let NumericDomain::Interval(ref ivl) = self.domain {
            if let Some(ptr_off) = ivl.get_ptr_offset(reg) {
                return (Some(ptr_off.off), Some(ptr_off.var_off), ptr_off.range);
            }
        }
        (None, None, None)
    }

    pub fn restore_anchor_info(&mut self, reg: Reg, spilled: &SpilledReg) {
        trace!("Restoring anchor info for {}", reg.name());
        trace!("{:?}, ", spilled);

        use crate::analysis::machine::stack_state::PointerBounds;
        match &spilled.ptr_bounds {
            Some(PointerBounds::Zone {
                anchor,
                anchor_lo,
                anchor_hi,
            }) => {
                if let Some(anchor_reg) = anchor {
                    if let Some(hi) = anchor_hi {
                        self.domain.add_constraint(reg, *anchor_reg, *hi); // reg - anchor <= hi
                    }
                    if let Some(lo) = anchor_lo {
                        self.domain.add_constraint(*anchor_reg, reg, *lo); // anchor - reg <= lo
                    }
                    self.domain.close();
                }
            }
            Some(PointerBounds::Interval {
                off,
                var_off,
                range,
            }) => {
                // Determine anchor from register type
                let anchor = match spilled.reg_type {
                    RegType::PtrToPacket => Some(Reg::AnchorData),
                    RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
                    RegType::PtrToPacketEnd => Some(Reg::AnchorDataEnd),
                    RegType::PtrToStack { .. } => Some(Reg::R10),
                    _ => None, // fallback is None
                };

                if let (Some(anchor_reg), Some(o)) = (anchor, off) {
                    if let NumericDomain::Interval(ref mut ivl) = self.domain {
                        let v = var_off.unwrap_or(0);
                        let ptr_offset = crate::domains::interval::PtrOffset {
                            anchor: anchor_reg,
                            off: *o,
                            var_off: v,
                            range: *range,
                            // id not round-tripped through spill/fill
                            // today; conservative None — loses id-aware
                            // refinement on reload but stays sound.
                            id: None,
                        };

                        // Set the PtrOffset on the register
                        ivl.get_mut(reg).ptr_offset = Some(ptr_offset);
                    }
                }
            }
            None => {}
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
            self.domain.clone(),
            self.tnums.clone(),
        );
    }

    /// Push a callback frame entered via a callback-taking helper (W3.4b).
    /// Caller state is captured like a normal push, but the frame is
    /// flagged so Exit drops the path instead of resuming the caller.
    /// `helper` is stashed on the frame for return-value tightening.
    pub fn push_callback_frame(&mut self, return_pc: usize, helper: u32) {
        self.frames.push_callback(
            return_pc,
            self.types.clone(),
            self.domain.clone(),
            self.tnums.clone(),
            helper,
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

    /// Compact per-register summary for log lines.
    ///
    /// Per-register format (first matching rule wins):
    ///
    /// 1. **Interval mode pointer** — register has a `PtrOffset`:
    ///    `rN=@anchor[±off][+[lo,hi]]`
    ///    e.g. `r10=@r10`, `r2=@r10-8`, `r4=@data+[0,100]`
    ///
    /// 2. **Scalar constant** — `lo == hi`:
    ///    `rN=V`
    ///
    /// 3. **Bounded scalar** — at least one finite bound:
    ///    `rN=[lo,hi]`, `rN=[lo,inf]`, `rN=[-inf,hi]`
    ///
    /// Registers that are `NotInit`, fully unbounded `[-inf,inf]`, or `Zero`
    /// (always 0 and structurally constant) are skipped.
    /// Returns `"(all unbounded)"` when every register is skipped so the caller
    /// always gets a non-empty string to embed in a log line.
    pub fn reg_ranges_str(&self) -> String {
        let mut parts: Vec<String> = Vec::new();

        for r in Reg::ALL {
            if r == Reg::Zero {
                continue;
            }
            if self.types.get(r) == RegType::NotInit {
                continue;
            }

            // Interval mode: PtrOffset captures the anchor relationship that
            // scalar bounds cannot (e.g. R10 is [-inf,inf] as a scalar but
            // carries PtrOffset{anchor:R10, off:0}).  Prefer it when present.
            if let Some(ptr_str) = self.domain.ptr_offset_str(r) {
                parts.push(format!("{}={}", r.name(), ptr_str));
                continue;
            }

            let (lo, hi) = self.domain.get_interval(r);

            // Skip fully unbounded registers — they carry no information.
            if lo == i64::MIN && hi == i64::MAX {
                continue;
            }

            let lo_str = if lo == i64::MIN {
                "-inf".to_string()
            } else {
                lo.to_string()
            };
            let hi_str = if hi == i64::MAX {
                "inf".to_string()
            } else {
                hi.to_string()
            };

            let token = if lo == hi {
                format!("{}={}", r.name(), lo)
            } else {
                format!("{}=[{},{}]", r.name(), lo_str, hi_str)
            };
            parts.push(token);
        }

        if parts.is_empty() {
            "(all unbounded)".to_string()
        } else {
            parts.join(" ")
        }
    }

    /// Compact per-register tnum summary for log lines.
    ///
    /// Uses `Tnum::compact_str()` which emits:
    ///   `V`              for constants (decimal ≤ 65535, else `0x<hex>`)
    ///   `0x<V>/0x<M>`   for partially-known values
    ///
    /// Fully-unknown tnums and `NotInit` registers are skipped.
    /// `Zero` is always structurally constant and is skipped.
    /// Returns an empty string when nothing is worth logging.
    pub fn reg_tnums_compact_str(&self) -> String {
        let mut parts: Vec<String> = Vec::new();

        for r in Reg::ALL {
            if r == Reg::Zero {
                continue;
            }
            if self.types.get(r) == RegType::NotInit {
                continue;
            }
            let tnum = self.get_tnum(r);
            if tnum.is_unknown() {
                continue;
            }
            parts.push(format!("{}={}", r.name(), tnum.compact_str()));
        }

        parts.join(" ")
    }
}
