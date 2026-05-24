// src/analysis/state.rs
use crate::analysis::machine::frame_stack::{CallFrame, FrameLevel, FrameStack};
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::stack_state::StackState;
use crate::common::config::DomainMode;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;
use crate::refinement::symbolic::SymbolicState;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockState {
    pub ptr_id: u32,      // which pointer instance
    pub lock_offset: u32, // offset of spin_lock within value (e.g., 4)
}

/// One entry on the `bpf_res_spin_lock` LIFO held-stack.
/// `reg_id` is the call-site reg-id of the lock pointer; `ptr_id`
/// disambiguates two acquires of the same map at different elements
/// (kernel `find_lock_state` checks `reg->id` AND `ptr` together,
/// verifier.c v6.15 L8326 / L8332).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResLockEntry {
    pub reg_id: u32,
    pub ptr_id: u32,
    pub is_irq: bool,
}

/// Reasons a `bpf_res_spin_unlock` may fail. Distinct so the caller
/// can map each to a specific verifier error variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResLockReleaseError {
    Empty,
    NotInStack,
    OutOfOrder,
    WrongClass,
}

/// Tracks the BTF struct field that a `PtrToBtfId` register currently
/// points into, so helper-arg readers can bound-check the read length
/// against the leaf member's size. Mirrors the kernel's
/// `bpf_reg_state.off` + `btf_struct_walk` work, but kept as a sparse
/// side channel keyed by Reg rather than as a new variant on
/// `RegType::PtrToBtfId` — propagating an extra field across the 100+
/// PtrToBtfId construction sites would be invasive (per the
/// "encapsulate representation changes" guideline).
///
/// Set when pointer arithmetic on a PtrToBtfId resolves a known-size
/// member (`r1 = task; r1 += 1912` → comm at [1912, 1928)). Updated on
/// further `r1 += k` while staying inside the same field. Cleared
/// otherwise, and ignored at the read site if the reg's type is no
/// longer `PtrToBtfId{struct_name}` matching this entry's struct.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BtfFieldRef {
    /// Containing struct name (must match `PtrToBtfId.type_name`; if
    /// the reg's type changes, the entry becomes stale and validators
    /// must filter it out by re-checking).
    pub struct_name: &'static str,
    /// Current absolute byte offset of the reg within the struct.
    pub current_offset: u32,
    /// Start of the containing leaf field (byte offset within struct).
    pub field_start: u32,
    /// End (exclusive) of the containing leaf field.
    pub field_end: u32,
}

/// Per-program `may_goto` iteration budget. Mirrors the kernel's
/// `BPF_MAY_GOTO_LIMIT` (see `kernel/bpf/verifier.c`). Each time the
/// verifier takes a `may_goto` back-edge it decrements this counter; the
/// back-edge becomes infeasible once the counter hits zero, which is what
/// lets the analysis terminate on unbounded-looking loops. Plumbing only in
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

    /// Per-state parent-cached-state link, mirroring kernel
    /// `bpf_verifier_state.parent` (verifier.c v6.15). Set to the
    /// `cache_id` of the most recent cached predecessor on this
    /// state's path. `None` at program entry. Followed by
    /// `mark_chain_precision_backward` to mark precise on the
    /// specific cached states along this path's lineage rather than
    /// all cached states at each PC (which over-marks across
    /// unrelated paths).
    pub parent_cache_id: Option<u32>,

    /// If this state has been cached (i.e. it lives inside
    /// `env.explored_states[pc]`), the unique id assigned to it at
    /// cache time. Used as the link target for descendants'
    /// `parent_cache_id`. `None` for ephemeral (in-flight) states
    /// before they're cached.
    pub cache_id: Option<u32>,

    /// Mirrors kernel `bpf_verifier_state.children_unsafe` set by
    /// `bcf_refine` (verifier.c:24580-81). After a path-unreachable
    /// refinement, the cached ancestor states on that path are no
    /// longer safe to prune *against*: a later arrival subsumed by
    /// one of them may reach the same reject via a *different* path
    /// whose path_cond — and hence the bundle entry the kernel needs
    /// — differs. Skipped as a subsumption candidate in
    /// `handle_*_pruning`. Set by `mark_path_children_unsafe`.
    pub children_unsafe: bool,

    /// SCC bookkeeping — mirror of kernel `bpf_verifier_state.{dfs_depth,
    /// branches, loop_entry}` (verifier.c v6.15 L1675+, L1885+). Drives
    /// the `force_exact` gate in `is_state_visited` that decides whether
    /// subsumption uses RANGE_WITHIN (strict, inside an open SCC) or
    /// NOT_EXACT (lax, outside). Without this gate, zovia silently
    /// subsumes iter-loop body states whose `r6=0` vs `r6=1` would force
    /// the kernel to explore both, masking the deps2-family soundness
    /// FAs.
    ///
    /// `dfs_depth`: state's DFS depth. Successors inherit parent's +1.
    /// `branches`: count of in-flight DFS children through this cached
    /// state. Bumped on each successor push, decremented when a child's
    /// DFS terminates (pruned/exit/reject). 0 ⇒ all DFS through this
    /// state finished.
    /// `loop_entry_cache_id`: cache_id of the outermost loop-header
    /// ancestor on the current DFS path, set by `update_loop_entry` at
    /// back-edges or via `update_branch_counts` propagation.
    pub dfs_depth: u32,
    pub branches: u32,
    /// Kernel-faithful "open paths through this cached state" counter,
    /// parallel to `branches` (which has zovia-internal accounting tied
    /// to subsumption / cleaning / loop-entry tracking and cannot be
    /// changed without breaking dozens of selftests). `dfs_paths` mirrors
    /// the kernel `bpf_verifier_state.branches` field semantics exactly:
    /// - init to 1 at cache creation (kernel `elem->st.branches = 1`,
    ///   verifier.c v6.15 L2816)
    /// - bump parent.dfs_paths by (succ_count - 1) at fork sites — only
    ///   the EXTRA siblings count (kernel `push_stack` L2045 is called
    ///   once per ALT, not once per total successor)
    /// - decremented exactly once per completion (exit OR prune-hit)
    ///   in `complete_dfs_branch`, walking up parent chain until a
    ///   cache with dfs_paths > 0 is found
    /// - reaches 0 iff the entire DFS subtree through this cached state
    ///   has completed
    /// Used by the inf-loop trap gate (`prev.dfs_paths == 0` ⇒ skip
    /// trap, mirroring kernel verifier.c L19024
    /// `if (sl->state.branches)`). The existing `branches` field is
    /// untouched because the subsumption/eviction/loop-entry call
    /// sites in zovia have been tuned against its bumped-per-push
    /// semantics.
    pub dfs_paths: u32,
    pub loop_entry_cache_id: Option<u32>,

    /// Per-path counters for the `add_new_state` sparse-cache heuristic
    /// (`ZOVIA_KERNEL_ENGINE=1`). The kernel's linear `do_check` flow
    /// uses env-wide `insn_processed` / `jmps_processed` because cur
    /// IS the one in-flight path. Zovia's worklist interleaves paths,
    /// so we instead carry per-path counters on each State (cloned at
    /// branches; bumped in run_worklist per popped insn / jmp). The
    /// `prev_*_at_cache` snapshots are set at the most recent cache
    /// event on this path's lineage (kernel `prev_jmps_processed` /
    /// `prev_insn_processed` semantics, L19260-L19261).
    pub path_insn_count: usize,
    pub path_jmp_count: usize,
    pub prev_insn_at_cache: usize,
    pub prev_jmp_at_cache: usize,

    /// Kernel `bpf_verifier_state.jmp_history_cnt` (verifier.c v6.15
    /// ~L4274). Counts branch-decision entries accumulated on the
    /// current state's lineage (incremented at each `push_jmp_history`
    /// site — primarily `is_jmp_point` PCs in do_check L21128-L21131,
    /// plus conditional-jump linked-regs and stack-spill bookkeeping).
    /// Read by `add_new_state`'s safety valve at L20256:
    ///   `force_new_state = ... || cur->jmp_history_cnt > 40`
    /// to avoid accumulating an unbounded jmp_history array. This is a
    /// COUNT OF BRANCH DECISIONS, not raw insns — the kernel value at
    /// PC 1340 for calico c17 from_tnl_debug is 8 (versus
    /// path_insns_delta=42). Bumped in `run_worklist` when popping a
    /// state at a `jmp_point` PC. Cloned at forks.
    pub jmp_history_cnt: usize,

    /// Kernel-aligned `bpf_verifier_state.cleaned` (verifier.c v6.15
    /// L19488). Set to `true` by `clean_verifier_state` when this
    /// cached state's `branches` first hits 0 — its DFS subtree is
    /// complete, so future visits will only COMPARE against it, never
    /// extend through it. At that point dead regs / dead stack slots
    /// are mutated away to make future subsumption looser. Once
    /// cleaned, never re-cleaned (kernel's L19542 guard).
    pub cleaned: bool,

    pub tnums: HashMap<Reg, Tnum>, // tnum info for R0-R10

    /// Identity tokens for scalar values. Two registers (or a register and
    /// a stack slot via `SpilledReg::scalar_id`) that share an id are the
    /// same underlying unknown scalar; refining one propagates to the
    /// others. See `new_scalar_id` / `alloc_scalar_id` / `link_scalar_id`.
    /// Sparse: absent entry = unlinked.
    pub scalar_ids: HashMap<Reg, u32>,

    /// Registers whose exact scalar bounds are "precision-critical" — i.e. a
    /// safety check downstream depends on the tight value rather than a
    /// coarser widened bound. Populated by
    /// [`State::mark_reg_precise`] at branch comparisons and at
    /// variable-offset memory accesses. Propagated forward through ALU
    ///  and persisted across spills via [`SpilledReg::precise`].
    /// Consumed to block state pruning from over-generalising
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

    /// RCU read-side critical section nesting depth. Incremented
    /// by `bpf_rcu_read_lock`, decremented by `bpf_rcu_read_unlock`.
    /// Helpers/kfuncs marked with `CallFlags::RCU` require depth > 0.
    /// Program exit rejects if depth > [`Self::implicit_rcu_at_entry`].
    pub rcu_read_depth: u32,

    /// True iff the program type runs with the kernel's implicit RCU
    /// read-side CS held (kprobe / tracepoint / raw_tp / perf_event).
    /// `analysis::mod` calls `rcu_read_lock()` once at entry for those,
    /// so `rcu_read_depth` starts at 1 instead of 0. The exit check
    /// (`UnreleasedRcuRead`) tolerates a residual depth of 1 in this
    /// case — the kernel releases the lock for us when the prog returns.
    pub implicit_rcu_at_entry: bool,

    /// Preempt-disabled nesting count. Incremented by `bpf_preempt_disable`
    /// kfunc, decremented by `bpf_preempt_enable`. Mirrors kernel
    /// `bpf_verifier_state.active_preempt_locks` (verifier.c v6.15
    /// ~L13560). Helpers/kfuncs marked `CallFlags::MIGHT_SLEEP` are
    /// rejected when this is > 0; `BPF_EXIT` in main prog also rejects.
    pub active_preempt_locks: u32,

    /// LIFO stack of acquired IRQ-flag ids. Pushed by `bpf_local_irq_save`
    /// (and `bpf_res_spin_lock_irqsave`); popped by the matching
    /// `_restore`. `_restore` rejects unless the released id equals the
    /// top of this stack (kernel `release_irq_state` ~L1611). Empty
    /// means no IRQ-disabled region active. The TOP id is what the
    /// kernel calls `state->active_irq_id`. Used by:
    /// - EXIT-in-main-prog gate (kernel ~L11086).
    /// - MIGHT_SLEEP gate inside region (kernel ~L13576).
    /// - tail_call gate (kernel `check_lock` chain).
    pub acquired_irq_ids: Vec<u32>,

    /// LIFO stack of `bpf_res_spin_lock` entries currently held on this
    /// path. Mirrors the kernel `state->refs[]` filtered to
    /// `REF_TYPE_RES_LOCK | REF_TYPE_RES_LOCK_IRQ` (verifier.c v6.15
    /// L8331-8341). Each entry pairs the reg-id (`reg->id`) with the
    /// owning object's pointer-id (map_idx for PtrToMapValue, or kptr
    /// btf-id for PtrToOwnedKptr) so the AA-deadlock check
    /// (`find_lock_state` L8326+) and the "different lock" / "out of
    /// order" unlock checks (L8369-8376) can distinguish two acquires
    /// of the same lock from two different locks of the same map.
    pub acquired_res_locks: Vec<ResLockEntry>,

    /// Remaining `may_goto` iterations on this path. Initialised to
    /// [`BPF_MAY_GOTO_LIMIT`] at entry. Decremented by the `may_goto`
    /// transfer function on the taken branch; once zero the
    /// taken edge is infeasible. Subsumption will require the pruned
    /// state's budget to be ≥ the candidate's.
    pub goto_budget: u32,

    /// Static-analysis counter incremented each time the abstract
    /// interpreter visits a `MayGoto` insn. Mirrors kernel
    /// `bpf_verifier_state.may_goto_depth` (verifier.c v6.15 ~L1757,
    /// bumped in `check_cond_jmp_op` ~L16407). Distinct from
    /// `goto_budget`: this is the per-state visit count used to admit a
    /// RANGE_WITHIN prune class at may_goto pcs (~L19102) and to defuse
    /// the EXACT inf-loop trap on revisits (~L19118). Per-state, not
    /// env-global — parallel DFS branches have independent depths.
    pub may_goto_depth: u32,

    /// maps each pointer register to the scalar register that
    /// contributed its variable offset, if any. Set at `Alu Add ptr +
    /// Reg(scalar)` (handle_add); cleared on dst-clobbering ops (Mov-from-
    /// imm, Load, Mov-from-other-pointer, Mov-from-different-anchor). At
    /// variable-offset memory access sites, the access checker calls
    /// `mark_chain_precision_backward` on this scalar so the access's
    /// bounds-critical lineage survives kernel-aligned widening at
    /// iter_next / may_goto / cb-return (the wideners skip precise regs,
    /// matching kernel `maybe_widen_reg` L8752).
    pub var_off_contributor: HashMap<Reg, Reg>,

    /// Per-pointer accumulated **constant** offset from its anchor —
    /// mirror of the kernel's `ptr_reg->off` field
    /// (verifier.c:14383-14471). Updated on `ptr += K` / `ptr -= K` and
    /// on `ptr += reg` when `reg` is a known constant; **preserved**
    /// across `ptr += reg` with a variable scalar (kernel only updates
    /// `var_off`, leaves `->off` alone). Copied across `mov ptr_dst,
    /// ptr_src`. Cleared by ops that destroy pointer-ness (And/Or/Xor/
    /// Mul/Div/Mod/Shift/Neg) and by `mov` from an immediate.
    ///
    /// Read by [`crate::refinement::refine_stack`] as the explicit K in
    /// the kernel-shape refine_cond: `JSGT(var_off_expr, higher_bound -
    /// sz - (insn_off + K))`. Without this, multi-variable-contributor
    /// chains (`r1 += r0; r1 += r2`) can't be refined — `K`
    /// reconstruction from the abstract distance interval requires a
    /// single contributor, since `distance.lo = K + Σ c_i.lo` and we
    /// only track the last `c_i`.
    pub ptr_const_off: HashMap<Reg, i64>,

    /// Sparse map: register → containing-BTF-field info, used by the
    /// helper-arg validators to bound-check `bpf_strncmp(task->comm, N)`
    /// style reads against the leaf member's size. See [`BtfFieldRef`].
    pub btf_field_refs: HashMap<Reg, BtfFieldRef>,

    /// Set of registers whose tnum the *kernel* would have marked
    /// unknown (`__mark_reg_unknown` via
    /// `is_safe_to_compute_dst_reg_range` returning false; see
    /// verifier.c v6.15 L15089). Concretely populated by DIV / MOD
    /// (always) and non-const shifts. Propagates through subsequent
    /// ALU ops so the imprecision tag survives chained transforms
    /// (e.g. `r8 /= 1; r8 &= 8` — kernel sees both as imprecise).
    /// Cleared on MOV-from-imm, MOV from a clean reg, and on any
    /// load.
    ///
    /// Used at the `PtrToFlowKeys` arithmetic gate
    /// ([alu/validation.rs]) to reject `flow_keys += off` whenever
    /// the kernel would observe `tnum_is_const(off.var_off) == false`,
    /// even if our own tnum stayed const through e.g. our div-by-1
    /// preservation. Closes
    /// verifier_value_illegal_alu::flow_keys_illegal_variable_offset_alu.
    pub kernel_tnum_imprecise: HashSet<Reg>,

    /// Program-default exception callback entry PC.
    /// Used when `bpf_throw` unwinds past every frame without finding a
    /// frame-local `exception_cb` (see [`CallFrame::exception_cb`]). A
    /// modern BPF program registers this via `bpf_set_exception_callback`
    /// at a well-known point; unset means an unhandled throw exits the
    /// program with the throw value in R0. Read through
    /// [`State::effective_exception_cb`] rather than touching the field.
    program_exception_cb: Option<usize>,

    /// BCF symbolic-tracking state (userspace BCF, Phase 1+). `None` unless
    /// the `--bcf` flag enabled symbolic tracking at env init; otherwise a
    /// per-path DAG of `BcfExpr`s parallel to the numeric/tnum domains.
    /// Cloned at every branch fork along with the rest of `State`; the
    /// `Box` keeps the per-clone cost at a pointer copy when the inner
    /// state is large. Mutated in parallel with `domain` / `tnums` by
    /// transfer hooks in `transfer/alu/*`. See
    /// `reference_bcf_symbolic_tracking.md` and
    /// `project_userspace_bcf.md`.
    pub bcf: Option<Box<SymbolicState>>,
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
            parent_cache_id: None,
            cache_id: None,
            children_unsafe: false,
            dfs_depth: 0,
            branches: 0,
            dfs_paths: 0,
            loop_entry_cache_id: None,
            path_insn_count: 0,
            path_jmp_count: 0,
            jmp_history_cnt: 0,
            prev_insn_at_cache: 0,
            prev_jmp_at_cache: 0,
            cleaned: false,
            tnums: tnums.clone(),
            scalar_ids: HashMap::new(),
            precise_regs: HashSet::new(),
            frames: FrameStack::new(),
            frame_depth: 0,
            active_refs: HashSet::new(),
            active_lock: None,
            rcu_read_depth: 0,
            implicit_rcu_at_entry: false,
            active_preempt_locks: 0,
            acquired_irq_ids: Vec::new(),
            acquired_res_locks: Vec::new(),
            goto_budget: BPF_MAY_GOTO_LIMIT,
            may_goto_depth: 0,
            var_off_contributor: HashMap::new(),
            ptr_const_off: HashMap::new(),
            btf_field_refs: HashMap::new(),
            kernel_tnum_imprecise: HashSet::new(),
            program_exception_cb: None,
            bcf: None,
        }
    }

    // ── Exception handler ──────────────────────
    //
    // Handler resolution mirrors the kernel: `bpf_throw` walks the frame
    // stack from innermost outward looking for a frame-local
    // `exception_cb`; if none is set, fall back to the program-default
    // slot. Call sites go through these helpers rather than touching
    // `program_exception_cb` / `CallFrame::exception_cb` directly.
    // Semantics (throw/unwind, callback frame push) land.

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

    // ── may_goto budget ───────────────────────
    //
    // Helpers mirror the spin_lock / ref_id conventions: call sites go
    // through these methods rather than touching `goto_budget` directly.
    // Semantics: decrement on taken edge, reject on empty must-take.

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
    // (encapsulation). Semantics are wired; today these are
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

    // ── Precision marking ───────────────────────────────
    //
    // `mark_reg_precise` is the entry point for callers that recognise a
    // register's exact bounds matter for safety (e.g. a branch comparison
    // that will refine bounds, or a variable offset feeding a memory
    // access). Marks propagate along scalar-id equivalence classes and
    // forward through arithmetic; the field is consumed to block
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

    /// Drop ALL precision marks (regs + spilled stack scalars).
    ///
    /// Mirrors kernel `mark_all_scalars_imprecise` (verifier.c v6.15
    /// L4543), called proactively at checkpoint to produce
    /// maximally-permissive cached states. Precision is then
    /// re-established on demand via `propagate_precision` when a child
    /// path requires it for safety.
    pub fn mark_all_scalars_imprecise(&mut self) {
        self.precise_regs.clear();
        for frame in self.frames.iter_mut() {
            for offset in frame.stack.slot_offsets() {
                if let Some(slot) = frame.stack.get_slot_mut(offset) {
                    slot.precise = false;
                }
            }
        }
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

    /// Demote every reg / spilled slot whose `PtrToAllocMem*` carries
    /// the given dynptr identity to `ScalarValue`. Mirrors kernel
    /// `verifier.c` v6.15 L913-919 inside `destroy_if_dynptr_stack_slot`,
    /// which uses `bpf_for_each_reg_in_vstate` to find slices tagged
    /// with the dynptr's id. Walks every frame's stack so a slice
    /// stored across a subprog call is also caught.
    /// Mark every RCU-protected iter slot as `untrusted` (kind ∈ task,
    /// css). Mirrors kernel verifier.c v6.15 ~L13543: on
    /// `bpf_rcu_read_unlock`, every reg/slot tagged MEM_RCU is
    /// re-flagged PTR_UNTRUSTED. We track this on the iter slot only;
    /// the iter's `_next` consumer rejects on the untrusted slot in the
    /// next iteration. Called by `transfer_call` after a successful
    /// `state.rcu_read_unlock()` that leaves us outside any RCU CS.
    /// Demote every reg / spilled slot whose `PtrToBtfId{,OrNull}` is
    /// flagged `MEM_RCU` to `PTR_UNTRUSTED`. Mirrors kernel verifier.c
    /// v6.15 ~L13543: on `bpf_rcu_read_unlock` (outermost), every
    /// MEM_RCU reg/slot is re-flagged UNTRUSTED so subsequent
    /// helper/kfunc args requiring TRUSTED reject. Iter slots are
    /// handled separately in `invalidate_rcu_iter_slots`.
    ///
    /// Closes rcu_read_lock::{task_untrusted_rcuptr,cross_rcu_region}:
    /// `task->real_parent` loaded under RCU lands as PtrToBtfId{RCU};
    /// after unlock it becomes UNTRUSTED, then `bpf_task_storage_get`
    /// (which expects PtrToTask / TRUSTED PtrToBtfId{task_struct})
    /// rejects.
    pub fn demote_rcu_btf_regs_to_untrusted(&mut self) {
        use crate::analysis::machine::reg_types::PtrFlags;
        let demote_flags = |flags: PtrFlags| -> PtrFlags {
            if flags.contains(PtrFlags::RCU) {
                flags.difference(PtrFlags::RCU | PtrFlags::TRUSTED)
                    .union(PtrFlags::UNTRUSTED)
            } else {
                flags
            }
        };
        let demote_one = |ty: &mut RegType| match ty {
            RegType::PtrToBtfId { flags, .. } | RegType::PtrToBtfIdOrNull { flags, .. } => {
                *flags = demote_flags(*flags);
            }
            _ => {}
        };
        for i in 0..self.types.regs.len() {
            demote_one(&mut self.types.regs[i]);
        }
        for frame in self.frames.iter_mut() {
            for (_off, spilled) in frame.stack.slots.iter_mut() {
                demote_one(&mut spilled.reg_type);
            }
        }
    }

    pub fn invalidate_rcu_iter_slots(&mut self) {
        for frame in self.frames.iter_mut() {
            let offsets = frame.stack.slot_offsets();
            for off in offsets {
                if let Some(slot) = frame.stack.stack_get_iterator(off)
                    && slot.kind.is_rcu_protected()
                    && !slot.untrusted
                {
                    frame.stack.stack_set_iterator(
                        off,
                        crate::analysis::machine::stack_state::IteratorSlot {
                            untrusted: true,
                            ..slot
                        },
                    );
                }
            }
        }
    }

    /// Collect dynptr_ids of every Skb/Xdp dynptr currently registered
    /// in any frame's stack. Mirrors the kernel's reg-walk in
    /// `bpf_for_each_reg_in_vstate` over `xdp/skb_dynptr` slots
    /// (verifier.c v6.15 L913-919). Used by packet-mutating helpers
    /// (`bpf_xdp_adjust_head`, `bpf_skb_pull_data`, …) to invalidate
    /// every slice derived from a packet dynptr — kernel rejects post-
    /// mutation slice access with "invalid mem access 'scalar'"
    /// (`dynptr_fail.c::xdp_invalid_data_slice1`).
    pub fn collect_packet_dynptr_ids(&self) -> Vec<u32> {
        use crate::analysis::machine::stack_state::DynptrKind;
        let mut ids = Vec::new();
        for frame in self.frames.iter() {
            for off in frame.stack.slot_offsets() {
                if let Some(d) = frame.stack.stack_get_dynptr(off as i16)
                    && matches!(d.kind, DynptrKind::Skb | DynptrKind::Xdp)
                    && d.first_slot
                {
                    ids.push(d.dynptr_id);
                }
            }
        }
        ids
    }

    /// Sweep dynptr stack slots whose `ref_id` matches `id`, clear their
    /// annotation and slot bytes, and invalidate any slices tied to those
    /// slots' `dynptr_id`. Mirrors kernel `release_reference` walking all
    /// stack slots in addition to regs (verifier.c v6.15) — needed for
    /// `bpf_dynptr_clone` lineage where clone and parent share `ref_obj_id`
    /// but live at different stack offsets.
    pub fn invalidate_dynptr_slots_by_ref(&mut self, id: u32) {
        if id == 0 {
            return;
        }
        let mut slice_ids: Vec<u32> = Vec::new();
        let mut to_clear: Vec<(crate::analysis::machine::frame_stack::FrameLevel, i16)> =
            Vec::new();
        for (idx, frame) in self.frames.iter().enumerate() {
            let frame_level = crate::analysis::machine::frame_stack::FrameLevel::from_index(idx);
            for off in frame.stack.slot_offsets() {
                let off_i16 = off as i16;
                if let Some(slot) = frame.stack.stack_get_dynptr(off_i16)
                    && slot.ref_id == id
                {
                    if slot.first_slot && !slice_ids.contains(&slot.dynptr_id) {
                        slice_ids.push(slot.dynptr_id);
                    }
                    to_clear.push((frame_level, off_i16));
                }
            }
        }
        for (frame_level, off) in to_clear {
            self.stack_at_mut(frame_level).stack_clear_dynptr(off);
        }
        for did in slice_ids {
            self.invalidate_dynptr_slices(did);
        }
    }

    pub fn invalidate_dynptr_slices(&mut self, dynptr_id: u32) {
        for i in 0..self.types.regs.len() {
            let demote = matches!(
                self.types.regs[i],
                RegType::PtrToAllocMem { dynptr_id: Some(did), .. }
                    | RegType::PtrToAllocMemOrNull { dynptr_id: Some(did), .. }
                    if did == dynptr_id
            );
            if demote {
                self.types.regs[i] = RegType::ScalarValue;
            }
        }
        for frame in self.frames.iter_mut() {
            for (_off, spilled) in frame.stack.slots.iter_mut() {
                let demote = matches!(
                    spilled.reg_type,
                    RegType::PtrToAllocMem { dynptr_id: Some(did), .. }
                        | RegType::PtrToAllocMemOrNull { dynptr_id: Some(did), .. }
                        if did == dynptr_id
                );
                if demote {
                    spilled.reg_type = RegType::ScalarValue;
                }
            }
        }
    }

    /// Convert every reg holding `PtrToOwnedKptr` with the given
    /// `ref_id` from owning to non-owning: clear `ref_id`, set the
    /// `non_owning` flag, keep the type and offset. Mirrors kernel
    /// `verifier.c` v6.15 L12471 `ref_convert_owning_non_owning` —
    /// fired by `bpf_rbtree_add` / `bpf_list_push_*` after they consume
    /// the owning ref into the container. Stack-slot conversion not
    /// modeled (no current test stores an OwnedKptr to stack across a
    /// graph-add).
    pub fn convert_ref_to_non_owning(&mut self, id: u32) {
        for i in 0..self.types.regs.len() {
            if let RegType::PtrToOwnedKptr {
                ref_id: Some(rid),
                offset,
                pointee_btf_id,
                ..
            } = self.types.regs[i]
                && rid == id
            {
                self.types.regs[i] = RegType::PtrToOwnedKptr {
                    ref_id: None,
                    offset,
                    non_owning: true,
                    pointee_btf_id,
                };
            }
        }
    }

    /// Drop every non-owning OwnedKptr reg back to ScalarValue. Fired
    /// on `bpf_spin_unlock` — non-owning refs are only valid under the
    /// lock that scoped the graph-add. Mirrors kernel `verifier.c`
    /// v6.15 L10242 `invalidate_non_owning_refs` (called from L8382 on
    /// spin_unlock).
    pub fn invalidate_non_owning_refs(&mut self) {
        for i in 0..self.types.regs.len() {
            if let RegType::PtrToOwnedKptr {
                non_owning: true, ..
            } = self.types.regs[i]
            {
                self.types.regs[i] = RegType::ScalarValue;
            }
        }
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

    // ── RCU read-side tracking ───────────────────────────

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

    // ── Preempt-disable tracking (kernel verifier.c v6.15 ~L13560) ──

    pub fn preempt_disable(&mut self) {
        self.active_preempt_locks = self.active_preempt_locks.saturating_add(1);
    }

    /// Decrement preempt-disable nesting. Returns `false` (caller must
    /// reject as unmatched-enable) if no disable is active.
    pub fn preempt_enable(&mut self) -> bool {
        if self.active_preempt_locks == 0 {
            return false;
        }
        self.active_preempt_locks -= 1;
        true
    }

    pub fn in_preempt_disabled(&self) -> bool {
        self.active_preempt_locks > 0
    }

    // ── IRQ-flag tracking (kernel verifier.c v6.15 ~L1184-L1626) ──

    /// Mint a fresh IRQ id and push it on the LIFO stack. Caller is
    /// responsible for stamping the corresponding stack slot via
    /// `stack_set_irq_flag`.
    pub fn irq_save(&mut self) -> u32 {
        let id = crate::analysis::machine::reg_types::new_irq_id();
        self.acquired_irq_ids.push(id);
        id
    }

    /// Try to pop a saved IRQ id matching `id`. Returns `Ok(())` on
    /// LIFO match; returns the active (top) id on out-of-order release;
    /// returns `Err(None)` if no IRQ region is active.
    pub fn irq_restore(&mut self, id: u32) -> Result<(), Option<u32>> {
        let top = self.acquired_irq_ids.last().copied();
        match top {
            None => Err(None),
            Some(t) if t == id => {
                self.acquired_irq_ids.pop();
                Ok(())
            }
            Some(t) => Err(Some(t)),
        }
    }

    pub fn in_irq_disabled(&self) -> bool {
        !self.acquired_irq_ids.is_empty()
            || self
                .acquired_res_locks
                .iter()
                .any(|e| e.is_irq)
    }

    /// True iff `(reg_id, ptr_id)` is already in the res-lock stack —
    /// the AA-deadlock predicate (kernel `find_lock_state`,
    /// verifier.c v6.15 L8326). `ptr_id` is the owning-object id
    /// (map_idx for PtrToMapValue, kptr btf-id for PtrToOwnedKptr).
    pub fn res_lock_already_held(&self, reg_id: u32, ptr_id: u32) -> bool {
        self.acquired_res_locks
            .iter()
            .any(|e| e.reg_id == reg_id && e.ptr_id == ptr_id)
    }

    /// Push a res_spin_lock onto the held-stack. `is_irq` distinguishes
    /// `bpf_res_spin_lock_irqsave` from the plain variant (kernel
    /// REF_TYPE_RES_LOCK_IRQ vs REF_TYPE_RES_LOCK).
    pub fn res_lock_acquire(&mut self, reg_id: u32, ptr_id: u32, is_irq: bool) {
        self.acquired_res_locks.push(ResLockEntry {
            reg_id,
            ptr_id,
            is_irq,
        });
    }

    /// Try to release a res_spin_lock matching `(reg_id, ptr_id, is_irq)`.
    /// Mirrors kernel L8369-8376:
    ///   - `Empty` if no lock held (kernel "without taking a lock");
    ///   - `NotInStack` if `(reg_id, ptr_id)` is not in the stack at all
    ///     (kernel "unlock of different lock");
    ///   - `OutOfOrder` if it's in the stack but not at top
    ///     (kernel "cannot be out of order");
    ///   - `WrongClass` if the top matches `(reg_id, ptr_id)` but the
    ///     `is_irq` flavor disagrees (kernel "irq flag acquired by …
    ///     kfuncs cannot be restored …" analogue for res-lock).
    /// On success, pops the top entry.
    pub fn res_lock_release(
        &mut self,
        reg_id: u32,
        ptr_id: u32,
        is_irq: bool,
    ) -> Result<(), ResLockReleaseError> {
        let Some(top) = self.acquired_res_locks.last() else {
            return Err(ResLockReleaseError::Empty);
        };
        if top.reg_id == reg_id && top.ptr_id == ptr_id {
            if top.is_irq != is_irq {
                return Err(ResLockReleaseError::WrongClass);
            }
            self.acquired_res_locks.pop();
            return Ok(());
        }
        let in_stack = self
            .acquired_res_locks
            .iter()
            .any(|e| e.reg_id == reg_id && e.ptr_id == ptr_id);
        if in_stack {
            Err(ResLockReleaseError::OutOfOrder)
        } else {
            Err(ResLockReleaseError::NotInStack)
        }
    }

    pub fn active_irq_id(&self) -> Option<u32> {
        self.acquired_irq_ids.last().copied()
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

    /// Variant of `push_frame` for global-subprog calls. The kernel
    /// verifies global subprogs in isolation, so RCU lock-state changes
    /// inside the body must NOT propagate back to the caller. Stamps
    /// the caller's `rcu_read_depth` onto the new frame's snapshot
    /// field; `transfer_exit` restores it on Exit. Closes
    /// `rcu_read_lock.c::rcu_read_lock_global_subprog_unlock`.
    pub fn push_global_subprog_frame(&mut self, return_pc: usize) {
        let snapshot = self.rcu_read_depth;
        self.push_frame(return_pc);
        let level = self.frames.current_level();
        self.frames.get_mut(level).caller_rcu_read_depth_snapshot = Some(snapshot);
    }

    /// Push a callback frame entered via a callback-taking helper.
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
