// src/analysis/transfer/call/signatures.rs
//
// Unified call-proto representation (Phase 4 W4.1a).
//
// `CallProto` is the single shape consumed by the arg checker for both
// helpers and (Phase 4+) kfuncs. For helpers it's built statically from
// the table below; for kfuncs it'll be built at load time from BTF +
// kfunc flags. Today (W4.1a) only the helper producer exists — the new
// `ret`/`flags`/`side_effects` fields are populated with defaults and
// act as infrastructure for W4.1b+.

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::stack_state::{DynptrKind, IterKind};
use crate::common::constants;
use crate::parsing::btf::SpecialFieldKind;

// ============================================================================
// ArgKind — per-argument expected shape
// ============================================================================

/// Expected shape of a call argument (R1..R5).
///
/// Classic helper kinds today; Phase 4 will extend with `BtfPtr`,
/// `DynptrArg`, `IterArg`, `CallbackArg` variants consumed by the same
/// checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum ArgKind {
    /// Unused argument slot
    DontCare,

    // ---- Map-related ----
    ConstMapPtr,
    /// `ConstMapPtr` whose backing `BpfMapDef::type_` must equal the given
    /// kernel `BPF_MAP_TYPE_*` value. Used by kfuncs (e.g. arena alloc/free)
    /// that demand a specific map kind. Distinct from `ConstMapPtr`'s
    /// helper-id-driven type table because kfunc dispatch doesn't go
    /// through `helper_id_by_name`.
    ConstMapPtrOfType(u32),
    PtrToMapKey,
    PtrToMapValue,
    PtrToUninitMapValue,

    // ---- Memory access ----
    PtrToMem,
    PtrToUninitMem,
    PtrToAllocMem,

    // ---- Size ----
    ConstSize,
    ConstSizeOrZero,
    ConstAllocSizeOrZero,

    // ---- Context / general ----
    PtrToCtx,
    Anything,

    // ---- Socket ----
    PtrToSockCommon,
    PtrToSocket,
    PtrToBTFIdSockCommon,

    // ---- BTF ID ----
    PtrToBtfId,

    // ---- Stack ----
    PtrToStack,

    // ---- Nullable variants ----
    PtrToCtxOrNull,
    PtrToMemOrNull,
    PtrToStackOrNull,
    PtrToMapValueOrNull,

    // ---- Fixed-size pointer ----
    PtrToLong,

    // ---- Callback (W4.1c) ----
    /// Subprog pointer (`RegType::PtrToCallback`). Used by callback-
    /// taking kfuncs like `bpf_set_exception_callback`.
    PtrToCallback,

    // ---- Dynptr (W4.2) ----
    /// `&bpf_dynptr` on the stack (a `PtrToStack` aimed at a 16-byte
    /// dynptr pair).
    ///
    /// `uninit = true` means the kfunc is the *constructor* — the slot
    /// must be uninitialized (no prior dynptr annotation). `false` means
    /// the kfunc is a *consumer* — the slot must hold an initialized
    /// dynptr at its first slot.
    ///
    /// `rdwr_only = true` rejects rdonly dynptrs (e.g. `bpf_dynptr_write`,
    /// `bpf_dynptr_slice_rdwr`). `false` accepts both rdonly and rdwr.
    DynptrArg { uninit: bool, rdwr_only: bool },

    // ---- Iterator (W4.3) ----
    /// `&bpf_iter_*` on the stack. The iterator's kind and lifecycle
    /// state are tracked via `IteratorSlot`; this arg shape encodes both
    /// the expected `kind` and what slot states the kfunc accepts.
    ///
    /// - `Uninit`            — no prior annotation (constructor sink).
    /// - `Active`            — slot must be live (consumer: `*_next`).
    /// - `ActiveOrDrained`   — accept either (destructor sink).
    IterArg { kind: IterKind, expected: IterArgExpect },

    // ---- Cpumask (W5.3) ----
    /// `struct bpf_cpumask *` argument. The actual reg must be a
    /// non-null, ref-tracked `RegType::PtrToCpumask` (i.e. the program
    /// has already null-checked a freshly created cpumask). Consumers
    /// `bpf_cpumask_set_cpu` / `bpf_cpumask_test_cpu` / `bpf_cpumask_first`
    /// / `bpf_cpumask_release` all use this shape.
    PtrToCpumask,

    // ---- Cgroup (W6.3-followon) ----
    /// `struct cgroup *` argument. Same shape as `PtrToCpumask` —
    /// only the non-null `RegType::PtrToCgroup` is accepted; the
    /// program must have null-checked a freshly minted ref before
    /// passing it to `bpf_cgroup_acquire` / `bpf_cgroup_release`.
    PtrToCgroup,

    // ---- Task (Phase 7 wrap-up) ----
    /// `struct task_struct *` argument. Same shape as `PtrToCgroup` —
    /// only the non-null `RegType::PtrToTask` accepted. Program must
    /// have null-checked a `bpf_task_acquire` / `bpf_task_from_pid`
    /// result first; `bpf_get_current_task_btf` returns a non-null
    /// task directly.
    PtrToTask,

    // ---- Arena (W5.5) ----
    /// Bounded arena memory pointer. The actual reg must be a non-null,
    /// ref-tracked `RegType::PtrToArena` (i.e. the program has already
    /// null-checked a freshly allocated arena range). Drives
    /// `bpf_arena_free_pages`'s pointer-arg validation; also reused by
    /// future arena-consumer kfuncs.
    PtrToArena,

    // ---- Owned kptr (W5.4) ----
    /// Refcounted heap-allocated kernel object. The actual reg must be
    /// a non-null, ref-tracked `RegType::PtrToOwnedKptr` (the program
    /// has already null-checked an alloc / pop / refcount_acquire
    /// result). Drives `bpf_obj_drop_impl`, `bpf_refcount_acquire_impl`,
    /// and the list/rbtree push kfuncs (which release the ref).
    PtrToOwnedKptr,

    // ---- Map-value special field (W5.1) ----
    /// Pointer into a map value, aimed at a specific kernel-defined
    /// field embedded in the value (e.g. `bpf_timer`, `bpf_spin_lock`).
    /// The actual reg must be `PtrToMapValue { offset, map_idx }` where
    /// the map's value BTF carries a `SpecialField` of `kind` at exactly
    /// `offset`. Drives `bpf_timer_*` arg validation; future use will
    /// cover real `bpf_spin_lock` pointer args (W5.2) and rbtree/list
    /// roots (W5.4).
    MapValueSpecial { kind: SpecialFieldKind },
}

/// Required slot state for an `IterArg`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum IterArgExpect {
    Uninit,
    Active,
    ActiveOrDrained,
}

// ============================================================================
// CallFlags / RetKind / SideEffect — post-call semantics
// ============================================================================

/// Behavioral flags attached to a call proto.
///
/// For helpers these are currently all unset — existing post-call
/// logic in `transfer.rs` / `types.rs` handles acquire/release/
/// ret-null by helper-id switch. W4.1b migrates that logic to be
/// flag-driven (so kfuncs can reuse it).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CallFlags(u16);

#[allow(dead_code)]
impl CallFlags {
    /// Return value is a freshly-acquired reference (track it).
    pub const ACQUIRE: Self = Self(1 << 0);
    /// One arg (by convention the first ref-typed ptr) is released.
    pub const RELEASE: Self = Self(1 << 1);
    /// Return value may be NULL — fork null / non-null successors.
    pub const RET_NULL: Self = Self(1 << 2);
    /// All pointer args must be trusted (kfunc KF_TRUSTED_ARGS).
    pub const TRUSTED_ARGS: Self = Self(1 << 3);
    /// Must run inside an RCU read-side critical section. Pre-call check
    /// rejects if `state.rcu_read_depth == 0` (W5.2).
    pub const RCU: Self = Self(1 << 4);
    /// Callable only from sleepable programs.
    pub const SLEEPABLE: Self = Self(1 << 5);
    /// Destructive kfunc (KF_DESTRUCTIVE).
    pub const DESTRUCTIVE: Self = Self(1 << 6);
    /// Pre-call: acquires the spin_lock pointed to by R1 (which the
    /// `MapValueSpecial { SpinLock }` arg validator has already shape-
    /// checked). Rejects if a lock is already held; otherwise records
    /// `(ptr_id, lock_offset)` in `state.active_lock`. W5.2.
    pub const SPIN_LOCK_ACQUIRE: Self = Self(1 << 7);
    /// Pre-call: releases the spin_lock pointed to by R1. Rejects if no
    /// lock is held or if the held lock's `ptr_id` doesn't match R1's.
    /// W5.2.
    pub const SPIN_LOCK_RELEASE: Self = Self(1 << 8);
    /// Pre-call: enters an RCU read-side critical section by
    /// incrementing `state.rcu_read_depth`. W5.2.
    pub const RCU_READ_LOCK: Self = Self(1 << 9);
    /// Pre-call: exits an RCU read-side critical section by
    /// decrementing `state.rcu_read_depth`. Rejects if depth is already
    /// zero. W5.2.
    pub const RCU_READ_UNLOCK: Self = Self(1 << 10);
    /// Pre-call precondition: a spin_lock must be held (W5.4). Drives
    /// rbtree / list mutation kfuncs which would race on the per-map-
    /// value head/root without the lock. Rejects with
    /// `NotInSpinLockSection` when `state.active_lock.is_none()`.
    pub const SPIN_LOCK_HELD: Self = Self(1 << 11);
    /// Post-call: skip the default caller-saved clobber of R1..R5
    /// (regtypes + DBM + tnum + scalar_id). The kernel's `bpf_fastcall`
    /// calling-convention hint (v6.13) lets clang emit shorter
    /// sequences around these calls because R1..R5 retain their
    /// pre-call values. Used by select helpers (see `is_fastcall_helper`)
    /// and per-kfunc on cpumask read-only queries. W7.2.
    pub const FASTCALL: Self = Self(1 << 12);

    pub const fn empty() -> Self {
        Self(0)
    }

    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }

    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

impl core::ops::BitOr for CallFlags {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        self.union(rhs)
    }
}

impl core::ops::BitOrAssign for CallFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// Shape of R0 after the call.
///
/// `Unknown` = legacy `update_call_types` arm decides R0's type by
/// helper-id. Concrete variants drive R0 typing through the shared
/// post-call applier (`call::side_effects`) so kfuncs can reuse it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[allow(dead_code)]
pub enum RetKind {
    /// Legacy fallback — leave R0 alone; per-helper logic sets it.
    #[default]
    Unknown,
    /// Kfunc returns `void`. Post-call applier leaves R0 = Scalar (BPF
    /// ABI gives every callee an R0; we don't expose any constraints).
    Void,
    /// Generic scalar return.
    Scalar,
    /// `RegType::PtrToSocket`. Combined with `CallFlags::ACQUIRE` the
    /// applier mints a fresh ref_id; combined with `CallFlags::RET_NULL`
    /// the result wraps as `PtrToSocketOrNull`.
    PtrToSocket,
    /// `RegType::PtrToSockCommon`. Same acquire/null semantics as above.
    PtrToSockCommon,
    /// `RegType::PtrToAllocMem` sized by the value of the arg at index
    /// `size_arg` (W4.2g). Used by `bpf_dynptr_slice`/`slice_rdwr`,
    /// which return a pointer into the dynptr's backing memory whose
    /// length matches the caller-supplied scratch-buffer size. Combined
    /// with `CallFlags::RET_NULL` the applier wraps as
    /// `PtrToAllocMemOrNull`.
    PtrToAllocMemFromArg { size_arg: u8 },
    /// `RegType::PtrToAllocMem` with a const element size baked in
    /// (W4.3). Used by `bpf_iter_*_next` whose returned pointer width
    /// is per-iter-kind, not driven by an arg. Combined with
    /// `CallFlags::RET_NULL` the applier wraps as `PtrToAllocMemOrNull`.
    PtrToAllocMem { mem_size: u64 },
    /// `RegType::PtrToCpumask` (W5.3). `bpf_cpumask_create` returns a
    /// freshly-acquired cpumask. Combined with `CallFlags::ACQUIRE` the
    /// applier mints a fresh ref_id; combined with `CallFlags::RET_NULL`
    /// the result wraps as `PtrToCpumaskOrNull`.
    PtrToCpumask,
    /// `RegType::PtrToArena` (W5.5). Used by `bpf_arena_alloc_pages`
    /// whose returned bounded-memory size is `R(page_cnt_arg+1) * PAGE_SIZE`
    /// — i.e. the page count argument scaled by the architectural page
    /// size (4096). Combined with `CallFlags::ACQUIRE` the applier mints
    /// a fresh ref_id; combined with `CallFlags::RET_NULL` the result
    /// wraps as `PtrToArenaOrNull`.
    PtrToArenaFromArg { page_cnt_arg: u8 },
    /// `RegType::PtrToOwnedKptr` (W5.4). Used by `bpf_obj_new_impl`,
    /// `bpf_refcount_acquire_impl`, and the list/rbtree pop/remove
    /// kfuncs. Combined with `CallFlags::ACQUIRE` the applier mints a
    /// fresh ref_id; combined with `CallFlags::RET_NULL` the result
    /// wraps as `PtrToOwnedKptrOrNull`.
    PtrToOwnedKptr,
    /// `RegType::PtrToCgroup` (W6.3-followon). Used by `bpf_cgroup_from_id`
    /// and `bpf_cgroup_acquire`. Same applier shape as `PtrToCpumask`:
    /// `ACQUIRE` mints a ref, `RET_NULL` wraps as `PtrToCgroupOrNull`.
    PtrToCgroup,
    /// `RegType::PtrToTask` (Phase 7 wrap-up). Used by
    /// `bpf_get_current_task_btf` (no acquire), `bpf_task_acquire`,
    /// `bpf_task_from_pid`. Same applier shape as `PtrToCgroup`:
    /// `ACQUIRE` mints a ref, `RET_NULL` wraps as `PtrToTaskOrNull`.
    PtrToTask,
    /// `RegType::PtrToBtfId { type_name, flags: TRUSTED }` for kernel
    /// types that don't have a dedicated reg-type specialization
    /// (e.g. `struct file *` from `bpf_get_task_exe_file`,
    /// `struct bpf_key *` from `bpf_lookup_user_key`,
    /// `struct sk_buff *` from `bpf_kfunc_nested_acquire_*_test`).
    /// `ACQUIRE` mints a `ref_id` carried on the variant so the
    /// matching `KF_RELEASE` consumer (`bpf_put_file`, `bpf_key_put`,
    /// `bpf_kfunc_nested_release_test`) finds it via `get_ref_id()`;
    /// `RET_NULL` wraps as `PtrToBtfIdOrNull` so the program must
    /// null-check before passing the pointer to a `PtrToBtfId`-arg
    /// kfunc (the kernel's "Possibly NULL pointer passed to trusted
    /// arg0" diagnostic).
    PtrToBtfIdNamed { type_name: &'static str },
    /// `bpf_iter_*_next(&it)` (W4.3b): forks the call into two
    /// successors. Non-NULL: R0 = `PtrToAllocMem { mem_size = elem_size }`,
    /// iterator slot at `iter_arg` stays Active. NULL: R0 = scalar 0,
    /// slot transitions Active → Drained. The kfunc dispatcher in
    /// `transfer_kfunc_proto` recognizes this variant and produces both
    /// successors; the flat-state applier `apply_call_proto_r0` does
    /// not handle it (would assert).
    IterNextElem { iter_arg: u8, elem_size: u64 },
}

/// Post-call side effect entries — applied in order by the shared
/// applier. Today only the release pattern; W4.2/W4.3 add dynptr/iter
/// transitions, stack-buffer init, etc.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum SideEffect {
    /// Drop & invalidate the ref carried on the given arg index (0..=4
    /// → R1..R5). Drives `bpf_sk_release` and ref-release kfuncs.
    ReleaseRefFromArg { arg: u8 },
    /// Read a `PtrToCallback { subprog_pc }` from the given arg and
    /// register that subprog as the program-default exception handler.
    /// Drives `bpf_set_exception_callback`.
    SetExceptionCallbackFromArg { arg: u8 },
    /// Stamp a fresh dynptr annotation on the stack pair pointed to by
    /// `arg` (W4.2). For acquire-tracked kinds (`Ringbuf`) the applier
    /// mints a ref_id and links it onto the slot; for non-acquire kinds
    /// the ref_id is 0. Drives `bpf_dynptr_from_mem`,
    /// `bpf_ringbuf_reserve_dynptr`, etc.
    DynptrInitOnArg {
        arg: u8,
        kind: DynptrKind,
        rdonly: bool,
    },
    /// Clear the dynptr annotation on the stack pair pointed to by `arg`
    /// and drop its ref_id (W4.2). Drives `bpf_ringbuf_submit_dynptr` and
    /// `bpf_ringbuf_discard_dynptr`.
    DynptrReleaseFromArg { arg: u8 },
    /// Initialize an iterator slot (W4.3). Validator already accepted
    /// the arg as Uninit; the applier zeros `bpf_iter_size(kind)` bytes
    /// (matching the kernel's STACK_ITER mark) and stamps an `Active`
    /// annotation with a fresh `iter_id`. Drives `bpf_iter_*_new`.
    IterInitOnArg { arg: u8, kind: IterKind },
    /// Clear an iterator slot (W4.3). Validator accepted Active|Drained
    /// at this slot; the applier wipes the annotation. Drives
    /// `bpf_iter_*_destroy`.
    IterDestroyOnArg { arg: u8 },
}

// ============================================================================
// CallProto — unified shape for helpers and kfuncs
// ============================================================================

/// Maximum number of arguments for a BPF call (helper or kfunc).
pub const MAX_BPF_FUNC_ARGS: usize = 5;

/// Unified proto for a helper or kfunc call.
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)] // W4.1b migrates post-call logic onto ret/flags/side_effects
pub struct CallProto {
    /// Argument shapes for R1..R5 (use `DontCare` for unused).
    pub args: [ArgKind; MAX_BPF_FUNC_ARGS],
    /// Return value shape; `Unknown` defers to legacy post-call logic.
    pub ret: RetKind,
    /// Behavioral flags (acquire/release/ret-null/trust/rcu/...).
    pub flags: CallFlags,
    /// Post-call state mutations to apply in order.
    pub side_effects: &'static [SideEffect],
    /// Pointer-size pairs to validate before the call: each pair links a
    /// pointer arg with the size arg that bounds its access. Drives the
    /// `check_mem_size_pairs` pass and the `validate_ptr_to_mem` skip
    /// for paired pointers (W4.2d: was helper-id-keyed; now lives on
    /// the proto so kfuncs reuse the same machinery).
    pub mem_size_pairs: &'static [MemSizePair],
    /// Prog-type allowlist (W6.3). `None` means "allowed in any prog
    /// type"; `Some(list)` restricts the kfunc to programs whose
    /// `ProgramKind` appears in the list. Mirrors the kernel verifier's
    /// per-kfunc `KF_PROG_TYPE_*` bitmap. Enforced once at the start of
    /// `transfer_kfunc_proto`; helper paths ignore this field.
    pub prog_type_allowlist: Option<&'static [crate::ast::ProgramKind]>,
    /// W6.4c: per-(ops_struct, member) allowlist for struct_ops kfuncs.
    /// `None` means "no per-member restriction". `Some(list)` restricts
    /// the kfunc to subprogs wired into one of the listed (ops_struct,
    /// member) pairs. Mirrors kernel sched_ext's per-callback kfunc
    /// gating (e.g. `scx_bpf_select_cpu_dfl` is only callable from
    /// `sched_ext_ops.select_cpu`). Enforced after `prog_type_allowlist`
    /// in `transfer_kfunc_proto`. Only consulted for `ProgramKind::StructOps`.
    pub ops_member_allowlist: Option<&'static [(&'static str, &'static str)]>,
}

impl CallProto {
    /// Minimal constructor — args only, everything else default.
    /// Used by helper table entries that haven't been flag-migrated yet.
    const fn with_args(args: [ArgKind; MAX_BPF_FUNC_ARGS]) -> Self {
        Self {
            args,
            ret: RetKind::Unknown,
            flags: CallFlags::empty(),
            side_effects: &[],
            mem_size_pairs: &[],
            prog_type_allowlist: None,
            ops_member_allowlist: None,
        }
    }

    /// Builder: set return shape.
    const fn ret(mut self, ret: RetKind) -> Self {
        self.ret = ret;
        self
    }

    /// Builder: set behavioral flags.
    const fn flags(mut self, flags: CallFlags) -> Self {
        self.flags = flags;
        self
    }

    /// Builder: set post-call side effects.
    const fn side_effects(mut self, side_effects: &'static [SideEffect]) -> Self {
        self.side_effects = side_effects;
        self
    }

    /// Builder: set pointer-size pair list.
    const fn mem_size_pairs(mut self, pairs: &'static [MemSizePair]) -> Self {
        self.mem_size_pairs = pairs;
        self
    }

    /// Builder: restrict the kfunc to a specific list of `ProgramKind`s.
    /// Programs with any other prog kind will reject the call. Used by
    /// W6.3 to encode per-kfunc prog-type allowlists (cgroup / cpumask /
    /// task families gate access to syscall / tracepoint / perf_event
    /// and reject from raw_tp).
    const fn prog_type_allowlist(
        mut self,
        list: &'static [crate::ast::ProgramKind],
    ) -> Self {
        self.prog_type_allowlist = Some(list);
        self
    }

    /// Builder: restrict a struct_ops kfunc to a specific list of
    /// (ops_struct, member) pairs. W6.4c.
    const fn ops_member_allowlist(
        mut self,
        list: &'static [(&'static str, &'static str)],
    ) -> Self {
        self.ops_member_allowlist = Some(list);
        self
    }
}

// ============================================================================
// Pointer-Size Pair Table
// ============================================================================

/// A pointer argument paired with its size argument.
#[derive(Debug, Clone, Copy)]
pub struct MemSizePair {
    pub ptr_reg: Reg,
    pub size_reg: Reg,
    /// If true, size can be 0 (and if ptr is NULL, size MUST be 0)
    pub allow_zero: bool,
}

impl MemSizePair {
    pub(crate) const fn new(ptr_reg: Reg, size_reg: Reg) -> Self {
        Self {
            ptr_reg,
            size_reg,
            allow_zero: false,
        }
    }

    pub(crate) const fn new_nullable(ptr_reg: Reg, size_reg: Reg) -> Self {
        Self {
            ptr_reg,
            size_reg,
            allow_zero: true,
        }
    }
}

// ============================================================================
// Helper Function Prototypes
// ============================================================================

// Convenience aliases
use ArgKind::*;

/// Helper function prototypes indexed by helper ID.
/// Returns None for unknown helpers.
pub fn get_helper_proto(helper: u32) -> Option<CallProto> {
    Some(match helper {
        // ---- Map operations ----
        constants::BPF_MAP_LOOKUP_ELEM => CallProto::with_args([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_MAP_UPDATE_ELEM => CallProto::with_args([
            ConstMapPtr,   // R1: map
            PtrToMapKey,   // R2: key
            PtrToMapValue, // R3: value
            Anything,      // R4: flags
            DontCare,
        ]),

        constants::BPF_MAP_DELETE_ELEM => CallProto::with_args([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_LOCAL_STORAGE => CallProto::with_args([
            ConstMapPtr, // R1: map
            Anything,    // R2: index
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- Memory helpers ----
        constants::BPF_GET_STACK => CallProto::with_args([
            PtrToCtx,
            PtrToUninitMem,
            ConstSizeOrZero,
            Anything,
            DontCare,
        ])
        .mem_size_pairs(&pairs::GET_STACK),

        // ---- Tail call ----
        constants::BPF_TAIL_CALL => CallProto::with_args([
            PtrToCtx,    // R1: ctx
            ConstMapPtr, // R2: prog_array_map
            Anything,    // R3: index
            DontCare,
            DontCare,
        ]),

        // ---- Socket/context helpers ----
        constants::BPF_GET_SOCKET_COOKIE => CallProto::with_args([
            PtrToCtx, // R1: ctx
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_GET_NETNS_COOKIE => CallProto::with_args([
            PtrToCtxOrNull, // R1: ctx (nullable — kernel accepts NULL)
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_CSUM_UPDATE => CallProto::with_args([
            PtrToCtx, // R1: skb
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_CSUM_DIFF => CallProto::with_args([
            PtrToMemOrNull,  // R1: from
            ConstSizeOrZero, // R2: from_size
            PtrToMemOrNull,  // R3: to
            ConstSizeOrZero, // R4: to_size
            Anything,        // R5: seed
        ])
        .mem_size_pairs(&pairs::CSUM_DIFF),

        constants::BPF_SKB_ECN_SET_CE => CallProto::with_args([
            PtrToCtxOrNull, // R1: skb (can be NULL)
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_HASH_RECALC => CallProto::with_args([
            PtrToCtx, // R1: ctx
            DontCare, DontCare, DontCare, DontCare,
        ]),

        // ---- SKB data access ----
        constants::BPF_SKB_LOAD_BYTES => CallProto::with_args([
            PtrToCtx,       // R1: skb
            Anything,       // R2: offset
            PtrToUninitMem, // R3: to (destination buffer)
            ConstSize,      // R4: len
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_LOAD_BYTES),

        constants::BPF_SKB_VLAN_PUSH => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: vlan_proto
            Anything, // R3: vlan_tci
            DontCare, DontCare,
        ]),

        constants::BPF_SKB_GET_TUNNEL_KEY => CallProto::with_args([
            PtrToCtx,       // R1: skb
            PtrToUninitMem, // R2: key (buffer to store key)
            ConstSize,      // R3: size
            Anything,       // R4: flags
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_GET_TUNNEL_KEY),

        constants::BPF_SKB_SET_TUNNEL_KEY => CallProto::with_args([
            PtrToCtx,  // R1: skb
            PtrToMem,  // R2: key
            ConstSize, // R3: size
            Anything,  // R4: flags
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_SET_TUNNEL_KEY),

        constants::BPF_SKB_VLAN_POP => CallProto::with_args([
            PtrToCtx, // R1: skb
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_SKB_STORE_BYTES => CallProto::with_args([
            PtrToCtx,  // R1: skb
            Anything,  // R2: offset
            PtrToMem,  // R3: from (source buffer)
            ConstSize, // R4: len
            DontCare,
        ])
        .mem_size_pairs(&pairs::SKB_STORE_BYTES),

        // ---- Redirect ----
        constants::BPF_REDIRECT => CallProto::with_args([
            Anything, // R1: ifindex
            Anything, // R2: flags
            DontCare, DontCare, DontCare,
        ]),

        // ---- XDP helpers ----
        constants::BPF_XDP_ADJUST_HEAD
        | constants::BPF_XDP_ADJUST_TAIL
        | constants::BPF_XDP_ADJUST_META => CallProto::with_args([
            PtrToCtx, // R1: xdp_md
            Anything, // R2: delta
            DontCare, DontCare, DontCare,
        ]),

        // ---- Tail modification ----
        constants::BPF_SKB_CHANGE_TAIL => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: len
            Anything, // R3: flags
            DontCare, DontCare,
        ]),

        // ---- Socket lookup ----
        constants::BPF_SKC_LOOKUP_TCP => CallProto::with_args([
            PtrToCtx, // R1: ctx
            PtrToMem, // R2: tuple
            Anything, // R3: tuple_size
            DontCare, DontCare,
        ])
        .ret(RetKind::PtrToSockCommon)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL))
        .mem_size_pairs(&pairs::SK_LOOKUP_TCP),

        constants::BPF_SK_LOOKUP_TCP => CallProto::with_args([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ])
        .ret(RetKind::PtrToSocket)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL))
        .mem_size_pairs(&pairs::SK_LOOKUP_TCP),

        constants::BPF_SK_LOOKUP_UDP => CallProto::with_args([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ])
        .ret(RetKind::PtrToSocket)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL))
        .mem_size_pairs(&pairs::SK_LOOKUP_UDP),

        constants::BPF_SK_RELEASE => CallProto::with_args([
            PtrToSocket, // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        constants::BPF_SKC_TO_UDP6_SOCK => CallProto::with_args([
            PtrToSocket, // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_SK_FULLSOCK => CallProto::with_args([
            PtrToSockCommon, // R1: sock_common
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_TCP_SOCK => {
            CallProto::with_args([PtrToSockCommon, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Socket storage helpers ----
        constants::BPF_SK_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,
            PtrToBTFIdSockCommon,
            PtrToMapValueOrNull,
            Anything,
            DontCare,
        ]),

        constants::BPF_GET_SOCKOPT => {
            // R1 is `bpf_socket` (kernel UAPI). The kernel verifier accepts
            // it as PtrToCtx in cgroup_sock_addr/sock_ops contexts AND as
            // a trusted PtrToBtfId{sock} in struct_ops contexts (where the
            // BPF_PROG-wrapped struct_ops method has unpacked the sock arg
            // out of the ctx array). Modeling as `Anything` matches the
            // multi-shape acceptance and lets struct_ops methods like
            // bpf_dctcp_init pass; the size pair on (R4, R5) still gates
            // the actual write region.
            CallProto::with_args([Anything, Anything, Anything, PtrToUninitMem, ConstSize])
                .mem_size_pairs(&pairs::GET_SOCKOPT)
        }

        // ---- FIB lookup ----
        constants::BPF_FIB_LOOKUP => CallProto::with_args([
            PtrToCtx, // R1: ctx
            PtrToMem, // R2: params (bpf_fib_lookup struct)
            Anything, // R3: plen
            Anything, // R4: flags
            DontCare,
        ]),

        constants::BPF_PROBE_READ
        | constants::BPF_PROBE_READ_STR
        | constants::BPF_PROBE_READ_USER => CallProto::with_args([
            PtrToUninitMem,  // R1: dst
            ConstSizeOrZero, // R2: size
            Anything,        // R3: unsafe_ptr (user address)
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::PROBE_READ),

        constants::BPF_PROBE_READ_KERNEL => CallProto::with_args([
            PtrToUninitMem,  // R1: dst (output buffer)
            ConstSizeOrZero, // R2: size
            Anything,        // R3: unsafe_ptr (kernel address, not validated)
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::PROBE_READ),

        constants::BPF_PERF_EVENT_READ_VALUE => CallProto::with_args([
            ConstMapPtr,     // R1: map
            Anything,        // R2: flags
            PtrToUninitMem,  // R3: buf
            ConstSizeOrZero, // R4: buf_size
            DontCare,
        ])
        .mem_size_pairs(&pairs::PERF_EVENT_READ_VALUE),

        constants::BPF_PERF_PROG_READ_VALUE => CallProto::with_args([
            PtrToCtx,        // R1: ctx
            PtrToUninitMem,  // R2: buf
            ConstSizeOrZero, // R3: buf_size
            DontCare,        // R4: flags (not verified here)
            DontCare,
        ])
        .mem_size_pairs(&pairs::PERF_PROG_READ_VALUE),

        // ---- Spin lock (W5.2) ----
        // void bpf_spin_lock(struct bpf_spin_lock *lock)
        // void bpf_spin_unlock(struct bpf_spin_lock *lock)
        // R1 must be a PtrToMapValue aimed at a `bpf_spin_lock` field
        // recorded in the map's value-type BTF. The shape check rides
        // `MapValueSpecial { SpinLock }`; the lock-state mutation
        // (`active_lock` acquire / release) is driven by the
        // `SPIN_LOCK_{ACQUIRE,RELEASE}` flags in the pre-call hook.
        constants::BPF_SPIN_LOCK => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::SpinLock },
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::SPIN_LOCK_ACQUIRE),

        constants::BPF_SPIN_UNLOCK => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::SpinLock },
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::SPIN_LOCK_RELEASE),

        // ---- RCU read-side critical section (W5.2) ----
        // void bpf_rcu_read_lock(void)
        // void bpf_rcu_read_unlock(void)
        constants::BPF_RCU_READ_LOCK => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RCU_READ_LOCK),

        constants::BPF_RCU_READ_UNLOCK => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RCU_READ_UNLOCK),

        // ---- Timers (W5.1) ----
        // long bpf_timer_init(struct bpf_timer *timer, struct bpf_map *map, u64 flags)
        constants::BPF_TIMER_INIT => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            ConstMapPtr,                                       // R2: map the cb will operate on
            Anything,                                          // R3: flags
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // long bpf_timer_set_callback(struct bpf_timer *timer,
        //                             void *callback_fn)
        // Routed through is_callback_helper → transfer_callback_helper for
        // the cb-frame fork; this proto just covers the arg validation
        // (timer field + PtrToCallback) and post-call R0 typing for the
        // skip successor (the cb-frame branch updates R0 separately).
        constants::BPF_TIMER_SET_CALLBACK => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            PtrToCallback,                                     // R2: callback subprog
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // long bpf_timer_start(struct bpf_timer *timer, u64 nsecs, u64 flags)
        constants::BPF_TIMER_START => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            Anything,                                          // R2: nsecs
            Anything,                                          // R3: flags
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // long bpf_timer_cancel(struct bpf_timer *timer)
        constants::BPF_TIMER_CANCEL => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::Timer }, // R1: &timer field
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Ringbuf helpers ----
        constants::BPF_RINGBUF_OUTPUT => CallProto::with_args([
            ConstMapPtr,     // R1: ringbuf map
            PtrToMem,        // R2: data to copy (must be initialized)
            ConstSizeOrZero, // R3: size
            Anything,        // R4: flags
            DontCare,
        ]),

        constants::BPF_RINGBUF_RESERVE => CallProto::with_args([
            ConstMapPtr,
            ConstAllocSizeOrZero,
            Anything,
            DontCare,
            DontCare,
        ]),

        constants::BPF_RINGBUF_SUBMIT => {
            CallProto::with_args([PtrToAllocMem, Anything, DontCare, DontCare, DontCare])
        }

        // W6.5: bpf_user_ringbuf_drain(map, callback, ctx, flags)
        // Drains a user-space-written ringbuf, invoking `callback`
        // for each sample. Routed through `is_callback_helper` →
        // `transfer_callback_helper` so the callback subprog gets a
        // pushed frame on the enter-callback successor; the callback
        // signature is `(struct bpf_dynptr *dynptr, void *ctx) -> long`,
        // but per the existing callback convention we leave R1/R2 as
        // NotInit in the callee frame — programs that dereference
        // `ctx` (R2) without typing reject, which is the right outcome
        // for the lone existing test (`unsafe_ringbuf_drain`).
        constants::BPF_USER_RINGBUF_DRAIN => CallProto::with_args([
            ConstMapPtrOfType(crate::common::constants::BPF_MAP_TYPE_USER_RINGBUF),
            PtrToCallback,
            Anything,
            Anything,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Information helpers ----
        constants::BPF_KTIME_GET_NS => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }
        constants::BPF_KTIME_GET_COARSE_NS => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Process info helpers ----
        constants::BPF_GET_TASK_STACK => CallProto::with_args([
            PtrToBtfId,
            PtrToUninitMem,
            ConstSizeOrZero,
            Anything,
            DontCare,
        ])
        .mem_size_pairs(&pairs::GET_TASK_STACK),

        // ---- Sockmap operations ----
        constants::BPF_SOCK_MAP_UPDATE => CallProto::with_args([
            PtrToCtx,    // R1: bpf_sock_ops context (SockOps only)
            ConstMapPtr, // R2: sockmap
            PtrToMapKey, // R3: key
            Anything,    // R4: flags
            DontCare,
        ]),

        // ---- Miscellaneous ----
        constants::BPF_GET_PRANDOM_U32 => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_TRACE_PRINTK => CallProto::with_args([
            PtrToMem,  // R1: fmt string
            ConstSize, // R2: fmt_size (MUST BE > 0)
            Anything,  // R3: arg1
            Anything,  // R4: arg2
            Anything,  // R5: arg3
        ]),

        constants::BPF_STRTOUL => {
            CallProto::with_args([PtrToMem, ConstSize, Anything, PtrToLong, DontCare])
        }

        constants::BPF_STRTOL => {
            CallProto::with_args([PtrToMem, ConstSize, Anything, PtrToLong, DontCare])
        }

        constants::BPF_CHECK_MTU => CallProto::with_args([
            PtrToCtx,       // R1: ctx (skb / xdp_md)
            Anything,       // R2: ifindex
            PtrToUninitMem, // R3: u32 *mtu_len — writable; rdonly-map gated
            Anything,       // R4: len_diff
            Anything,       // R5: flags
        ]),

        constants::BPF_COPY_FROM_USER => CallProto::with_args([
            PtrToUninitMem, // R1: dst — writable; rdonly-map gated
            ConstSize,      // R2: size
            Anything,       // R3: user_ptr
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_CGROUP_CLASS_ID => {
            CallProto::with_args([PtrToCtx, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_GET_CURRENT_COMM => CallProto::with_args([
            PtrToUninitMem, // R1: buf (output buffer for comm string)
            ConstSize,      // R2: size_of_buf
            DontCare,
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::GET_CURRENT_COMM),

        constants::BPF_PERF_EVENT_OUTPUT => CallProto::with_args([
            PtrToCtx,    // R1: ctx
            ConstMapPtr, // R2: map
            Anything,    // R3: flags
            PtrToMem,    // R4: data
            ConstSize,   // R5: size
        ])
        .mem_size_pairs(&pairs::PERF_EVENT_OUTPUT),

        constants::BPF_L3_CSUM_REPLACE => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: offset
            Anything, // R3: from
            Anything, // R4: to
            Anything, // R5: flags
        ]),

        constants::BPF_L4_CSUM_REPLACE => CallProto::with_args([
            PtrToCtx, // R1: skb
            Anything, // R2: offset
            Anything, // R3: from
            Anything, // R4: to
            Anything, // R5: flags
        ]),

        // ---- W7.1: storage_get/_delete (sk + task + inode) ----
        // R0 typing for *_storage_get is handled by the legacy
        // `update_call_types` arm in transfer/types.rs, which keys
        // PtrToMapValueOrNull off R1 (the map) — same pattern as
        // bpf_get_local_storage. The arg-side proto is identical across
        // the three families; only R2's expected ptr family differs
        // (sock_common vs btf_id task vs btf_id inode).
        constants::BPF_SK_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToBTFIdSockCommon,   // R2: sk
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        constants::BPF_TASK_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToTask,              // R2: task (Phase 7 wrap-up: typed)
            PtrToMapValueOrNull,    // R3: value (may be NULL)
            Anything,               // R4: flags
            DontCare,
        ]),

        constants::BPF_TASK_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToTask,              // R2: task
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        constants::BPF_INODE_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToBtfId,             // R2: inode
            PtrToMapValueOrNull,    // R3: value
            Anything,               // R4: flags
            DontCare,
        ]),

        constants::BPF_INODE_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,            // R1: map
            PtrToBtfId,             // R2: inode
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Phase 7 wrap-up: bpf_get_current_task_btf ----
        // Returns the kernel's current-task pointer, typed as PTR_TO_BTF_ID
        // (task_struct *) with PTR_TRUSTED. Modeled here as PtrToTask (no
        // ACQUIRE — the kernel guarantees the returned pointer is live for
        // the duration of the program). Zero arguments.
        constants::BPF_GET_CURRENT_TASK_BTF => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToTask),

        // ---- W7.1: bpf_d_path ----
        // (path: struct path *, buf: writable, sz: const) -> s64
        constants::BPF_D_PATH => CallProto::with_args([
            PtrToBtfId,     // R1: struct path *
            PtrToUninitMem, // R2: buf
            ConstSize,      // R3: sz
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::D_PATH)
        .ret(RetKind::Scalar),

        // ---- W7.1: bpf_snprintf ----
        // (buf, sz, fmt, data, data_len) -> s32
        // Lite scope: fmt and data are accepted as PtrToMem; the kernel
        // additionally validates fmt against const-rodata + matches data
        // entries against fmt specifiers (not modeled).
        constants::BPF_SNPRINTF => CallProto::with_args([
            PtrToUninitMem,  // R1: buf
            ConstSizeOrZero, // R2: sz
            PtrToMem,        // R3: fmt (read-only; not size-paired — string)
            PtrToMemOrNull,  // R4: data (u64 array; may be NULL if data_len=0)
            ConstSizeOrZero, // R5: data_len
        ])
        .mem_size_pairs(&pairs::SNPRINTF)
        .ret(RetKind::Scalar),

        // ---- W7.1: bpf_strncmp ----
        // (s1: PtrToMem, s1_sz: ConstSize, s2: PtrToMem) -> s32
        // Kernel additionally requires s2 to be a const string (rodata);
        // we relax to PtrToMem.
        constants::BPF_STRNCMP => CallProto::with_args([
            PtrToMem,  // R1: s1
            ConstSize, // R2: s1_sz
            PtrToMem,  // R3: s2 (const string in rodata)
            DontCare,
            DontCare,
        ])
        .mem_size_pairs(&pairs::STRNCMP)
        .ret(RetKind::Scalar),

        // ---- Dynptr helpers (W4.2) ----
        //
        // These are real helpers (numeric BPF_FUNC_* ids in v6.15 uapi),
        // not kfuncs — clang emits CALL insns with the helper id, not
        // PSEUDO_KFUNC_CALL. Their prototypes happen to live in the
        // name-keyed table next to the related kfuncs (slice/from_skb/
        // from_xdp); delegate by name so we don't duplicate them. Without
        // these arms the entire dynptr modeling (init/release/leak
        // detection) is unreachable on numeric-helper calls.
        constants::BPF_DYNPTR_FROM_MEM => return get_kfunc_proto("bpf_dynptr_from_mem"),
        constants::BPF_RINGBUF_RESERVE_DYNPTR => {
            return get_kfunc_proto("bpf_ringbuf_reserve_dynptr");
        }
        constants::BPF_RINGBUF_SUBMIT_DYNPTR => {
            return get_kfunc_proto("bpf_ringbuf_submit_dynptr");
        }
        constants::BPF_RINGBUF_DISCARD_DYNPTR => {
            return get_kfunc_proto("bpf_ringbuf_discard_dynptr");
        }
        constants::BPF_DYNPTR_READ => return get_kfunc_proto("bpf_dynptr_read"),
        constants::BPF_DYNPTR_WRITE => return get_kfunc_proto("bpf_dynptr_write"),
        constants::BPF_DYNPTR_DATA => return get_kfunc_proto("bpf_dynptr_data"),

        _ => return None,
    })
}

// ============================================================================
// Kfunc Prototypes (W4.1c)
// ============================================================================
//
// Today this is a name-keyed override table — a small set of kfuncs whose
// arg shape and side effects can't (yet) be derived purely from BTF +
// KF_* flags. W4.2 (dynptr) and W4.3 (open-coded iterators) will populate
// it heavily; eventually most kfuncs should fall through to a generic
// BTF-driven producer that reads the func-proto BTF + KF flags directly.

/// Prog-type allowlist for kfunc families that need a vmlinux BTF
/// context (W6.3 / W6.3-followon). Used by the cpumask family
/// (`bpf_cpumask_*`) and the cgroup family (`bpf_cgroup_*`) — both
/// mirror the kernel verifier's `KF_PROG_TYPE_*` set. Permitted in
/// syscall / tracing (fentry/fexit/tp_btf/iter) / tracepoint /
/// perf_event programs; rejected from raw_tp and network paths.
const CPUMASK_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 5] = [
    crate::ast::ProgramKind::Syscall,
    crate::ast::ProgramKind::Tracing,
    crate::ast::ProgramKind::Tracepoint,
    crate::ast::ProgramKind::PerfEvent,
    // W6.4b: sched_ext implementations call bpf_cpumask_test_cpu and
    // friends on idle masks fetched via scx_bpf_get_idle_cpumask.
    crate::ast::ProgramKind::StructOps,
];

/// Cgroup kfunc family allowlist — same set as cpumask. Aliased
/// rather than reusing the cpumask constant directly so future
/// per-family divergence (e.g. cgroup-only access from `cgroup/skb`)
/// can be encoded without unwiring callers.
const CGROUP_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 5] =
    CPUMASK_KFUNC_PROG_TYPES;

/// Task kfunc family allowlist (Phase 7 wrap-up). Mirrors the kernel's
/// `tasks_kfunc_set` registration: tracing (fentry/fexit/tp_btf), LSM,
/// tracepoint, perf_event, syscall, struct_ops. LSM is added vs the
/// cpumask/cgroup list because `local_storage.c` exercises
/// `bpf_get_current_task_btf` from `lsm.s/*` hooks.
const TASK_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 6] = [
    crate::ast::ProgramKind::Syscall,
    crate::ast::ProgramKind::Tracing,
    crate::ast::ProgramKind::Tracepoint,
    crate::ast::ProgramKind::PerfEvent,
    crate::ast::ProgramKind::Lsm,
    crate::ast::ProgramKind::StructOps,
];

/// LSM-only kfunc family — `bpf_path_d_path`, `bpf_get_task_exe_file`,
/// `bpf_put_file`. Kernel registers these in `bpf_lsm_kfunc_set` only.
/// `verifier_vfs_reject.c::path_d_path_kfunc_non_lsm` calls
/// `bpf_path_d_path` from `fentry/vfs_open` and the kernel rejects
/// ("calling kernel function bpf_path_d_path is not allowed").
const LSM_ONLY_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 1] =
    [crate::ast::ProgramKind::Lsm];

/// `bpf_dynptr_from_skb` allowlist (W4.2f). The kfunc is registered for
/// program types that receive an `__sk_buff *` context — sched_cls/act
/// (tc), socket_filter, cgroup_skb, lwt_*, sk_skb, sock_ops, sk_msg,
/// flow_dissector. raw_tp / tracing / xdp / others get the kernel's
/// "calling kernel function bpf_dynptr_from_skb is not allowed".
const SKB_DYNPTR_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 11] = [
    crate::ast::ProgramKind::SchedCls,
    crate::ast::ProgramKind::SchedAct,
    crate::ast::ProgramKind::SocketFilter,
    crate::ast::ProgramKind::CgroupSkb,
    crate::ast::ProgramKind::LwtIn,
    crate::ast::ProgramKind::LwtOut,
    crate::ast::ProgramKind::LwtXmit,
    crate::ast::ProgramKind::SkSkb,
    crate::ast::ProgramKind::SockOps,
    crate::ast::ProgramKind::SkMsg,
    crate::ast::ProgramKind::FlowDissector,
];

/// `bpf_dynptr_from_xdp` allowlist (W4.2f) — only XDP programs receive
/// `xdp_md *` context.
const XDP_DYNPTR_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 1] =
    [crate::ast::ProgramKind::Xdp];

/// Sched_ext kfunc family allowlist (W6.4b). The kernel registers most
/// `scx_bpf_*` kfuncs against the sched_ext class. A subset (notably
/// `scx_bpf_create_dsq` / `_destroy_dsq` / `_exit_bstr`) is also exposed
/// to `BPF_PROG_TYPE_SYSCALL` — see `prog_run.bpf.c`. We accept both for
/// every scx_bpf_* proto rather than tracking the per-kfunc subdivision;
/// the corpus has no test that distinguishes them, and broadening here
/// cannot produce a false_accept for any current entry.
const SCHED_EXT_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 2] = [
    crate::ast::ProgramKind::StructOps,
    crate::ast::ProgramKind::Syscall,
];

/// Kfunc prototypes indexed by kfunc name. Returns `None` for kfuncs not
/// yet on the proto path — the caller falls back to the legacy bespoke
/// dispatch in `kfunc.rs`.
pub fn get_kfunc_proto(name: &str) -> Option<CallProto> {
    Some(match name {
        "bpf_set_exception_callback" => CallProto::with_args([
            PtrToCallback, // R1: subprog ptr (PSEUDO_FUNC)
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::SetExceptionCallbackFromArg { arg: 0 }]),

        // ---- Ringbuf dynptrs (W4.2c) ----
        //
        // void bpf_ringbuf_reserve_dynptr(struct bpf_map *rb, u32 size,
        //                                 u64 flags, struct bpf_dynptr *ptr)
        //
        // R4 is the dynptr ctor sink. Mints a ref_id, stamps a
        // `Ringbuf` annotation on the stack pair. Returns 0/-errno;
        // failure path leaves the slot initialized but the dynptr's
        // internal data NULL — runtime concern, not a verifier one.
        "bpf_ringbuf_reserve_dynptr" => CallProto::with_args([
            ConstMapPtr, // R1: ringbuf map
            Anything,    // R2: size
            Anything,    // R3: flags
            DynptrArg { uninit: true, rdwr_only: false }, // R4: &dynptr
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::DynptrInitOnArg {
            arg: 3,
            kind: DynptrKind::Ringbuf,
            rdonly: false,
        }]),

        // void bpf_ringbuf_submit_dynptr(struct bpf_dynptr *ptr, u64 flags)
        "bpf_ringbuf_submit_dynptr" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false }, // R1: &dynptr
            Anything,                                       // R2: flags
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::DynptrReleaseFromArg { arg: 0 }]),

        // void bpf_ringbuf_discard_dynptr(struct bpf_dynptr *ptr, u64 flags)
        "bpf_ringbuf_discard_dynptr" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false }, // R1: &dynptr
            Anything,                                       // R2: flags
            DontCare,
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::DynptrReleaseFromArg { arg: 0 }]),

        // ---- Local-cluster dynptrs (W4.2e) ----
        //
        // int bpf_dynptr_from_mem(void *data, u32 size, u64 flags,
        //                         struct bpf_dynptr *ptr)
        //
        // Wraps a caller-owned buffer (stack/map/packet) in a Local
        // dynptr. R1 is the buffer; mem-size-pair (R1,R2) proves that
        // `size` bytes are accessible. No ref tracking — Local dynptrs
        // are pure metadata and need no release.
        "bpf_dynptr_from_mem" => CallProto::with_args([
            PtrToMem,    // R1: source buffer
            ConstSize,   // R2: size
            Anything,    // R3: flags (rdonly bit etc. — not modeled yet)
            DynptrArg { uninit: true, rdwr_only: false }, // R4: &dynptr
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::DynptrInitOnArg {
            arg: 3,
            kind: DynptrKind::Local,
            rdonly: false,
        }])
        .mem_size_pairs(&pairs::DYNPTR_FROM_MEM),

        // int bpf_dynptr_read(void *dst, u32 len, const struct bpf_dynptr *src,
        //                     u32 offset, u64 flags)
        //
        // Copies `len` bytes from `src` dynptr (at `offset`) into `dst`.
        // Pair (R1,R2) bounds the dst write. Reads from any dynptr kind
        // including rdonly.
        "bpf_dynptr_read" => CallProto::with_args([
            PtrToUninitMem, // R1: dst
            ConstSize,      // R2: len
            DynptrArg { uninit: false, rdwr_only: false }, // R3: src dynptr
            Anything,       // R4: offset
            Anything,       // R5: flags
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::DYNPTR_READ),

        // int bpf_dynptr_write(const struct bpf_dynptr *dst, u32 offset,
        //                      void *src, u32 len, u64 flags)
        //
        // Copies `len` bytes from `src` into `dst` dynptr at `offset`.
        // `rdwr_only` rejects rdonly dynptrs (e.g. would-be skb/xdp
        // dynptrs). Pair (R3,R4) bounds the src read.
        "bpf_dynptr_write" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: true }, // R1: dst dynptr
            Anything,                                      // R2: offset
            PtrToMem,                                      // R3: src
            ConstSize,                                     // R4: len
            Anything,                                      // R5: flags
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::DYNPTR_WRITE),

        // void *bpf_dynptr_data(const struct bpf_dynptr *ptr, u32 offset, u32 len)
        //
        // Returns a pointer into the dynptr's backing memory bounded by
        // `len` (R3), or NULL on failure. Used for Local/Ringbuf dynptrs
        // (skb/xdp must use bpf_dynptr_slice). Caller null-checks before
        // dereferencing — RET_NULL on the proto.
        "bpf_dynptr_data" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false }, // R1: src dynptr
            Anything,  // R2: offset
            ConstSize, // R3: len (bounds the returned pointer)
            DontCare,
            DontCare,
        ])
        .ret(RetKind::PtrToAllocMemFromArg { size_arg: 2 })
        .flags(CallFlags::RET_NULL),

        // ---- skb / xdp dynptrs (W4.2f) ----
        //
        // int bpf_dynptr_from_skb(struct __sk_buff *skb, u64 flags,
        //                         struct bpf_dynptr *ptr)
        //
        // Wraps skb data as a dynptr. We force rdonly=true here:
        // matches kernel default for read-only skb program types
        // (socket filter, tracing); SCHED_CLS / SCHED_ACT wrap as
        // rdwr but require per-program-type modeling we defer.
        "bpf_dynptr_from_skb" => CallProto::with_args([
            PtrToCtx,    // R1: skb context
            Anything,    // R2: flags
            DynptrArg { uninit: true, rdwr_only: false }, // R3: &dynptr
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::DynptrInitOnArg {
            arg: 2,
            kind: DynptrKind::Skb,
            rdonly: true,
        }])
        .prog_type_allowlist(&SKB_DYNPTR_KFUNC_PROG_TYPES),

        // int bpf_dynptr_from_xdp(struct xdp_md *xdp, u64 flags,
        //                         struct bpf_dynptr *ptr)
        //
        // Wraps xdp frame data as a dynptr. Same conservative
        // rdonly=true posture as from_skb pending program-type
        // refinement.
        "bpf_dynptr_from_xdp" => CallProto::with_args([
            PtrToCtx,    // R1: xdp context
            Anything,    // R2: flags
            DynptrArg { uninit: true, rdwr_only: false }, // R3: &dynptr
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::DynptrInitOnArg {
            arg: 2,
            kind: DynptrKind::Xdp,
            rdonly: true,
        }])
        .prog_type_allowlist(&XDP_DYNPTR_KFUNC_PROG_TYPES),

        // ---- Open-coded iterators (W4.3a) ----
        //
        // `bpf_iter_*_new(&it, ...)` — Uninit→Active. The iter struct is
        // stack-allocated by the program; the side-effect zero-inits its
        // bytes and stamps a fresh iter_id. Returns 0/-errno: applier
        // sets R0 = scalar; legacy bespoke handler tightened the bound to
        // [-MAX_ERRNO, 0] which the proto applier doesn't reproduce —
        // dropping that bound is intentional (matches dynptr ctor bounds
        // and isn't load-bearing for the test corpus).
        //
        // R2..R5 vary per-kind (num: start/end/step, task/css: opaque
        // ptrs). We accept any scalar/ptr there with `Anything`; the
        // kernel does deeper checks but those don't affect our
        // soundness for the slot-state model.
        "bpf_iter_num_new" => CallProto::with_args([
            IterArg { kind: IterKind::Num, expected: IterArgExpect::Uninit },
            Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::Num }]),

        "bpf_iter_task_new" => CallProto::with_args([
            IterArg { kind: IterKind::Task, expected: IterArgExpect::Uninit },
            Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::Task }]),

        "bpf_iter_css_new" => CallProto::with_args([
            IterArg { kind: IterKind::Css, expected: IterArgExpect::Uninit },
            Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::Css }]),

        "bpf_iter_bits_new" => CallProto::with_args([
            IterArg { kind: IterKind::Bits, expected: IterArgExpect::Uninit },
            Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::Bits }]),

        // `bpf_iter_*_next(&it)` — requires Active; the dispatcher
        // forks into non-NULL (R0 = PtrToAllocMem{elem_size}, slot
        // stays Active) and NULL (R0 = 0, slot → Drained) successors.
        // Element sizes mirror the bespoke handler: num=4 (int*),
        // bits=8 (u64*), task/css=8 (placeholder pointer-width until
        // PtrToBtfId per-kind typing in a future phase).
        "bpf_iter_num_next" => CallProto::with_args([
            IterArg { kind: IterKind::Num, expected: IterArgExpect::Active },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextElem { iter_arg: 0, elem_size: 4 }),

        "bpf_iter_task_next" => CallProto::with_args([
            IterArg { kind: IterKind::Task, expected: IterArgExpect::Active },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextElem { iter_arg: 0, elem_size: 8 }),

        "bpf_iter_css_next" => CallProto::with_args([
            IterArg { kind: IterKind::Css, expected: IterArgExpect::Active },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextElem { iter_arg: 0, elem_size: 8 }),

        "bpf_iter_bits_next" => CallProto::with_args([
            IterArg { kind: IterKind::Bits, expected: IterArgExpect::Active },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextElem { iter_arg: 0, elem_size: 8 }),

        // `bpf_iter_*_destroy(&it)` — accept Active|Drained, transition
        // back to Uninit. Calling on an Uninit slot is a REJECT (mirrors
        // kernel "destroy on uninitialized").
        "bpf_iter_num_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::Num, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IterDestroyOnArg { arg: 0 }]),

        "bpf_iter_task_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::Task, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IterDestroyOnArg { arg: 0 }]),

        "bpf_iter_css_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::Css, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IterDestroyOnArg { arg: 0 }]),

        "bpf_iter_bits_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::Bits, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IterDestroyOnArg { arg: 0 }]),

        // ---- Slice cluster (W4.2g) ----
        //
        // const void *bpf_dynptr_slice(const struct bpf_dynptr *p,
        //                              u32 offset,
        //                              void *buffer, u32 buffer_size)
        //
        // Returns a pointer into the dynptr's backing memory (fast
        // path, contiguous case) or copies into the caller-provided
        // `buffer` (slow path, fragmented). May be NULL if the slice
        // straddles a non-copyable boundary. Pair (R3,R4) bounds the
        // scratch buffer; the returned pointer is bounded by `R4` —
        // RetKind::PtrToAllocMemFromArg{size_arg=3}.
        "bpf_dynptr_slice" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false }, // R1: src dynptr
            Anything,       // R2: offset
            PtrToUninitMem, // R3: scratch buffer (write target on slow path)
            ConstSize,      // R4: buffer size
            DontCare,
        ])
        .ret(RetKind::PtrToAllocMemFromArg { size_arg: 3 })
        .flags(CallFlags::RET_NULL)
        .mem_size_pairs(&pairs::DYNPTR_SLICE),

        // void *bpf_dynptr_slice_rdwr(const struct bpf_dynptr *p,
        //                             u32 offset,
        //                             void *buffer, u32 buffer_size)
        //
        // Same as `slice` but rejects rdonly dynptrs. Returns a writable
        // pointer; rdonly tracking on the *result* isn't modeled yet
        // (`PtrToAllocMem` carries no rdonly bit) — defer until a
        // real consumer needs it.
        "bpf_dynptr_slice_rdwr" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: true }, // R1: src dynptr
            Anything,       // R2: offset
            PtrToUninitMem, // R3: scratch buffer (write target on slow path)
            ConstSize,      // R4: buffer size
            DontCare,
        ])
        .ret(RetKind::PtrToAllocMemFromArg { size_arg: 3 })
        .flags(CallFlags::RET_NULL)
        .mem_size_pairs(&pairs::DYNPTR_SLICE),

        // ---- Cpumask kfuncs (W5.3 + W6.3) ----
        //
        // All cpumask kfuncs share the W6.3 prog-type allowlist
        // (`KF_PROG_TYPE_*` in the kernel): permitted in `syscall`,
        // `tracing` (fentry/fexit/tp_btf/iter), `tracepoint`, and
        // `perf_event`; rejected from `raw_tp` and other prog types
        // that lack a vmlinux BTF context. Validated by
        // `transfer_kfunc_proto` before arg checks.
        //
        // struct bpf_cpumask *bpf_cpumask_create(void)
        // KF_ACQUIRE | KF_RET_NULL — fresh refcounted cpumask, may be
        // NULL on alloc failure. Applier mints a ref_id and returns
        // PtrToCpumaskOrNull; the program must null-check before use.
        "bpf_cpumask_create" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCpumask)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // struct bpf_cpumask *bpf_cpumask_acquire(struct bpf_cpumask *p)
        // KF_ACQUIRE | KF_TRUSTED_ARGS — increments refcount on an
        // existing cpumask. Returns the same logical pointer with a
        // fresh ref_id (so the program can release each independently).
        // Not RET_NULL: the kernel guarantees acquire never fails
        // (refcount_t saturating add). R1 must be a non-null,
        // ref-tracked PtrToCpumask.
        "bpf_cpumask_acquire" => CallProto::with_args([
            PtrToCpumask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCpumask)
        .flags(CallFlags::ACQUIRE)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // void bpf_cpumask_release(struct bpf_cpumask *cpumask)
        // KF_RELEASE — drops the refcount. R1 must be a non-null,
        // ref-tracked PtrToCpumask; ReleaseRefFromArg invalidates the
        // ref_id everywhere it's still aliased.
        "bpf_cpumask_release" => CallProto::with_args([
            PtrToCpumask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }])
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // void bpf_cpumask_set_cpu(u32 cpu, struct bpf_cpumask *cpumask)
        // Mutates the cpumask. R1 = cpu (scalar), R2 = cpumask.
        "bpf_cpumask_set_cpu" => CallProto::with_args([
            Anything, PtrToCpumask, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_test_cpu(u32 cpu, const struct cpumask *cpumask)
        // Read-only query. We accept PtrToCpumask for R2 — the const
        // cpumask vs bpf_cpumask distinction isn't modeled here.
        "bpf_cpumask_test_cpu" => CallProto::with_args([
            Anything, PtrToCpumask, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // u32 bpf_cpumask_first(const struct cpumask *cpumask)
        "bpf_cpumask_first" => CallProto::with_args([
            PtrToCpumask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // ---- Cgroup kfuncs (W6.3-followon) ----
        //
        // Parallels the cpumask family: `RegType::PtrToCgroup{,OrNull}`,
        // acquire/release with ref_id tracking + null-check refinement.
        // All three kfuncs share `CGROUP_KFUNC_PROG_TYPES`.
        //
        // struct cgroup *bpf_cgroup_from_id(u64 cgrp_id)
        // KF_ACQUIRE | KF_RET_NULL — looks up a cgroup by id, returns
        // a fresh refcounted pointer or NULL if not found.
        "bpf_cgroup_from_id" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCgroup)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
        .prog_type_allowlist(&CGROUP_KFUNC_PROG_TYPES),

        // struct cgroup *bpf_cgroup_acquire(struct cgroup *cgrp)
        // KF_ACQUIRE | KF_RET_NULL | KF_TRUSTED_ARGS — increments the
        // refcount on an existing cgroup pointer. Tests in
        // verifier_kfunc_prog_types.c null-check the result, so we
        // model RET_NULL (kernel may return NULL on dying cgroups).
        "bpf_cgroup_acquire" => CallProto::with_args([
            PtrToCgroup, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCgroup)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
        .prog_type_allowlist(&CGROUP_KFUNC_PROG_TYPES),

        // void bpf_cgroup_release(struct cgroup *cgrp)
        // KF_RELEASE — drops the refcount.
        "bpf_cgroup_release" => CallProto::with_args([
            PtrToCgroup, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }])
        .prog_type_allowlist(&CGROUP_KFUNC_PROG_TYPES),

        // ---- Task kfuncs (Phase 7 wrap-up) ----
        //
        // Mirrors the cgroup family. `RegType::PtrToTask{,OrNull}`
        // tracks the optional ref_id minted by acquire-style getters.
        // Selftest corpus exercise: local_storage.c, task_local_storage.c,
        // rcu_read_lock.c, verifier_kfunc_prog_types.c, test_snprintf.c.
        //
        // struct task_struct *bpf_get_current_task_btf(void)
        // KF_TRUSTED — returns the kernel's current-task pointer. Not
        // refcounted (the kernel guarantees liveness across the helper
        // call), so no ACQUIRE flag and ret_id stays None.
        "bpf_get_current_task_btf" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToTask)
        .prog_type_allowlist(&TASK_KFUNC_PROG_TYPES),

        // struct task_struct *bpf_task_acquire(struct task_struct *p)
        // KF_ACQUIRE | KF_RET_NULL | KF_TRUSTED_ARGS — increments the
        // refcount; may return NULL on a dying task.
        "bpf_task_acquire" => CallProto::with_args([
            PtrToTask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToTask)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
        .prog_type_allowlist(&TASK_KFUNC_PROG_TYPES),

        // struct task_struct *bpf_task_from_pid(s32 pid)
        // KF_ACQUIRE | KF_RET_NULL — looks up a task by pid; returns
        // a fresh refcounted pointer or NULL.
        "bpf_task_from_pid" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToTask)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
        .prog_type_allowlist(&TASK_KFUNC_PROG_TYPES),

        // void bpf_task_release(struct task_struct *p)
        // KF_RELEASE — drops the refcount.
        "bpf_task_release" => CallProto::with_args([
            PtrToTask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }])
        .prog_type_allowlist(&TASK_KFUNC_PROG_TYPES),

        // ---- Cluster B Phase 3 (vfs_accept / nested_acquire / key) ----
        //
        // Kernel types without a dedicated `RegType::PtrTo<X>` reg-type
        // specialization (`struct file`, `struct bpf_key`,
        // `struct sk_buff` from the testmod nested-acquire kfuncs)
        // funnel through `RetKind::PtrToBtfIdNamed { type_name }`, which
        // produces a `PtrToBtfId{name, TRUSTED, ref_id}`. The ref_id
        // travels on the variant for KF_ACQUIRE callers; the matching
        // KF_RELEASE consumer recovers it via `get_ref_id()` from the
        // existing `ReleaseRefFromArg` side-effect.
        //
        // struct file *bpf_get_task_exe_file(struct task_struct *task)
        // KF_ACQUIRE | KF_RET_NULL | KF_TRUSTED_ARGS — kernel registers
        // in bpf_lsm_kfunc_set; only LSM programs may call.
        "bpf_get_task_exe_file" => CallProto::with_args([
            PtrToTask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "file" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
        .prog_type_allowlist(&LSM_ONLY_KFUNC_PROG_TYPES),

        // void bpf_put_file(struct file *file)
        // KF_RELEASE — LSM-only.
        "bpf_put_file" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }])
        .prog_type_allowlist(&LSM_ONLY_KFUNC_PROG_TYPES),

        // int bpf_path_d_path(struct path *path, char *buf, u32 sz)
        // KF_TRUSTED_ARGS — fills `buf[..sz]` with the file's path; the
        // kfunc-side `bpf_d_path` analogue. Mem-size pair (R2, R3) so
        // `validate_ptr_to_uninit_mem` enforces the buffer's bounds.
        // LSM-only (kernel `bpf_lsm_kfunc_set`).
        "bpf_path_d_path" => CallProto::with_args([
            PtrToBtfId, PtrToUninitMem, ConstSize, DontCare, DontCare,
        ])
        .mem_size_pairs(&pairs::D_PATH)
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&LSM_ONLY_KFUNC_PROG_TYPES),

        // ---- nested-acquire test kfuncs (testmod) ----
        //
        // struct sk_buff *bpf_kfunc_nested_acquire_nonzero_offset_test(struct sk_buff_head *)
        // struct sk_buff *bpf_kfunc_nested_acquire_zero_offset_test(struct sock_common *)
        //   KF_ACQUIRE only (NOT KF_RET_NULL — kernel guarantees non-null return).
        // void bpf_kfunc_nested_release_test(struct sk_buff *)
        //   KF_RELEASE.
        "bpf_kfunc_nested_acquire_nonzero_offset_test" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "sk_buff" })
        .flags(CallFlags::ACQUIRE),

        "bpf_kfunc_nested_acquire_zero_offset_test" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "sk_buff" })
        .flags(CallFlags::ACQUIRE),

        "bpf_kfunc_nested_release_test" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        // ---- key kfuncs (kernel/bpf/key.c) ----
        //
        // struct bpf_key *bpf_lookup_user_key(u32 serial, u64 flags)
        // struct bpf_key *bpf_lookup_system_key(u64 id)
        //   KF_ACQUIRE | KF_RET_NULL — caller must null-check before
        //   passing to bpf_key_put.
        // void bpf_key_put(struct bpf_key *key)
        //   KF_RELEASE — rejects PtrToBtfIdOrNull at the validator
        //   (which is how we keep the upstream
        //   "user_key_reference_without_check" / "release_with_null_key_pointer"
        //   __failure tests rejected: validate_ptr_to_btf_id only accepts
        //   the non-null variant).
        "bpf_lookup_user_key" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "bpf_key" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_lookup_system_key" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "bpf_key" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_key_put" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        // ---- Arena kfuncs (W5.5 + W6.1c + W6.1d) ----
        //
        // W6.1d realigns these protos with kernel semantics. The kernel
        // registers both as `KF_TRUSTED_ARGS | KF_SLEEPABLE` — NOT
        // KF_ACQUIRE / KF_RELEASE. Arena pages are reclaimed when the
        // map is destroyed, not per-alloc; consequently:
        //   - alloc without free is fine (W5.5's UnreleasedReference
        //     check was over-approximation).
        //   - use after free is fine — freed pages simply read as zero.
        // The `ref_id` field on `RegType::PtrToArena{,OrNull}` stays
        // (the type still tracks `mem_size` for bounds checking) but is
        // always `None` because no kfunc mints one.
        //
        // void __arena *bpf_arena_alloc_pages(void *map, void __arena *addr,
        //                                     u32 page_cnt, int node_id, u64 flags)
        // KF_RET_NULL — returns a bounded arena pointer or NULL on alloc
        // failure. R1 must be a `PtrToMapObject` whose backing map's
        // `type_ == BPF_MAP_TYPE_ARENA` (W6.1c). The addr-hint arg is
        // `Anything` — arena pointers come back from BTF as a kernel
        // type that we don't trace through the addr-cast.
        "bpf_arena_alloc_pages" => CallProto::with_args([
            ConstMapPtrOfType(crate::common::constants::BPF_MAP_TYPE_ARENA),
            Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::PtrToArenaFromArg { page_cnt_arg: 2 })
        .flags(CallFlags::RET_NULL),

        // void bpf_arena_free_pages(void *map, void __arena *ptr, u32 page_cnt)
        // No KF flags — verifier-side this is a no-op shape check. R2
        // must still be a non-null `PtrToArena` (validates the arg is
        // really an arena pointer), and R1 must be an arena map. The
        // pointer is NOT invalidated — kernel allows reads after free
        // (they return zero).
        "bpf_arena_free_pages" => CallProto::with_args([
            ConstMapPtrOfType(crate::common::constants::BPF_MAP_TYPE_ARENA),
            PtrToArena, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // ---- Owned-kptr alloc / drop / refcount (W5.4a) ----
        //
        // void *bpf_obj_new_impl(u64 local_type_id, void *meta__ign)
        // KF_ACQUIRE | KF_RET_NULL — heap-allocates a refcounted kernel
        // object of the BTF-described type. The meta pointer is compiler-
        // generated and not modeled here (Anything). Returns NULL on
        // alloc failure; program must null-check before using.
        "bpf_obj_new_impl" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToOwnedKptr)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        // void bpf_obj_drop_impl(void *kptr, void *meta__ign)
        // KF_RELEASE — drops the refcount. R1 must be a non-null,
        // ref-tracked PtrToOwnedKptr; ReleaseRefFromArg invalidates the
        // ref everywhere it's still aliased.
        "bpf_obj_drop_impl" => CallProto::with_args([
            PtrToOwnedKptr, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        // void *bpf_refcount_acquire_impl(void *kptr, void *meta__ign)
        // KF_ACQUIRE | KF_RET_NULL — bumps the refcount and returns a
        // fresh ref to the same object. The input ref stays valid (no
        // RELEASE flag); the new ref must be independently dropped or
        // pushed into a container.
        "bpf_refcount_acquire_impl" => CallProto::with_args([
            PtrToOwnedKptr, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToOwnedKptr)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        // ---- List + rbtree kfuncs (W5.4b) ----
        //
        // int bpf_list_push_front_impl(struct bpf_list_head *head,
        //                              struct bpf_list_node *node,
        //                              void *meta__ign, u64 off__ign)
        // KF_RELEASE on the node — transfers ownership into the list.
        // KF_LOCK_HELD: must be called under a spin_lock (real kernel
        // requires the lock that protects this list head; lite scope
        // accepts any held lock). R1 must point at a SpecialField{ListHead}
        // inside a map value.
        "bpf_list_push_front_impl" => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::ListHead },
            PtrToOwnedKptr,
            Anything,
            Anything,
            DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE | CallFlags::SPIN_LOCK_HELD)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 1 }]),

        // struct bpf_list_node *bpf_list_pop_front(struct bpf_list_head *head)
        // KF_ACQUIRE | KF_RET_NULL | KF_LOCK_HELD — pops a node out of
        // the list and hands ownership to the caller. NULL on empty list.
        "bpf_list_pop_front" => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::ListHead },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToOwnedKptr)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL | CallFlags::SPIN_LOCK_HELD),

        // int bpf_rbtree_add_impl(struct bpf_rb_root *root,
        //                         struct bpf_rb_node *node,
        //                         bool (*less)(struct bpf_rb_node *,
        //                                      const struct bpf_rb_node *),
        //                         void *meta__ign, u64 off__ign)
        // KF_RELEASE on the node + KF_LOCK_HELD. Lite scope: the `less`
        // callback (R3) is accepted as Anything — we don't walk into the
        // cb subprog for ordering-correctness checks. Tech-debt: future
        // precision should validate it as `PtrToCallback` and explore.
        "bpf_rbtree_add_impl" => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::RbRoot },
            PtrToOwnedKptr,
            Anything,
            Anything,
            DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE | CallFlags::SPIN_LOCK_HELD)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 1 }]),

        // ---- W6.4a-followon: kernel-exported TCP CC helpers ----
        //
        // bpf_dctcp.c and bpf_cubic.c reach into the kernel's TCP
        // congestion-control library via these ksyms. Clang emits each
        // as a `BPF_PSEUDO_KFUNC_CALL`; without protos here, our kfunc
        // dispatcher rejects with `UnsupportedModernFeature`.
        //
        // All four take a sock/tcp_sock pointer (which our struct_ops
        // entry-state plumbing types as PtrToBtfId{unknown}) plus
        // scalars; three return void, one returns u32. We model the
        // pointer args as `PtrToBtfId` (matches the trusted-pointer
        // shape) and let the verifier's permissive "unknown" type_name
        // path handle access typing.
        //
        //   void tcp_reno_cong_avoid(struct sock *sk, u32 ack, u32 acked)
        //   void tcp_slow_start    (struct tcp_sock *tp, u32 acked)
        //   void tcp_cong_avoid_ai (struct tcp_sock *tp, u32 w, u32 acked)
        //   u32  tcp_reno_undo_cwnd(struct sock *sk)
        "tcp_reno_cong_avoid" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        "tcp_slow_start" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        "tcp_cong_avoid_ai" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        "tcp_reno_undo_cwnd" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Sched_ext kfuncs (W6.4b) ----
        //
        // All gated to `ProgramKind::StructOps` — the kernel registers
        // these against the sched_ext class. Task-pointer args use
        // `PtrToBtfId` (we don't model `task_struct` field offsets);
        // dsq_id / cpu / flags args are scalars (`Anything`). The
        // *_bstr variadic-error/exit kfuncs accept any pointer for the
        // fmt/data args — the kernel does its own probe-read; over-
        // approximating to `Anything` matches our existing trace_printk
        // shape.

        // void scx_bpf_dsq_insert(struct task_struct *p, u64 dsq_id,
        //                         u64 slice, u64 enq_flags)
        "scx_bpf_dsq_insert" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // void scx_bpf_dsq_insert_vtime(struct task_struct *p, u64 dsq_id,
        //                               u64 slice, u64 vtime, u64 enq_flags)
        "scx_bpf_dsq_insert_vtime" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // s32 scx_bpf_create_dsq(u64 dsq_id, s32 node)
        "scx_bpf_create_dsq" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // void scx_bpf_destroy_dsq(u64 dsq_id)
        "scx_bpf_destroy_dsq" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // bool scx_bpf_dsq_move_to_local(u64 dsq_id)
        "scx_bpf_dsq_move_to_local" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // s32 scx_bpf_task_cpu(const struct task_struct *p)
        "scx_bpf_task_cpu" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // s32 scx_bpf_select_cpu_dfl(struct task_struct *p, s32 prev_cpu,
        //                            u64 wake_flags, bool *is_idle)
        // R4 is an output pointer; we accept any pointer (`Anything`)
        // here since the corpus passes a stack address and the kernel
        // verifier checks PTR_TO_STACK separately.
        // W6.4c: kernel gates this kfunc to `sched_ext_ops.select_cpu`
        // context only — calling it from `.enqueue` (or any other
        // member) rejects with the kfunc-context check. See
        // `selftests/sched_ext/enq_select_cpu_fails.bpf.c`.
        "scx_bpf_select_cpu_dfl" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES)
        .ops_member_allowlist(&[("sched_ext_ops", "select_cpu")]),

        // void scx_bpf_error_bstr(char *fmt, unsigned long long *data,
        //                         u32 data_len)
        // Variadic error-reporting kfunc; backs the scx_bpf_error()
        // wrapper macro. fmt/data are pointers we don't tightly type.
        "scx_bpf_error_bstr" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // void scx_bpf_exit_bstr(s64 exit_code, char *fmt,
        //                        unsigned long long *data, u32 data__sz)
        "scx_bpf_exit_bstr" => CallProto::with_args([
            Anything, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // bool scx_bpf_test_and_clear_cpu_idle(s32 cpu)
        "scx_bpf_test_and_clear_cpu_idle" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // s32 scx_bpf_pick_idle_cpu(const cpumask_t *cpus_allowed, u64 flags)
        // s32 scx_bpf_pick_any_cpu(const cpumask_t *cpus_allowed, u64 flags)
        // Cpumask args reuse W5.3 `PtrToCpumask` (the const cpumask vs
        // bpf_cpumask distinction isn't modeled — see bpf_cpumask_first).
        "scx_bpf_pick_idle_cpu" => CallProto::with_args([
            PtrToCpumask, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        "scx_bpf_pick_any_cpu" => CallProto::with_args([
            PtrToCpumask, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // const struct cpumask *scx_bpf_get_idle_cpumask(void)
        // const struct cpumask *scx_bpf_get_idle_smtmask(void)
        // KF_ACQUIRE — paired with scx_bpf_put_idle_cpumask.
        "scx_bpf_get_idle_cpumask" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCpumask)
        .flags(CallFlags::ACQUIRE)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        "scx_bpf_get_idle_smtmask" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCpumask)
        .flags(CallFlags::ACQUIRE)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // void scx_bpf_put_idle_cpumask(const struct cpumask *cpumask)
        // void scx_bpf_put_cpumask(const struct cpumask *cpumask)
        // KF_RELEASE — drops the implicit ref from a get_*_cpumask call.
        "scx_bpf_put_idle_cpumask" => CallProto::with_args([
            PtrToCpumask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }])
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        "scx_bpf_put_cpumask" => CallProto::with_args([
            PtrToCpumask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }])
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // ---- NUMA-aware variants used by numa.bpf.c ----

        // u32 scx_bpf_nr_node_ids(void)
        "scx_bpf_nr_node_ids" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // int scx_bpf_cpu_node(s32 cpu)
        "scx_bpf_cpu_node" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // const struct cpumask *scx_bpf_get_idle_cpumask_node(int node)
        "scx_bpf_get_idle_cpumask_node" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCpumask)
        .flags(CallFlags::ACQUIRE)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // s32 scx_bpf_pick_idle_cpu_node(const cpumask_t *cpus_allowed,
        //                                int node, u64 flags)
        "scx_bpf_pick_idle_cpu_node" => CallProto::with_args([
            PtrToCpumask, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // s32 scx_bpf_pick_any_cpu_node(const cpumask_t *cpus_allowed,
        //                               int node, u64 flags)
        "scx_bpf_pick_any_cpu_node" => CallProto::with_args([
            PtrToCpumask, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // ---- compat.bpf.h CO-RE aliases for older kernels ----
        //
        // The scx_bpf_dsq_insert(), scx_bpf_dsq_move_to_local() etc.
        // macros expand to a `bpf_ksym_exists(modern) ? modern(...) :
        // legacy___compat(...)` ternary. Both kfunc names are emitted
        // as relocs at compile time; libbpf picks one at load time.
        // For our purposes we accept both with the same proto.

        "scx_bpf_dispatch___compat" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        "scx_bpf_dispatch_vtime___compat" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        "scx_bpf_consume___compat" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&SCHED_EXT_KFUNC_PROG_TYPES),

        // ---- bpf_testmod struct_ops kfuncs ----
        // int bpf_kfunc_st_ops_inc10(struct st_ops_args *args)
        // Trivial test kfunc invoked from struct_ops prologue/epilogue
        // tests (`pro_epilogue.c`, `pro_epilogue_with_kfunc.c`). The
        // single arg is a kernel-typed pointer (PtrToBtfId / NULL); we
        // accept Anything since the test bodies don't read through the
        // returned scalar.
        "bpf_kfunc_st_ops_inc10" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // void *bpf_cast_to_kern_ctx(void *obj)
        // Reinterpret a uapi BPF ctx pointer as the corresponding kernel
        // type (e.g. __sk_buff -> sk_buff). Test bodies just call it and
        // either ignore the return or store/load through the same alias;
        // returning Scalar (no precise pointer typing yet) is sufficient
        // to clear the dispatch-time rejection.
        "bpf_cast_to_kern_ctx" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        _ => return None,
    })
}

// Static mem-size-pair arrays referenced inline by helper / kfunc protos
// (W4.2d: was helper-id-keyed via the now-deleted `get_mem_size_pairs`;
// pairs now ride on `CallProto::mem_size_pairs` so the same machinery
// serves both helpers and kfuncs).
//
// BPF_RINGBUF_OUTPUT is intentionally absent — the kernel allows
// reading uninitialized stack data in privileged mode; restoring this
// pair needs privileged/unprivileged-mode support.
pub(super) mod pairs {
    use super::{MemSizePair, Reg};
    pub static PROBE_READ: [MemSizePair; 1] = [MemSizePair::new_nullable(Reg::R1, Reg::R2)];
    pub static SKB_LOAD_BYTES: [MemSizePair; 1] = [MemSizePair::new(Reg::R3, Reg::R4)];
    pub static SKB_STORE_BYTES: [MemSizePair; 1] = [MemSizePair::new(Reg::R3, Reg::R4)];
    pub static SKB_GET_TUNNEL_KEY: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];
    pub static SKB_SET_TUNNEL_KEY: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];
    pub static CSUM_DIFF: [MemSizePair; 2] = [
        MemSizePair::new_nullable(Reg::R1, Reg::R2),
        MemSizePair::new_nullable(Reg::R3, Reg::R4),
    ];
    pub static SK_LOOKUP_TCP: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];
    pub static SK_LOOKUP_UDP: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];
    pub static GET_SOCKOPT: [MemSizePair; 1] = [MemSizePair::new(Reg::R4, Reg::R5)];
    pub static GET_TASK_STACK: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];
    pub static D_PATH: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];
    pub static SNPRINTF: [MemSizePair; 2] = [
        MemSizePair::new_nullable(Reg::R1, Reg::R2),
        MemSizePair::new_nullable(Reg::R4, Reg::R5),
    ];
    pub static STRNCMP: [MemSizePair; 1] = [MemSizePair::new(Reg::R1, Reg::R2)];
    pub static GET_STACK: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];
    pub static PERF_EVENT_OUTPUT: [MemSizePair; 1] = [MemSizePair::new(Reg::R4, Reg::R5)];
    pub static GET_CURRENT_COMM: [MemSizePair; 1] = [MemSizePair::new(Reg::R1, Reg::R2)];
    pub static PERF_EVENT_READ_VALUE: [MemSizePair; 1] = [MemSizePair::new(Reg::R3, Reg::R4)];
    pub static PERF_PROG_READ_VALUE: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];

    // ---- Local-cluster dynptr kfuncs (W4.2e) ----
    pub static DYNPTR_FROM_MEM: [MemSizePair; 1] = [MemSizePair::new(Reg::R1, Reg::R2)];
    pub static DYNPTR_READ: [MemSizePair; 1] = [MemSizePair::new(Reg::R1, Reg::R2)];
    pub static DYNPTR_WRITE: [MemSizePair; 1] = [MemSizePair::new(Reg::R3, Reg::R4)];

    // ---- Slice cluster (W4.2g) ----
    pub static DYNPTR_SLICE: [MemSizePair; 1] = [MemSizePair::new(Reg::R3, Reg::R4)];
}

/// W7.2: returns true if the helper is in the kernel's `is_fastcall_helper_call`
/// set. Fastcall helpers preserve R1..R5 across the call edge — the verifier
/// skips the caller-saved clobber so clang-emitted no-spill sequences type-check.
/// List mirrors `kernel/bpf/verifier.c::is_fastcall_helper_call` as of v6.13.
pub(crate) fn is_fastcall_helper(helper: u32) -> bool {
    matches!(
        helper,
        constants::BPF_KTIME_GET_NS
            | constants::BPF_GET_SMP_PROCESSOR_ID
            | constants::BPF_GET_CURRENT_PID_TGID
            | constants::BPF_GET_CURRENT_UID_GID
            | constants::BPF_GET_CURRENT_COMM
            | constants::BPF_GET_CURRENT_TASK
            | constants::BPF_GET_NUMA_NODE_ID
            | constants::BPF_GET_CURRENT_CGROUP_ID
            | constants::BPF_JIFFIES64
            | constants::BPF_KTIME_GET_BOOT_NS
            | constants::BPF_KTIME_GET_COARSE_NS
    )
}

/// Returns true if the helper rejects packet pointers for the given argument index.
pub(crate) fn helper_rejects_packet_for_arg(helper: u32, arg_index: usize) -> bool {
    match helper {
        // bpf_skb_store_bytes: R3 (from buffer) cannot be packet pointer
        // because the helper modifies packet data, causing pointer invalidation
        constants::BPF_SKB_STORE_BYTES => arg_index == 2,

        // Add other helpers with similar restrictions here
        _ => false,
    }
}

/// For helpers with PTR_OR_NULL args, returns the index of the paired size argument.
pub(crate) fn get_nullable_ptr_size_pair(helper: u32, ptr_arg_index: usize) -> Option<usize> {
    match helper {
        // bpf_csum_diff: R1=from (PTR_OR_NULL) paired with R2=from_size,
        //                R3=to (PTR_OR_NULL) paired with R4=to_size
        constants::BPF_CSUM_DIFF => match ptr_arg_index {
            0 => Some(1), // R1's size is R2
            2 => Some(3), // R3's size is R4
            _ => None,
        },
        // Add other helpers with PTR_OR_NULL + SIZE_OR_ZERO pairs
        _ => None,
    }
}
