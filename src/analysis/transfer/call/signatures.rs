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
use crate::analysis::machine::stack_state::{DynptrKind, IrqKfuncClass, IterKind};
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
    /// Pointer to a const, NUL-terminated string in a read-only map
    /// value (`.rodata`). Mirrors kernel `ARG_PTR_TO_CONST_STR`
    /// (`verifier.c::check_reg_const_str`, v6.15 ~L9405): rejects
    /// `PtrToMapValue` whose map is NOT `BPF_F_RDONLY_PROG`. Used by
    /// `bpf_snprintf`'s fmt arg.
    PtrToConstStr,

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
    /// `PtrToBtfId` whose `type_name` must equal the given kernel
    /// struct name. Stricter than `PtrToBtfId` (which accepts any
    /// named BTF pointer): used by kfuncs that demand a specific
    /// struct (`bpf_path_d_path` requires `struct path *` — kernel
    /// rejects `struct file *` interior pointers like
    /// `&file->f_task_work` cast to `(struct path *)`). The new
    /// per-field BTF arithmetic in `update_ptr_arithmetic_type`
    /// produces correctly-typed interior pointers so this name
    /// match becomes meaningful.
    PtrToBtfIdNamed { type_name: &'static str },

    // ---- Stack ----
    PtrToStack,

    // ---- Nullable variants ----
    PtrToCtxOrNull,
    PtrToMemOrNull,
    /// Writable buffer or NULL. Mirrors kernel
    /// `ARG_PTR_TO_MEM | PTR_MAYBE_NULL` for write helpers like
    /// `bpf_snprintf` (buf may be NULL when paired size = 0,
    /// switching the helper into "compute formatted length only" mode).
    PtrToUninitMemOrNull,
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

    // ---- IRQ flag ----
    /// `unsigned long *` on the stack pointing at an 8-byte slot used
    /// to hold an IRQ flag. `uninit = true` is the constructor (the
    /// slot must have NO IRQ_FLAG annotation, NO iter/dynptr annotation,
    /// and not carry an outstanding ref). `uninit = false` is the
    /// destructor (slot must carry an IRQ_FLAG annotation whose
    /// `kfunc_class` matches and whose `id` equals `active_irq_id`).
    IrqFlagArg { uninit: bool, kfunc_class: IrqKfuncClass },

    /// `bpf_res_spin_lock{,_irqsave}` / `_unlock{,_irqrestore}` arg.
    /// Mirrors kernel `KF_ARG_PTR_TO_RES_SPIN_LOCK` (verifier.c v6.15
    /// L13347): R must be `PtrToMapValue` or `PtrToOwnedKptr`; the
    /// reg's `var_off + reg.off` must equal the BTF-recorded
    /// `res_spin_lock` field offset of the pointee record (L8310);
    /// the map/struct must carry a `bpf_res_spin_lock` field (L8305).
    /// `is_irq` distinguishes the irqsave variant — used at the
    /// acquire/release transfer to flag the entry's `is_irq` field
    /// for the LIFO-match check.
    ResSpinLockArg { is_irq: bool },

    // ---- Cpumask (W5.3) ----
    /// `struct bpf_cpumask *` argument — mutating consumers only
    /// (`bpf_cpumask_set_cpu`, `_clear_cpu`, `_clear`, `_copy`,
    /// `_release`, …). Strict: only the acquire-tracked
    /// `RegType::PtrToCpumask` is accepted, so the program must have
    /// passed an actual `bpf_cpumask` allocated via
    /// `bpf_cpumask_create` / acquired via `bpf_cpumask_acquire`.
    /// `(struct bpf_cpumask *)task->cpus_ptr` casts (read-only kernel
    /// `cpumask`) are rejected here — kernel error
    /// "Can't set the CPU of a non-struct bpf_cpumask".
    PtrToCpumask,
    /// `const struct cpumask *` argument — read-only consumers
    /// (`bpf_cpumask_test_cpu`, `_first`, `_first_zero`, `_full`,
    /// `_empty`, `_equal`, `_intersects`, `_subset`, `_weight`, …).
    /// Accepts `PtrToCpumask` (the bpf_cpumask wrapper is also a
    /// const cpumask) AND `PtrToBtfId{type_name in {"cpumask",
    /// "bpf_cpumask"}, TRUSTED}` produced by the BTF field-load
    /// typing path (`task->cpus_ptr`, `&task->cpus_mask`).
    PtrToCpumaskRead,

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
pub struct CallFlags(u32);

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
    /// Pre-call: enters a preempt-disabled region by incrementing
    /// `state.active_preempt_locks`. Mirrors kernel `bpf_preempt_disable`
    /// kfunc (verifier.c v6.15 ~L13569).
    pub const PREEMPT_DISABLE: Self = Self(1 << 13);
    /// Pre-call: exits a preempt-disabled region. Rejects if the count
    /// is already zero (unmatched enable). Mirrors kernel
    /// `bpf_preempt_enable` kfunc (verifier.c v6.15 ~L13571).
    pub const PREEMPT_ENABLE: Self = Self(1 << 14);
    /// Pre-call: this helper/kfunc may sleep. Rejected when
    /// `state.in_preempt_disabled()`. Mirrors kernel `fn->might_sleep`
    /// (verifier.c v6.15 ~L11299) and `KF_SLEEPABLE` for kfuncs (~L13565).
    pub const MIGHT_SLEEP: Self = Self(1 << 15);
    /// Post-call: this `RELEASE`-flagged kfunc converts the released
    /// argument's owning ref into a non-owning ref instead of fully
    /// invalidating it. Mirrors kernel `verifier.c` v6.15
    /// `ref_convert_owning_non_owning` (L12471), driven by the
    /// `KF_RELEASE` flag on graph-add kfuncs (`bpf_rbtree_add_impl`,
    /// `bpf_list_push_{front,back}_impl`). Without this, the original
    /// alloc-pointer becomes Scalar after add and a follow-up
    /// `bpf_refcount_acquire(n)` (under the same lock) fails its arg
    /// type check.
    pub const RELEASE_NON_OWN: Self = Self(1 << 16);
    /// Pre-call: this kfunc disables IRQs and stamps `arg #0`'s stack
    /// slot as an IRQ flag. Pushes a fresh id on `acquired_irq_ids`.
    /// Drives the `IrqSaveOnArg` side effect.
    pub const IRQ_SAVE: Self = Self(1 << 17);
    /// Pre-call: this kfunc restores IRQ state from `arg #0`'s slot.
    /// Rejects unless the slot's id matches `active_irq_id` (LIFO).
    /// Drives the `IrqRestoreFromArg` side effect.
    pub const IRQ_RESTORE: Self = Self(1 << 18);
    /// Pre-call: `bpf_res_spin_lock` family acquire. The transfer
    /// function forks the state at the call insn (kernel `push_stack`,
    /// verifier.c v6.15 L13455-13479): success branch with R0=0 and
    /// the lock pushed on `acquired_res_locks`; failure branch with R0
    /// constrained to negative (no lock pushed). AA-deadlock check fires
    /// before push.
    pub const RES_SPIN_LOCK_ACQUIRE: Self = Self(1 << 19);
    /// Pre-call: `bpf_res_spin_unlock` family. Validates LIFO match on
    /// `acquired_res_locks` (kernel L8369-8376) — emits "different
    /// lock" / "out of order" errors as appropriate.
    pub const RES_SPIN_LOCK_RELEASE: Self = Self(1 << 20);

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
    /// Typed `_next` return: same fork shape as `IterNextElem` but R0
    /// on the non-NULL successor is `PtrToBtfId { type_name, flags,
    /// ref_id: None }` instead of generic `PtrToAllocMem`. Used by
    /// `bpf_iter_task_vma_next` (TRUSTED `vm_area_struct *`) and
    /// `bpf_iter_task_next` (RCU `task_struct *`). The matching
    /// consumer kfunc's flag enforcement (`KF_TRUSTED_ARGS` /
    /// `KF_RCU`) inspects `PtrFlags` to accept or reject — that's
    /// what keeps `iter_next_rcu_not_trusted`'s call to
    /// `bpf_kfunc_trusted_task_test` rejected (RCU isn't TRUSTED).
    IterNextBtfId {
        iter_arg: u8,
        type_name: &'static str,
        flags: crate::analysis::machine::reg_types::PtrFlags,
    },
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
    /// Stamp an IRQ-flag annotation on the 8-byte stack slot pointed to
    /// by `arg`. Validator must already have rejected non-uninit slots
    /// (kernel `is_irq_flag_reg_valid_uninit` ~L1243). The applier
    /// mints a fresh id via `state.irq_save()`. Drives
    /// `bpf_local_irq_save` and `bpf_res_spin_lock_irqsave`.
    IrqSaveOnArg { arg: u8, kfunc_class: IrqKfuncClass },
    /// Clear the IRQ-flag annotation on the slot pointed to by `arg`.
    /// Validator must already have checked the slot has an IRQ_FLAG of
    /// matching kfunc_class and that its id == active_irq_id (LIFO);
    /// the applier pops the LIFO entry. Drives `bpf_local_irq_restore`
    /// and `bpf_res_spin_unlock_irqrestore`.
    IrqRestoreFromArg { arg: u8, kfunc_class: IrqKfuncClass },
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
    /// If true, NULL ptr skips the size check entirely. Mirrors the
    /// kernel's `is_kfunc_arg_optional` (the `__opt` suffix) — when the
    /// pointer is NULL, no buffer access happens, so any size is fine.
    /// Used by `bpf_dynptr_slice`/`_rdwr` whose `buffer__opt` is the
    /// scratch-buffer for the slow copy path.
    pub null_skips_size_check: bool,
}

impl MemSizePair {
    pub(crate) const fn new(ptr_reg: Reg, size_reg: Reg) -> Self {
        Self {
            ptr_reg,
            size_reg,
            allow_zero: false,
            null_skips_size_check: false,
        }
    }

    pub(crate) const fn new_nullable(ptr_reg: Reg, size_reg: Reg) -> Self {
        Self {
            ptr_reg,
            size_reg,
            allow_zero: true,
            null_skips_size_check: false,
        }
    }

    pub(crate) const fn new_optional(ptr_reg: Reg, size_reg: Reg) -> Self {
        Self {
            ptr_reg,
            size_reg,
            allow_zero: false,
            null_skips_size_check: true,
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

        // bpf_map_lookup_percpu_elem(map, key, cpu) — same shape as
        // map_lookup_elem with an extra cpu scalar arg. Returns a
        // pointer to the per-cpu copy of the value, or NULL.
        // R0 typing handled by `update_call_types` (PtrToMapValueOrNull
        // keyed off R1's map).
        constants::BPF_MAP_LOOKUP_PERCPU_ELEM => CallProto::with_args([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            Anything,    // R3: cpu
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
            // Kernel registers 4 per-prog-type protos for this helper
            // (skb-ctx / sock / sock_addr-ctx / sock_common-btf-id).
            // We use PtrToCtx for the validator entry point; the
            // sock-shaped variants are admitted via a per-helper
            // relaxation in `validate_ptr_to_ctx` (keyed on
            // `ctx.helper == BPF_GET_SOCKET_COOKIE`) so that ctx-offset
            // validation still fires for skb-ctx programs.
            PtrToCtx, // R1: ctx / sock / btf_id sock_common
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
        ])
        .flags(CallFlags::MIGHT_SLEEP),

        // bpf_copy_from_user_task(void *dst, u32 size, const void __user
        // *src, struct task_struct *task, u64 flags) — sleepable variant
        // that reads from another task's address space. Required as a
        // *helper* proto (helper id 191) so the MIGHT_SLEEP gate fires
        // when called inside an RCU read region — closes
        // rcu_read_lock::inproper_sleepable_helper. R4 uses bare
        // `PtrToBtfId` (any BTF id) rather than `PtrToBtfIdNamed{"task_struct"}`
        // because kernel selftests pass `task_struct___local`-typed
        // subprog args via `__arg_trusted` (libbpf rewrites the FUNC
        // proto to a local struct alias for CO-RE compatibility);
        // strict-name matching breaks `verifier_global_ptr_args::flavor_ptr_*`.
        constants::BPF_COPY_FROM_USER_TASK => CallProto::with_args([
            PtrToUninitMem, // R1: dst
            ConstSize,      // R2: size
            Anything,       // R3: user_ptr
            PtrToBtfId,     // R4: task (any BTF id; libbpf alias-tolerant)
            Anything,       // R5: flags
        ])
        .mem_size_pairs(&pairs::COPY_FROM_USER_STR)
        .flags(CallFlags::MIGHT_SLEEP),

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

        // bpf_cgrp_storage_get(map, cgroup, value, flags)
        // R0 typing handled by `update_call_types` (PtrToMapValueOrNull
        // keyed off R1's map). Arg-side: R2 must be a `cgroup` PtrToBtfId
        // — the typical bug (cgrp_ls_negative.c::on_enter) is passing a
        // task_struct cast as cgroup; PtrToBtfIdNamed catches the type
        // mismatch.
        constants::BPF_CGRP_STORAGE_GET => CallProto::with_args([
            ConstMapPtr,                                  // R1: map
            PtrToBtfIdNamed { type_name: "cgroup" },      // R2: cgroup
            PtrToMapValueOrNull,                          // R3: value
            Anything,                                     // R4: flags
            DontCare,
        ]),

        constants::BPF_CGRP_STORAGE_DELETE => CallProto::with_args([
            ConstMapPtr,                                  // R1: map
            PtrToBtfIdNamed { type_name: "cgroup" },      // R2: cgroup
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
            PtrToUninitMemOrNull, // R1: buf (NULL OK with size=0; "compute length only")
            ConstSizeOrZero,      // R2: sz
            PtrToConstStr,        // R3: fmt — must be const string in rodata map
            PtrToMemOrNull,  // R4: data (u64 array; may be NULL if data_len=0)
            ConstSizeOrZero, // R5: data_len
        ])
        .mem_size_pairs(&pairs::SNPRINTF)
        .ret(RetKind::Scalar),

        // ---- W7.1: bpf_strncmp ----
        // (s1: PtrToMem, s1_sz: ConstSize, s2: PtrToConstStr) -> s32
        // Kernel rejects writable / non-NUL-terminated comparands via
        // ARG_PTR_TO_CONST_STR (validate_ptr_to_const_str enforces
        // BPF_F_RDONLY_PROG + NUL-within-rodata-bounds). Closes
        // strncmp_bad_writable_target and strncmp_bad_not_null_term_target.
        constants::BPF_STRNCMP => CallProto::with_args([
            PtrToMem,       // R1: s1
            ConstSize,      // R2: s1_sz
            PtrToConstStr,  // R3: s2 (rodata, NUL-terminated)
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

/// Cgroup kfunc family allowlist. Mirrors the kernel's cgroup_kfunc_set
/// registration: tracing/tracepoint/perf_event/syscall/struct_ops (the
/// cpumask base) **plus LSM** — kernel registers the cgroup kfunc id_set
/// against BPF_PROG_TYPE_LSM (selftests like
/// iters_css_task::iter_css_task_for_each + test_task_under_cgroup::lsm_run
/// rely on LSM hooks calling bpf_cgroup_from_id/_acquire). Broken out
/// from the cpumask alias so the LSM addition doesn't bleed into cpumask
/// (cpumask kfuncs are not registered for LSM upstream).
const CGROUP_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 6] = [
    crate::ast::ProgramKind::Syscall,
    crate::ast::ProgramKind::Tracing,
    crate::ast::ProgramKind::Tracepoint,
    crate::ast::ProgramKind::PerfEvent,
    crate::ast::ProgramKind::StructOps,
    crate::ast::ProgramKind::Lsm,
];

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
/// program types that receive a skb-shaped context — sched_cls/act
/// (tc), socket_filter, cgroup_skb, lwt_*, sk_skb, sock_ops, sk_msg,
/// flow_dissector, netfilter, and Tracing (tp_btf hooks like
/// `kfree_skb`/`consume_skb` whose first arg is `struct sk_buff *`).
const SKB_DYNPTR_KFUNC_PROG_TYPES: [crate::ast::ProgramKind; 13] = [
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
    // Netfilter passes `struct sk_buff *` via `bpf_nf_ctx.skb`;
    // upstream `verifier_netfilter_ctx::with_valid_ctx_access_test6`
    // is `__success` calling `bpf_dynptr_from_skb` from a netfilter
    // hook.
    crate::ast::ProgramKind::Netfilter,
    // tp_btf hooks like `kfree_skb`/`consume_skb` receive
    // `struct sk_buff *` as their first arg; kernel allows
    // bpf_dynptr_from_skb here. dynptr_success::test_dynptr_skb_tp_btf
    // exercises this combination.
    crate::ast::ProgramKind::Tracing,
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
        // Preempt-region kfuncs (kernel verifier.c v6.15 ~L13560).
        // No args; PREEMPT_DISABLE / PREEMPT_ENABLE drive the
        // `active_preempt_locks` state machine in `apply_pre_call_lock_flags`.
        "bpf_preempt_disable" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::PREEMPT_DISABLE),

        "bpf_preempt_enable" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::PREEMPT_ENABLE),

        // IRQ-region kfuncs (kernel verifier.c v6.15 ~L1184).
        //
        // void bpf_local_irq_save(unsigned long *flags)
        // void bpf_local_irq_restore(unsigned long *flags)
        //
        // The validator (`IrqFlagArg`) enforces stack-pointer arg shape +
        // uninit/init slot state + LIFO ordering; the side-effect handler
        // mints the id, stamps the slot, and pushes/pops `acquired_irq_ids`.
        "bpf_local_irq_save" => CallProto::with_args([
            IrqFlagArg { uninit: true, kfunc_class: IrqKfuncClass::Native },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IrqSaveOnArg {
            arg: 0,
            kfunc_class: IrqKfuncClass::Native,
        }]),

        "bpf_local_irq_restore" => CallProto::with_args([
            IrqFlagArg { uninit: false, kfunc_class: IrqKfuncClass::Native },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IrqRestoreFromArg {
            arg: 0,
            kfunc_class: IrqKfuncClass::Native,
        }]),

        // ---- bpf_res_spin_lock (resilient queued spin lock, kernel
        // verifier.c v6.15 L8271+ `process_spin_lock` is_res_lock arm
        // and L13455 push_stack state-fork). Returns int (0 = acquired,
        // negative = failed-to-acquire); the call-site transfer forks
        // the state into success (R0=0, lock pushed) and failure
        // (R0 ∈ [-MAX_ERRNO, -1], no lock pushed) branches.
        "bpf_res_spin_lock" => CallProto::with_args([
            ResSpinLockArg { is_irq: false },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RES_SPIN_LOCK_ACQUIRE),

        "bpf_res_spin_unlock" => CallProto::with_args([
            ResSpinLockArg { is_irq: false },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RES_SPIN_LOCK_RELEASE),

        // _irqsave variant: arg #1 is also an IRQ-flag stack pointer
        // (uninit at acquire, popped at restore). Combines the
        // res-lock state-fork with the IRQ-flag stamp; class is
        // `IrqKfuncClass::Lock` so a `bpf_local_irq_restore`
        // (Native class) cannot release this flag and vice-versa
        // (kernel "irq flag acquired by … kfuncs cannot be restored …").
        "bpf_res_spin_lock_irqsave" => CallProto::with_args([
            ResSpinLockArg { is_irq: true },
            IrqFlagArg { uninit: true, kfunc_class: IrqKfuncClass::Lock },
            DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::RES_SPIN_LOCK_ACQUIRE)
        .side_effects(&[SideEffect::IrqSaveOnArg {
            arg: 1,
            kfunc_class: IrqKfuncClass::Lock,
        }]),

        "bpf_res_spin_unlock_irqrestore" => CallProto::with_args([
            ResSpinLockArg { is_irq: true },
            IrqFlagArg { uninit: false, kfunc_class: IrqKfuncClass::Lock },
            DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RES_SPIN_LOCK_RELEASE)
        .side_effects(&[SideEffect::IrqRestoreFromArg {
            arg: 1,
            kfunc_class: IrqKfuncClass::Lock,
        }]),

        // RCU read-side kfuncs (kernel `verifier.c` v6.15: registered
        // in `common_btf_ids` as `KF_RCU_PROTECTS_ALLOC`/no-arg). The
        // `BPF_PSEUDO_KFUNC_CALL` form is what `__ksym extern void
        // bpf_rcu_read_lock(void);` resolves to in refcounted_kptr.c.
        // Reuse the same RCU_READ_LOCK / _UNLOCK depth-counter
        // machinery used by the helper-form (transfer.rs ~L1226).
        "bpf_rcu_read_lock" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RCU_READ_LOCK),

        "bpf_rcu_read_unlock" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RCU_READ_UNLOCK),

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
            PtrToUninitMem,   // R1: dst
            ConstSizeOrZero,  // R2: len (0 accepted; runtime returns 0)
            DynptrArg { uninit: false, rdwr_only: false }, // R3: src dynptr
            Anything,         // R4: offset
            Anything,         // R5: flags
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::DYNPTR_READ),

        // int bpf_dynptr_write(const struct bpf_dynptr *dst, u32 offset,
        //                      void *src, u32 len, u64 flags)
        //
        // Copies `len` bytes from `src` into `dst` dynptr at `offset`.
        // Kernel doesn't enforce rdwr at verify time (no `__rdwr` on the
        // kfunc) — runtime returns -EINVAL when dst is rdonly. Tests
        // like test_skb_readonly / test_dynptr_skb_tp_btf rely on the
        // verifier accepting the call statically and then asserting on
        // the runtime errno.
        "bpf_dynptr_write" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false }, // R1: dst dynptr
            Anything,                                      // R2: offset
            PtrToMem,                                      // R3: src
            ConstSizeOrZero,                               // R4: len (0 accepted)
            Anything,                                      // R5: flags
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::DYNPTR_WRITE),

        // ---- XDP metadata kfuncs (NIC-driven RX metadata getters) ----
        //
        // All three take an XDP context plus output ptr(s). Used by
        // xdp_metadata.c, xdp_metadata2.c (freplace), xdp_hw_metadata.c.
        // Output buffer size is implicit in the C type; modeled as
        // PtrToUninitMem (writable mem of any size).

        "bpf_xdp_metadata_rx_timestamp" => CallProto::with_args([
            PtrToCtx, PtrToUninitMem, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&XDP_DYNPTR_KFUNC_PROG_TYPES),

        "bpf_xdp_metadata_rx_hash" => CallProto::with_args([
            PtrToCtx, PtrToUninitMem, PtrToUninitMem, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&XDP_DYNPTR_KFUNC_PROG_TYPES),

        "bpf_xdp_metadata_rx_vlan_tag" => CallProto::with_args([
            PtrToCtx, PtrToUninitMem, PtrToUninitMem, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&XDP_DYNPTR_KFUNC_PROG_TYPES),

        // int bpf_dynptr_clone(const struct bpf_dynptr *ptr,
        //                      struct bpf_dynptr *clone__init)
        //
        // Initializes `clone__init` as a fresh dynptr. Kernel propagates
        // source kind + rdonly onto the clone; we stamp DynptrKind::Local
        // with rdonly=false because we don't track parent-to-clone
        // invalidation lineage or propagate Xdp/Skb source kind. Those
        // are REAL coverage gaps that surface as FAs on
        // dynptr_fail::clone_invalidate1 + clone_xdp_packet_data —
        // suppressing the kfunc to mask them would be dishonest about
        // the verifier's coverage. Keep registered; surface the FAs.
        "bpf_dynptr_clone" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false },
            DynptrArg { uninit: true, rdwr_only: false },
            DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::DynptrInitOnArg {
            arg: 1,
            kind: DynptrKind::Local,
            rdonly: false,
        }]),

        // int bpf_dynptr_copy(struct bpf_dynptr *dst, u32 dst_off,
        //                     const struct bpf_dynptr *src, u32 src_off,
        //                     u32 len)
        //
        // Copies `len` bytes from src+src_off to dst+dst_off. Both dynptrs
        // must be initialized; dst must be writable (rdwr_only). Returns
        // 0 on success, negative errno on bounds/dst-rdonly. Used in
        // dynptr_success.c::test_dynptr_copy.
        "bpf_dynptr_copy" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: true },  // R1: dst (RW)
            Anything,                                       // R2: dst_off
            DynptrArg { uninit: false, rdwr_only: false }, // R3: src (any)
            Anything,                                       // R4: src_off
            Anything,                                       // R5: len
        ])
        .ret(RetKind::Scalar),

        // int bpf_dynptr_adjust(const struct bpf_dynptr *ptr,
        //                        u32 start, u32 end)
        //
        // Trims the dynptr's view to [start, end). Read-only on the
        // dynptr (mutates internal offset/size, not the buffer), so any
        // initialized dynptr (including rdonly) is acceptable. The
        // `__failure` sibling (`dynptr_fail::dynptr_adjust_invalid`)
        // passes `{}` — our `DynptrArg{uninit:false}` rejects it.
        "bpf_dynptr_adjust" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false }, // R1: ptr
            Anything, // R2: start
            Anything, // R3: end
            DontCare,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // bool bpf_dynptr_is_null(const struct bpf_dynptr *ptr)
        "bpf_dynptr_is_null" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // bool bpf_dynptr_is_rdonly(const struct bpf_dynptr *ptr)
        "bpf_dynptr_is_rdonly" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // __u32 bpf_dynptr_size(const struct bpf_dynptr *ptr)
        "bpf_dynptr_size" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // bpf_dynptr_clone deliberately NOT registered. Two `__failure`
        // siblings in `dynptr_fail.c` rely on kernel-only rejection
        // mechanisms we don't model:
        //   - `clone_invalidate1`: kernel propagates parent invalidation
        //     to all clones (after `bpf_ringbuf_submit_dynptr(&ptr)`,
        //     reads through the clone fail). We don't track parent/clone
        //     lineage on dynptr slots.
        //   - `clone_xdp_packet_data`: kernel propagates source `Xdp`
        //     kind onto the clone, so subsequent `bpf_xdp_adjust_head`
        //     invalidates the clone's slice. We'd default the clone to
        //     `Local` and miss the invalidation cascade.
        // Registering the proto without these mechanisms unmasks both as
        // PASS → FALSE_ACCEPT. Closing `test_dynptr_clone` (1 FR) isn't
        // worth opening 2 FAs; revisit when clone-lineage is modeled.

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
        // Wraps xdp frame data as a dynptr. XDP programs CAN mutate
        // packet data, so the dynptr is read-write — matches kernel
        // (no DYNPTR_RDONLY_BIT set in `bpf_dynptr_init` for XDP type).
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
            rdonly: false,
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

        // bpf_iter_task_new: kernel takes an RCU read lock for the
        // iter's lifetime so KF_RCU consumers (`bpf_kfunc_rcu_task_test`)
        // called between _new and _destroy don't need an explicit
        // `bpf_rcu_read_lock()`. Modeled here as RCU_READ_LOCK on
        // _new + RCU_READ_UNLOCK on _destroy. Closes the
        // `iters_testmod.c::iter_next_rcu` sequence.
        // bpf_iter_task_new is KF_RCU_PROTECTED in the kernel: it does
        // NOT take an RCU read lock itself (was a prior modeling
        // mistake); it only reads in_rcu_cs at call-time and stamps the
        // iter slot with MEM_RCU (trusted) or PTR_UNTRUSTED accordingly
        // (verifier.c v6.15 `mark_stack_slots_iter` ~L1041). Slot-trust
        // logic lives in the IterInitOnArg side-effect handler — it
        // calls `state.in_rcu_read_section()` and sets
        // `IteratorSlot.untrusted` for `IterKind::Task`/`Css`. Subsequent
        // `_next` calls reject on UNTRUSTED. Programs that rely on the
        // implicit kernel-held RCU CS (non-sleepable kprobe/raw_tp/etc.)
        // get `rcu_read_depth = 1` at entry from `analysis::mod`.
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

        // `bpf_iter_*_next(&it)` — accepts Active or Drained; the
        // dispatcher forks Active into non-NULL (R0 = PtrToAllocMem{elem_size},
        // slot stays Active) and NULL (R0 = 0, slot → Drained), and on
        // Drained input collapses to the NULL-only successor (kernel
        // semantics: a drained iterator just keeps returning NULL).
        // Without `ActiveOrDrained`, programs that call `_next` after a
        // post-loop unrolled iteration (iters.c::iter_pragma_unroll_loop)
        // FR'd because the static unroll re-enters _next on the Drained
        // slot a second time.
        // Element sizes mirror the bespoke handler: num=4 (int*),
        // bits=8 (u64*), task/css=8 (placeholder pointer-width until
        // PtrToBtfId per-kind typing in a future phase).
        "bpf_iter_num_next" => CallProto::with_args([
            IterArg { kind: IterKind::Num, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextElem { iter_arg: 0, elem_size: 4 }),

        "bpf_iter_task_next" => CallProto::with_args([
            IterArg { kind: IterKind::Task, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        // Returns `struct task_struct *`. Kernel verifies tasks held
        // across an iter as RCU-protected (the iter holds an RCU
        // read lock for its lifetime); KF_RCU consumers
        // (`bpf_kfunc_rcu_task_test`) accept, KF_TRUSTED_ARGS
        // consumers (`bpf_kfunc_trusted_task_test`) reject. Closes
        // `iter_next_rcu` while keeping `iter_next_rcu_not_trusted`
        // rejected via the new flag enforcement.
        .ret(RetKind::IterNextBtfId {
            iter_arg: 0,
            type_name: "task_struct",
            flags: crate::analysis::machine::reg_types::PtrFlags::RCU,
        }),

        // ---- bpf_iter_task_vma_* (Phase C iters_testmod.c) ----
        // 8-byte opaque iter struct (kernel-internal state lives in
        // bpf_iter_task_vma_kern). Returns `struct vm_area_struct *`
        // marked TRUSTED — the kernel iter holds the task's mmap
        // semaphore for the iter's lifetime, so the vma is
        // safe-to-deref. KF_TRUSTED_ARGS consumers
        // (`bpf_kfunc_trusted_vma_test`) accept.
        "bpf_iter_task_vma_new" => CallProto::with_args([
            IterArg { kind: IterKind::TaskVma, expected: IterArgExpect::Uninit },
            Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::TaskVma }]),

        "bpf_iter_task_vma_next" => CallProto::with_args([
            IterArg { kind: IterKind::TaskVma, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextBtfId {
            iter_arg: 0,
            type_name: "vm_area_struct",
            flags: crate::analysis::machine::reg_types::PtrFlags::TRUSTED,
        }),

        "bpf_iter_task_vma_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::TaskVma, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IterDestroyOnArg { arg: 0 }]),

        // ---- bpf_iter_kmem_cache_* (kmem_cache_iter.c) ----
        // 8-byte opaque iter struct. `_next` returns `struct kmem_cache *`
        // marked TRUSTED — the kernel iter holds the slab_mutex while
        // walking the slab cache list, so the returned cache is
        // safe-to-deref via BTF field loads (s->name, s->size).
        "bpf_iter_kmem_cache_new" => CallProto::with_args([
            IterArg { kind: IterKind::KmemCache, expected: IterArgExpect::Uninit },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::KmemCache }]),

        "bpf_iter_kmem_cache_next" => CallProto::with_args([
            IterArg { kind: IterKind::KmemCache, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextBtfId {
            iter_arg: 0,
            type_name: "kmem_cache",
            flags: crate::analysis::machine::reg_types::PtrFlags::TRUSTED,
        }),

        "bpf_iter_kmem_cache_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::KmemCache, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IterDestroyOnArg { arg: 0 }]),

        // ---- testmod consumer kfuncs (Phase C iters_testmod.c) ----
        //
        // The kernel registers these in `bpf_testmod_kfunc_set` to
        // exercise the kfunc-arg trust-band enforcement:
        //   - bpf_kfunc_trusted_vma_test  : KF_TRUSTED_ARGS, takes
        //     `struct vm_area_struct *` — accepts only TRUSTED.
        //   - bpf_kfunc_trusted_task_test : KF_TRUSTED_ARGS, takes
        //     `struct task_struct *`     — rejects RCU-flagged
        //     (catches `iter_next_rcu_not_trusted`).
        //   - bpf_kfunc_trusted_num_test  : KF_TRUSTED_ARGS, takes
        //     `int *`                    — rejects PtrToAllocMem
        //     (catches `iter_next_ptr_mem_not_trusted`).
        //   - bpf_kfunc_rcu_task_test     : KF_RCU, takes
        //     `struct task_struct *`     — accepts TRUSTED or RCU
        //     (closes `iter_next_rcu`).
        "bpf_kfunc_trusted_vma_test" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "vm_area_struct" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::TRUSTED_ARGS),

        "bpf_kfunc_trusted_task_test" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "task_struct" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::TRUSTED_ARGS),

        "bpf_kfunc_trusted_num_test" => CallProto::with_args([
            // Kernel signature is `int *ptr`. We don't have a
            // dedicated typed-int-pointer ArgKind; PtrToBtfId is the
            // closest non-anything kind, and the trust-band gate
            // rejects PtrToAllocMem (the only thing
            // `bpf_iter_num_next` can return) before the
            // PtrToBtfId-shape check would even fire.
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::TRUSTED_ARGS),

        "bpf_kfunc_rcu_task_test" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "task_struct" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RCU),

        "bpf_iter_css_next" => CallProto::with_args([
            IterArg { kind: IterKind::Css, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextElem { iter_arg: 0, elem_size: 8 }),

        "bpf_iter_bits_next" => CallProto::with_args([
            IterArg { kind: IterKind::Bits, expected: IterArgExpect::ActiveOrDrained },
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

        // No RCU_READ_UNLOCK side effect — iter_task_new doesn't take a
        // CS in our updated model (see comment there).
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

        // ---- bpf_iter_css_task_* (iters_css_task.c) ----
        // int bpf_iter_css_task_new(struct bpf_iter_css_task *it,
        //                           struct cgroup_subsys_state *css,
        //                           unsigned int flags)
        // KF_ITER_NEW | KF_TRUSTED_ARGS in the kernel (NOT KF_RCU_PROTECTED).
        // Allowlist-restricted to LSM / iter / sleepable programs
        // (`check_css_task_iter_allowlist`); the iter holds its own
        // `css_task_iter` lock so its slot trust does not depend on
        // in_rcu_cs at init time. `_next` returns `struct task_struct *`
        // (RCU-flagged); KF_RCU consumers accept, KF_TRUSTED_ARGS reject.
        "bpf_iter_css_task_new" => CallProto::with_args([
            IterArg { kind: IterKind::CssTask, expected: IterArgExpect::Uninit },
            Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::CssTask }]),

        "bpf_iter_css_task_next" => CallProto::with_args([
            IterArg { kind: IterKind::CssTask, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextBtfId {
            iter_arg: 0,
            type_name: "task_struct",
            flags: crate::analysis::machine::reg_types::PtrFlags::RCU,
        }),

        "bpf_iter_css_task_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::CssTask, expected: IterArgExpect::ActiveOrDrained },
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

        // ---- testmod_seq iterator family (Phase 3 cluster B) ----
        //
        // testmod-defined open-coded iterator. The kernel registers all
        // four kfuncs in `bpf_testmod_check_kfunc_call`:
        //   - _new   : KF_ITER_NEW
        //   - _next  : KF_ITER_NEXT | KF_RET_NULL
        //   - _destroy: KF_ITER_DESTROY
        //   - _value : reads the iter's stored value; the `it__iter`
        //     param suffix tells the kernel "this is an initialized iter
        //     reference" — accept Active *or* Drained, reject Uninit.
        //     Selftest `testmod_seq_getter_after_bad` covers the post-
        //     destroy case (Uninit → reject); _value's expected =
        //     ActiveOrDrained is what catches both bad calls.
        //
        // int bpf_iter_testmod_seq_new(struct bpf_iter_testmod_seq *it, s64 value, int cnt)
        "bpf_iter_testmod_seq_new" => CallProto::with_args([
            IterArg { kind: IterKind::TestmodSeq, expected: IterArgExpect::Uninit },
            Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .side_effects(&[SideEffect::IterInitOnArg { arg: 0, kind: IterKind::TestmodSeq }]),

        // s64 *bpf_iter_testmod_seq_next(struct bpf_iter_testmod_seq *it)
        "bpf_iter_testmod_seq_next" => CallProto::with_args([
            IterArg { kind: IterKind::TestmodSeq, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::IterNextElem { iter_arg: 0, elem_size: 8 }),

        // void bpf_iter_testmod_seq_destroy(struct bpf_iter_testmod_seq *it)
        "bpf_iter_testmod_seq_destroy" => CallProto::with_args([
            IterArg { kind: IterKind::TestmodSeq, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .side_effects(&[SideEffect::IterDestroyOnArg { arg: 0 }]),

        // s64 bpf_iter_testmod_seq_value(int val, struct bpf_iter_testmod_seq *it__iter)
        // The `__iter` suffix forces the kernel to treat arg #2 (R2 here)
        // as an initialized iter — Active or Drained, never Uninit.
        // Doesn't transition the slot's state.
        "bpf_iter_testmod_seq_value" => CallProto::with_args([
            Anything,
            IterArg { kind: IterKind::TestmodSeq, expected: IterArgExpect::ActiveOrDrained },
            DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

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
            Anything,             // R2: offset
            PtrToUninitMemOrNull, // R3: scratch buffer (NULL OK — `buffer__opt`)
            ConstSize,            // R4: buffer size
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
            Anything,             // R2: offset
            PtrToUninitMemOrNull, // R3: scratch buffer (NULL OK — `buffer__opt`)
            ConstSize,            // R4: buffer size
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
        // Read-only query — `PtrToCpumaskRead` accepts both the
        // bpf_cpumask wrapper (PtrToCpumask) and BTF-typed reads
        // (`task->cpus_ptr`).
        "bpf_cpumask_test_cpu" => CallProto::with_args([
            Anything, PtrToCpumaskRead, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // u32 bpf_cpumask_first(const struct cpumask *cpumask)
        "bpf_cpumask_first" => CallProto::with_args([
            PtrToCpumaskRead, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // u32 bpf_cpumask_first_zero(const struct cpumask *cpumask)
        // Same shape as `bpf_cpumask_first`, returns first unset cpu.
        // KF_RCU consumer.
        "bpf_cpumask_first_zero" => CallProto::with_args([
            PtrToCpumaskRead, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // u32 bpf_cpumask_first_and(const struct cpumask *src1,
        //                           const struct cpumask *src2)
        "bpf_cpumask_first_and" => CallProto::with_args([
            PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // u32 bpf_cpumask_weight(const struct cpumask *cpumask)
        "bpf_cpumask_weight" => CallProto::with_args([
            PtrToCpumaskRead, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // u32 bpf_cpumask_any_distribute(const struct cpumask *src)
        "bpf_cpumask_any_distribute" => CallProto::with_args([
            PtrToCpumaskRead, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // u32 bpf_cpumask_any_and_distribute(const struct cpumask *src1,
        //                                    const struct cpumask *src2)
        "bpf_cpumask_any_and_distribute" => CallProto::with_args([
            PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // ---- Read-only predicates (return bool) ----

        // bool bpf_cpumask_equal(const struct cpumask *src1, const struct cpumask *src2)
        "bpf_cpumask_equal" => CallProto::with_args([
            PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_intersects(const struct cpumask *src1, const struct cpumask *src2)
        "bpf_cpumask_intersects" => CallProto::with_args([
            PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_subset(const struct cpumask *src1, const struct cpumask *src2)
        "bpf_cpumask_subset" => CallProto::with_args([
            PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_empty(const struct cpumask *cpumask)
        "bpf_cpumask_empty" => CallProto::with_args([
            PtrToCpumaskRead, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_full(const struct cpumask *cpumask)
        "bpf_cpumask_full" => CallProto::with_args([
            PtrToCpumaskRead, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::FASTCALL)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // ---- Mutators that modify their first arg (PtrToCpumask) ----

        // void bpf_cpumask_clear_cpu(u32 cpu, struct bpf_cpumask *cpumask)
        "bpf_cpumask_clear_cpu" => CallProto::with_args([
            Anything, PtrToCpumask, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_test_and_set_cpu(u32 cpu, struct bpf_cpumask *cpumask)
        "bpf_cpumask_test_and_set_cpu" => CallProto::with_args([
            Anything, PtrToCpumask, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_test_and_clear_cpu(u32 cpu, struct bpf_cpumask *cpumask)
        "bpf_cpumask_test_and_clear_cpu" => CallProto::with_args([
            Anything, PtrToCpumask, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // void bpf_cpumask_setall(struct bpf_cpumask *cpumask)
        "bpf_cpumask_setall" => CallProto::with_args([
            PtrToCpumask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // void bpf_cpumask_clear(struct bpf_cpumask *cpumask)
        "bpf_cpumask_clear" => CallProto::with_args([
            PtrToCpumask, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // bool bpf_cpumask_and(struct bpf_cpumask *dst,
        //                      const struct cpumask *src1,
        //                      const struct cpumask *src2)
        "bpf_cpumask_and" => CallProto::with_args([
            PtrToCpumask, PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // void bpf_cpumask_or(struct bpf_cpumask *dst,
        //                     const struct cpumask *src1,
        //                     const struct cpumask *src2)
        "bpf_cpumask_or" => CallProto::with_args([
            PtrToCpumask, PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // void bpf_cpumask_xor(struct bpf_cpumask *dst,
        //                      const struct cpumask *src1,
        //                      const struct cpumask *src2)
        "bpf_cpumask_xor" => CallProto::with_args([
            PtrToCpumask, PtrToCpumaskRead, PtrToCpumaskRead, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // void bpf_cpumask_copy(struct bpf_cpumask *dst, const struct cpumask *src)
        "bpf_cpumask_copy" => CallProto::with_args([
            PtrToCpumask, PtrToCpumaskRead, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CPUMASK_KFUNC_PROG_TYPES),

        // int bpf_cpumask_populate(struct cpumask *cpumask,
        //                          void *src, size_t src__sz)
        // R2/R3 form a mem+size pair — kernel rejects "leads to invalid
        // memory access" when sz exceeds the source buffer (matches
        // cpumask_failure::test_populate_invalid_source's __failure
        // expectation). Destination expects writable cpumask wrapper.
        "bpf_cpumask_populate" => CallProto::with_args([
            PtrToCpumask, PtrToMem, ConstSize, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::CPUMASK_POPULATE)
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

        // struct cgroup *bpf_cgroup_ancestor(struct cgroup *cgrp, int level)
        // KF_ACQUIRE | KF_RCU | KF_RET_NULL — returns the ancestor at
        // the given level (or NULL) with a refcount the caller must
        // release.
        "bpf_cgroup_ancestor" => CallProto::with_args([
            PtrToCgroup, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCgroup)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
        .prog_type_allowlist(&CGROUP_KFUNC_PROG_TYPES),

        // void cgroup_rstat_updated(struct cgroup *cgrp, int cpu)
        // void cgroup_rstat_flush(struct cgroup *cgrp)
        // Plain cgroup-arg kfuncs registered as kernel symbols
        // (declared `__ksym` in selftests/cgroup_hierarchical_stats.c).
        // No flags — they neither acquire nor release; just take a
        // trusted cgroup pointer and either schedule a flush or run one.
        "cgroup_rstat_updated" => CallProto::with_args([
            PtrToCgroup, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CGROUP_KFUNC_PROG_TYPES),

        "cgroup_rstat_flush" => CallProto::with_args([
            PtrToCgroup, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .prog_type_allowlist(&CGROUP_KFUNC_PROG_TYPES),

        // struct cgroup *bpf_task_get_cgroup1(struct task_struct *task,
        //                                    int hierarchy_id)
        // KF_ACQUIRE | KF_RCU | KF_RET_NULL — looks up the v1 cgroup
        // the task is attached to in the named hierarchy. Used by the
        // bpf_cgrp_storage_* callers in cgrp_ls_*.c (recursion, tp_btf,
        // sleepable) and by test_cgroup1_hierarchy::lsm_*_run.
        "bpf_task_get_cgroup1" => CallProto::with_args([
            PtrToTask, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToCgroup)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL)
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

        // bpf_task_from_vpid: namespace-aware variant of from_pid. Same
        // signature shape (s32 vpid → struct task_struct *, ACQUIRE +
        // RET_NULL). Used by task_kfunc_success.c.
        "bpf_task_from_vpid" => CallProto::with_args([
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
        // LSM-only (kernel `bpf_lsm_kfunc_set`). R1 is strict-named
        // `struct path *` — the cluster B residual FA
        // (path_d_path_kfunc_type_mismatch) passes
        // `(struct path *)&file->f_task_work` whose corrected type
        // after the new BTF field-arithmetic is `callback_head`,
        // not `path`. PtrToBtfIdNamed catches the mismatch.
        "bpf_path_d_path" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "path" },
            PtrToUninitMem, ConstSize, DontCare, DontCare,
        ])
        .mem_size_pairs(&pairs::D_PATH)
        .ret(RetKind::Scalar)
        // KF_TRUSTED_ARGS — kernel rejects an untrusted `struct path *`
        // (e.g. one walked from `task->fs->root` outside an RCU CS).
        // Closes verifier_vfs_reject::path_d_path_kfunc_untrusted_*.
        .flags(CallFlags::TRUSTED_ARGS)
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
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL | CallFlags::MIGHT_SLEEP),

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
        // Kernel commit 7793fc3d (v6.13) dropped KF_RET_NULL from
        // bpf_refcount_acquire_impl: the input ref already guarantees
        // refcount > 0, so the bumped result cannot be NULL. Programs
        // ≥ v6.13 (incl. refcounted_kptr.c) skip the null check.
        "bpf_refcount_acquire_impl" => CallProto::with_args([
            PtrToOwnedKptr, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToOwnedKptr)
        .flags(CallFlags::ACQUIRE),

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
        .flags(CallFlags::RELEASE | CallFlags::RELEASE_NON_OWN | CallFlags::SPIN_LOCK_HELD)
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

        // bpf_list_push_back_impl / bpf_list_pop_back — symmetric
        // back-of-list variants. Same ownership / lock contracts as
        // their _front counterparts above.
        "bpf_list_push_back_impl" => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::ListHead },
            PtrToOwnedKptr,
            Anything,
            Anything,
            DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE | CallFlags::RELEASE_NON_OWN | CallFlags::SPIN_LOCK_HELD)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 1 }]),

        "bpf_list_pop_back" => CallProto::with_args([
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
        // struct bpf_rb_node *bpf_rbtree_first(struct bpf_rb_root *root)
        // KF_RET_NULL | KF_LOCK_HELD — peek at the leftmost node.
        // Return is a *non-owning* ref (no KF_ACQUIRE); the caller may
        // dereference it under the lock but cannot drop it. We model
        // the result as a `PtrToOwnedKptr` without `ref_id` (so any
        // attempt to release it is rejected by the
        // `ReleaseRefFromArg` precondition gate which demands a
        // present `ref_id`). After bpf_spin_unlock, non-owning refs
        // are invalidated by `state.invalidate_non_owning_refs()`.
        "bpf_rbtree_first" => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::RbRoot },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToOwnedKptr)
        .flags(CallFlags::RET_NULL | CallFlags::SPIN_LOCK_HELD),

        // struct bpf_rb_node *bpf_rbtree_remove(struct bpf_rb_root *root,
        //                                       struct bpf_rb_node *node)
        // KF_ACQUIRE | KF_RET_NULL | KF_LOCK_HELD — pull `node` out of
        // the tree, hand the caller a fresh owning ref. The `node`
        // arg must be a non-owning rb_node ref already in the tree
        // (kernel rejects "rbtree_remove node input must be
        // non-owning ref"); lite scope accepts any `PtrToOwnedKptr`.
        "bpf_rbtree_remove" => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::RbRoot },
            PtrToOwnedKptr,
            DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToOwnedKptr)
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL | CallFlags::SPIN_LOCK_HELD),

        "bpf_rbtree_add_impl" => CallProto::with_args([
            MapValueSpecial { kind: SpecialFieldKind::RbRoot },
            PtrToOwnedKptr,
            Anything,
            Anything,
            DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE | CallFlags::RELEASE_NON_OWN | CallFlags::SPIN_LOCK_HELD)
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

        // ---- TCP CC algorithm ksyms (BBR / DCTCP / CUBIC) ----
        //
        // tcp_ca_kfunc.c and bpf_cc_cubic.c reach into the kernel's
        // bbr / dctcp / cubictcp implementations via __ksym externs.
        // Same shape as the tcp_reno_* family above: each takes a
        // sock pointer (typed PtrToBtfId by struct_ops entry-state
        // plumbing) plus scalars; void or u32 return. Pure additive
        // registration — no acquire/release, no allowlist.
        //
        //   void bbr_init(struct sock *sk)
        //   void bbr_main(struct sock *sk, u32 ack, int flag,
        //                 const struct rate_sample *rs)
        //   u32  bbr_sndbuf_expand(struct sock *sk)
        //   u32  bbr_undo_cwnd(struct sock *sk)
        //   void bbr_cwnd_event(struct sock *sk, enum tcp_ca_event event)
        //   u32  bbr_ssthresh(struct sock *sk)
        //   u32  bbr_min_tso_segs(struct sock *sk)
        //   void bbr_set_state(struct sock *sk, u8 new_state)
        "bbr_init" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bbr_main" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Void),
        "bbr_sndbuf_expand" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bbr_undo_cwnd" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bbr_cwnd_event" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bbr_ssthresh" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bbr_min_tso_segs" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bbr_set_state" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        //   void dctcp_init(struct sock *sk)
        //   void dctcp_update_alpha(struct sock *sk, u32 flags)
        //   void dctcp_cwnd_event(struct sock *sk, enum tcp_ca_event ev)
        //   u32  dctcp_ssthresh(struct sock *sk)
        //   u32  dctcp_cwnd_undo(struct sock *sk)
        //   void dctcp_state(struct sock *sk, u8 new_state)
        "dctcp_init" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "dctcp_update_alpha" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "dctcp_cwnd_event" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "dctcp_ssthresh" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "dctcp_cwnd_undo" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "dctcp_state" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        //   void cubictcp_init(struct sock *sk)
        //   u32  cubictcp_recalc_ssthresh(struct sock *sk)
        //   void cubictcp_cong_avoid(struct sock *sk, u32 ack, u32 acked)
        //   void cubictcp_state(struct sock *sk, u8 new_state)
        //   void cubictcp_cwnd_event(struct sock *sk, enum tcp_ca_event event)
        //   void cubictcp_acked(struct sock *sk, const struct ack_sample *sample)
        "cubictcp_init" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "cubictcp_recalc_ssthresh" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "cubictcp_cong_avoid" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "cubictcp_state" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "cubictcp_cwnd_event" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "cubictcp_acked" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // ---- testmod sock-addr-syscall kfuncs (sock_addr_kern.c) ----
        //
        // Test kfuncs registered by bpf_testmod for the
        // sock_addr/syscall integration coverage. All called from
        // SEC("syscall") programs with a pointer to a per-test args
        // struct (`init_sock_args` / `addr_args` / `sendmsg_args`)
        // sitting on the syscall caller's input buffer; void or int
        // return. Pure additive — no acquire/release.
        //
        //   int  bpf_kfunc_init_sock(struct init_sock_args *args)
        //   void bpf_kfunc_close_sock(void)
        //   int  bpf_kfunc_call_kernel_connect(struct addr_args *args)
        //   int  bpf_kfunc_call_kernel_bind(struct addr_args *args)
        //   int  bpf_kfunc_call_kernel_listen(void)
        //   int  bpf_kfunc_call_kernel_sendmsg(struct sendmsg_args *args)
        //   int  bpf_kfunc_call_sock_sendmsg(struct sendmsg_args *args)
        //   int  bpf_kfunc_call_kernel_getsockname(struct addr_args *args)
        //   int  bpf_kfunc_call_kernel_getpeername(struct addr_args *args)
        "bpf_kfunc_init_sock" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_close_sock" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bpf_kfunc_call_kernel_connect" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_kernel_bind" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_kernel_listen" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_kernel_sendmsg" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_sock_sendmsg" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_kernel_getsockname" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_kernel_getpeername" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- testmod ref-tracked kfuncs (kfunc_call_test.c, map_kptr.c,
        //      jit_probe_mem.c, local_kptr_stash.c) ----
        //
        // struct prog_test_ref_kfunc *bpf_kfunc_call_test_acquire(unsigned long *)
        //   KF_ACQUIRE | KF_RET_NULL — mints a fresh refcounted pointer.
        // void bpf_kfunc_call_test_release(struct prog_test_ref_kfunc *p)
        //   KF_RELEASE — drops the ref minted by _acquire.
        // void bpf_kfunc_call_test_ref(struct prog_test_ref_kfunc *p)
        //   No flags — non-acquire/release passthrough; just validates a
        //   trusted ref arg.
        //
        // Returning PtrToBtfIdNamed{prog_test_ref_kfunc} keeps the matching
        // __failure siblings rejecting via the existing trusted-arg /
        // ref-id machinery. The bounded-mem-returning siblings
        // (bpf_kfunc_call_test_get_rdonly_mem / _get_rdwr_mem) are NOT
        // registered: they would need PtrToAllocMemFromArg + rdonly
        // tracking + ref-id propagation onto the returned mem to keep
        // the matching __failure tests in kfunc_call_fail.c rejecting.
        "bpf_kfunc_call_test_acquire" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "prog_test_ref_kfunc" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_kfunc_call_test_release" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "prog_test_ref_kfunc" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        "bpf_kfunc_call_test_ref" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "prog_test_ref_kfunc" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // int *bpf_kfunc_call_test_get_rdwr_mem(struct prog_test_ref_kfunc *p,
        //                                       const int rdwr_buf_size)
        // int *bpf_kfunc_call_test_get_rdonly_mem(struct prog_test_ref_kfunc *p,
        //                                         const int rdonly_buf_size)
        // KF_RET_NULL on both. Returns a bounded mem region whose size
        // is the value of R2 (a `const int`). Lite scope: model both with
        // `RetKind::PtrToAllocMemFromArg { size_arg: 1 }` — no rdonly /
        // ref-id-on-mem distinction. The matching `kfunc_call_fail.c`
        // siblings (rdonly-store, use-after-free, oob, non-const-size)
        // are upstream-ACCEPT in the v6.15 baseline (skel `?tc`-gated),
        // so the absent rdonly enforcement and ref-id propagation don't
        // surface FAs.
        "bpf_kfunc_call_test_get_rdwr_mem" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "prog_test_ref_kfunc" },
            Anything,
            DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToAllocMemFromArg { size_arg: 1 })
        .flags(CallFlags::RET_NULL),

        "bpf_kfunc_call_test_get_rdonly_mem" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "prog_test_ref_kfunc" },
            Anything,
            DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToAllocMemFromArg { size_arg: 1 })
        .flags(CallFlags::RET_NULL),

        // struct bpf_testmod_ctx *bpf_testmod_ctx_create(int *err)
        //   KF_ACQUIRE | KF_RET_NULL.
        // void bpf_testmod_ctx_release(struct bpf_testmod_ctx *ctx)
        //   KF_RELEASE.
        "bpf_testmod_ctx_create" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "bpf_testmod_ctx" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_testmod_ctx_release" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "bpf_testmod_ctx" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        // ---- testmod basic test kfuncs (kfunc_call_test.c) ----
        //
        // Scalar-only and pointer helpers (companion to the ref-tracked
        // family above).
        //
        // bpf_kfunc_call_test_pass_ctx takes `struct __sk_buff *skb`
        // — modeled as PtrToCtx so the matching __failure sibling
        // `kfunc_call_test_pointer_arg_type_mismatch` (passes literal
        // `(void *)10`) keeps rejecting. The mem_len_* kfuncs take a
        // (mem, len) pair — wired up via MemSizePair so the
        // out-of-bounds `kfunc_syscall_test_fail` sibling rejects on
        // size validation.
        //
        //   __u64 bpf_kfunc_call_test1(struct sock *sk, u32, u64, u32, u64)
        //   int   bpf_kfunc_call_test2(struct sock *sk, u32, u32)
        //   long  bpf_kfunc_call_test4(s8, s16, int, long)
        //   void  bpf_kfunc_call_test_pass_ctx(struct __sk_buff *skb)
        //   void  bpf_kfunc_call_test_pass1(struct prog_test_pass1 *p)
        //   void  bpf_kfunc_call_test_pass2(struct prog_test_pass2 *p)
        //   void  bpf_kfunc_call_test_mem_len_pass1(void *mem, int len)
        //   void  bpf_kfunc_call_test_mem_len_fail2(__u64 *mem, int len)
        //   u32   bpf_kfunc_call_test_static_unused_arg(u32 arg, u32 unused)
        "bpf_kfunc_call_test1" => CallProto::with_args([
            Anything, Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::Scalar),
        // struct sock *bpf_kfunc_call_test3(struct sock *sk) — passthrough
        // (returns the same sock). No KF_ACQUIRE / KF_RET_NULL flags;
        // caller dereferences the returned sock directly without a null
        // check (`bpf_kfunc_call_test3(sk)->__sk_common.skc_state`).
        "bpf_kfunc_call_test3" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "sock" }),
        "bpf_kfunc_call_test2" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_test4" => CallProto::with_args([
            Anything, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_call_test_pass_ctx" => CallProto::with_args([
            PtrToCtx, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bpf_kfunc_call_test_pass1" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bpf_kfunc_call_test_pass2" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bpf_kfunc_call_test_mem_len_pass1" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bpf_kfunc_call_test_mem_len_fail2" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bpf_kfunc_call_test_static_unused_arg" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_kfunc_common_test (testmod, no-op trace anchor) ----
        // `void bpf_kfunc_common_test(void)`. Registered from
        // bpf_testmod_kfunc.h; used by missed_kprobe.c, missed_kprobe_recursion.c,
        // and the wq.c sleepable callback variants as a trace-anchor target
        // (test driver puts a kprobe on this function to count invocations).
        // Trivially additive: no args, no side effects.
        "bpf_kfunc_common_test" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // ---- bpf_kfunc_call_test_destructive (testmod) ----
        // `void bpf_kfunc_call_test_destructive(void)` — KF_DESTRUCTIVE
        // (CAP_SYS_BOOT-gated runtime check; verifier just needs the
        // proto). Used by kfunc_call_destructive.c.
        "bpf_kfunc_call_test_destructive" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // ---- bpf_testmod_ops3_call_test_{1,2} (testmod struct_ops3) ----
        // `void bpf_testmod_ops3_call_test_N(void)` — used by struct_ops
        // private-stack tests (struct_ops_private_stack.c,
        // struct_ops_private_stack_recur.c) to thunk into ops3 vtable
        // methods. No args, no side effects.
        "bpf_testmod_ops3_call_test_1" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        "bpf_testmod_ops3_call_test_2" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // ---- bpf_xdp_flow_lookup (nf_flow_table xdp helper) ----
        // `struct flow_offload_tuple_rhash *bpf_xdp_flow_lookup(
        //      struct xdp_md *, struct bpf_fib_lookup *,
        //      struct bpf_flowtable_opts___local *, u32)`
        // — used by xdp_flowtable.c. Caller only null-checks the
        // returned pointer; Scalar return matches the same pattern as
        // bpf_get_kmem_cache.
        "bpf_xdp_flow_lookup" => CallProto::with_args([
            PtrToCtx, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_map_sum_elem_count (map introspection) ----
        // `__s64 bpf_map_sum_elem_count(const struct bpf_map *map)` —
        // sums per-cpu counters; runtime helper used by
        // map_percpu_stats.c (iter/bpf_map: ctx->map yields
        // PtrToBtfId{bpf_map}, not ConstMapPtr) and map_ptr_kern.c
        // (subprog arg). Anything matches the kernel acceptance of
        // either &literal_map or a typed bpf_map* from iter ctx; the
        // kernel runtime gates the call by BTF type-id check.
        "bpf_map_sum_elem_count" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- testmod struct_ops prologue/epilogue test kfuncs ----
        // Used by pro_epilogue.c, pro_epilogue_goto_start.c,
        // epilogue_exit.c (`syscall_*` SEC programs that thunk into
        // the struct_ops test infrastructure). Each takes
        // `struct st_ops_args *args` and returns int.
        //
        //   int bpf_kfunc_st_ops_test_prologue(struct st_ops_args *)
        //   int bpf_kfunc_st_ops_test_epilogue(struct st_ops_args *)
        //   int bpf_kfunc_st_ops_test_pro_epilogue(struct st_ops_args *)
        "bpf_kfunc_st_ops_test_prologue" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_st_ops_test_epilogue" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_kfunc_st_ops_test_pro_epilogue" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- testmod cross-module ordering test kfuncs ----
        // kfunc_module_order.c: two kfuncs registered from different
        // modules to exercise cross-module dispatch. No args.
        //
        //   int bpf_test_modorder_retx(void)  // returns 'x'
        //   int bpf_test_modorder_rety(void)  // returns 'y'
        "bpf_test_modorder_retx" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_test_modorder_rety" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_send_signal_task ----
        // test_send_signal_kern.c: targeted signal-delivery kfunc.
        //   int bpf_send_signal_task(struct task_struct *task,
        //                            int sig, enum pid_type type,
        //                            u64 value)
        // task arg is Anything to accept the PtrToTask result of
        // bpf_task_from_pid (and any other future task-pointer reg
        // type) without re-implementing per-arg trust gates.
        "bpf_send_signal_task" => CallProto::with_args([
            Anything, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- kprobe/uprobe session kfuncs ----
        // bpf_session_cookie() returns `__u64 *` — a pointer to an
        // 8-byte per-call stash slot the program reads/writes via
        // *cookie. Modeled with PtrToAllocMem{mem_size=8} so the
        // verifier accepts the 8-byte deref pattern. (Programs may
        // load OR store through the returned pointer.)
        // bpf_session_is_return() returns a 0/1 flag for return-probe
        // disambiguation. Used in kprobe_multi_session_cookie.c,
        // uprobe_multi_session_cookie.c, uprobe_multi_session.c.
        "bpf_session_cookie" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToAllocMem { mem_size: 8 }),
        "bpf_session_is_return" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- testmod nullable-dynptr arg test ----
        // bpf_kfunc_dynptr_test(struct bpf_dynptr *, struct bpf_dynptr *__nullable)
        // Used by test_kfunc_param_nullable.c. Both args are dynptrs;
        // the second is nullable. Modeled with DynptrArg consumers
        // (initialized, rdwr or rdonly) so the existing dynptr arg
        // validator handles slot-state checks. The nullable second
        // arg uses Anything to accept literal NULL plus init dynptrs.
        "bpf_kfunc_dynptr_test" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false },
            Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // ---- LSM xattr kfuncs ----
        // Used by test_get_xattr.c, test_set_remove_xattr.c (lsm.s/*
        // SEC). Each takes a kernel object pointer + name string +
        // optional value dynptr and returns int. Args are Anything
        // since the file/dentry pointers come from BPF_PROG entry
        // typing as PtrToBtfId{file/dentry} which we don't strictly
        // gate.
        //
        //   int bpf_get_file_xattr(struct file *, const char *,
        //                          struct bpf_dynptr *value)
        //   int bpf_get_dentry_xattr(struct dentry *, const char *,
        //                            struct bpf_dynptr *value)
        //   int bpf_set_dentry_xattr(struct dentry *, const char *,
        //                            struct bpf_dynptr *value, int flags)
        //   int bpf_remove_dentry_xattr(struct dentry *, const char *)
        "bpf_get_file_xattr" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_get_dentry_xattr" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_set_dentry_xattr" => CallProto::with_args([
            Anything, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_remove_dentry_xattr" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        // Locked variants (test_set_remove_xattr.c additionally
        // exercises these; kernel registers them separately).
        "bpf_set_dentry_xattr_locked" => CallProto::with_args([
            Anything, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_remove_dentry_xattr_locked" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- FOU/GUE tunnel encap kfuncs (test_tunnel_kern.c) ----
        //   int bpf_skb_set_fou_encap(struct __sk_buff *, struct bpf_fou_encap *, int)
        //   int bpf_skb_get_fou_encap(struct __sk_buff *, struct bpf_fou_encap *)
        "bpf_skb_set_fou_encap" => CallProto::with_args([
            PtrToCtx, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_skb_get_fou_encap" => CallProto::with_args([
            PtrToCtx, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Crypto kfuncs (crypto_basic.c, crypto_bench.c, crypto_sanity.c) ----
        //
        // struct bpf_crypto_ctx *bpf_crypto_ctx_create(const struct bpf_crypto_params *,
        //                                              u32 params__sz, int *err)
        //   KF_ACQUIRE | KF_RET_NULL | KF_SLEEPABLE.
        // struct bpf_crypto_ctx *bpf_crypto_ctx_acquire(struct bpf_crypto_ctx *ctx)
        //   KF_ACQUIRE | KF_RET_NULL.
        // void bpf_crypto_ctx_release(struct bpf_crypto_ctx *ctx)
        //   KF_RELEASE.
        // int bpf_crypto_encrypt/_decrypt(struct bpf_crypto_ctx *ctx,
        //                                  const struct bpf_dynptr *src,
        //                                  const struct bpf_dynptr *dst,
        //                                  const struct bpf_dynptr *iv)
        //   No flags; the iv arg is __nullable.
        "bpf_crypto_ctx_create" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "bpf_crypto_ctx" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL | CallFlags::MIGHT_SLEEP),

        "bpf_crypto_ctx_acquire" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "bpf_crypto_ctx" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "bpf_crypto_ctx" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_crypto_ctx_release" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "bpf_crypto_ctx" },
            DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        "bpf_crypto_encrypt" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "bpf_crypto_ctx" },
            DynptrArg { uninit: false, rdwr_only: false },
            DynptrArg { uninit: false, rdwr_only: false },
            Anything,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_crypto_decrypt" => CallProto::with_args([
            PtrToBtfIdNamed { type_name: "bpf_crypto_ctx" },
            DynptrArg { uninit: false, rdwr_only: false },
            DynptrArg { uninit: false, rdwr_only: false },
            Anything,
            DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- TCP raw syncookie kfuncs (xdp_synproxy_kern.c,
        //      test_tcp_custom_syncookie.c) ----
        //
        // u64 bpf_tcp_raw_gen_syncookie_ipv4(struct iphdr *, struct tcphdr *, u32)
        // u64 bpf_tcp_raw_gen_syncookie_ipv6(struct ipv6hdr *, struct tcphdr *, u32)
        // int bpf_tcp_raw_check_syncookie_ipv4(struct iphdr *, struct tcphdr *)
        // int bpf_tcp_raw_check_syncookie_ipv6(struct ipv6hdr *, struct tcphdr *)
        //   No flags. Operate on packet-derived header pointers.
        // int bpf_sk_assign_tcp_reqsk(struct __sk_buff *, struct sock *,
        //                              struct bpf_tcp_req_attrs *, u32)
        //   No flags. Used by test_tcp_custom_syncookie to install the
        //   custom syncookie's request_sock onto the skb.
        "bpf_tcp_raw_gen_syncookie_ipv4" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_tcp_raw_gen_syncookie_ipv6" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_tcp_raw_check_syncookie_ipv4" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_tcp_raw_check_syncookie_ipv6" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_sk_assign_tcp_reqsk" => CallProto::with_args([
            PtrToCtx, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- Conntrack kfuncs (test_bpf_nf.c, xdp_synproxy_kern.c) ----
        //
        // bpf_xdp_ct_lookup / bpf_xdp_ct_alloc / bpf_skb_ct_lookup / bpf_skb_ct_alloc:
        //   KF_ACQUIRE | KF_RET_NULL — return a refcounted nf_conn pointer.
        //   Args: ctx, sock_tuple, len, opts, opts_len.
        // bpf_ct_insert_entry:
        //   KF_ACQUIRE | KF_RET_NULL | KF_RELEASE on the input — confirms an
        //   allocated entry; consumes the alloc-time ref and returns a fresh
        //   inserted ref.
        // bpf_ct_release:
        //   KF_RELEASE — drops the refcount.
        // bpf_ct_set_timeout / bpf_ct_change_timeout / bpf_ct_set_status /
        // bpf_ct_change_status / bpf_ct_set_nat_info:
        //   No flags — non-acquire/release setters on a trusted nf_conn.
        "bpf_xdp_ct_lookup" => CallProto::with_args([
            PtrToCtx, Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "nf_conn" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_xdp_ct_alloc" => CallProto::with_args([
            PtrToCtx, Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "nf_conn___init" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_skb_ct_lookup" => CallProto::with_args([
            PtrToCtx, Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "nf_conn" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_skb_ct_alloc" => CallProto::with_args([
            PtrToCtx, Anything, Anything, Anything, Anything,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "nf_conn___init" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        // bpf_ct_insert_entry releases the input nf_conn___init ref and
        // returns a fresh nf_conn ref (transition from "uninitialized"
        // construction state to "live in conntrack table"). Modeled as
        // RELEASE+ACQUIRE+RET_NULL with ReleaseRefFromArg on R1.
        "bpf_ct_insert_entry" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "nf_conn" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL | CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        "bpf_ct_release" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        "bpf_ct_set_timeout" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        "bpf_ct_change_timeout" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_ct_set_status" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_ct_change_status" => CallProto::with_args([
            PtrToBtfId, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        "bpf_ct_set_nat_info" => CallProto::with_args([
            PtrToBtfId, Anything, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- xfrm state kfuncs (test_tunnel_kern.c xfrm_get_state_xdp) ----
        // struct xfrm_state *bpf_xdp_get_xfrm_state(struct xdp_md *ctx,
        //                                           struct bpf_xfrm_state_opts *opts,
        //                                           u32 opts__sz)
        //   KF_ACQUIRE | KF_RET_NULL — looks up an xfrm state by SPI/daddr.
        // void bpf_xdp_xfrm_state_release(struct xfrm_state *x)
        //   KF_RELEASE — drops the ref minted by bpf_xdp_get_xfrm_state.
        "bpf_xdp_get_xfrm_state" => CallProto::with_args([
            PtrToCtx, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::PtrToBtfIdNamed { type_name: "xfrm_state" })
        .flags(CallFlags::ACQUIRE | CallFlags::RET_NULL),

        "bpf_xdp_xfrm_state_release" => CallProto::with_args([
            PtrToBtfId, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void)
        .flags(CallFlags::RELEASE)
        .side_effects(&[SideEffect::ReleaseRefFromArg { arg: 0 }]),

        // ---- xfrm info kfuncs (xfrm_info.c) ----
        //   int bpf_skb_set_xfrm_info(struct __sk_buff *, const struct bpf_xfrm_info *)
        //   int bpf_skb_get_xfrm_info(struct __sk_buff *, struct bpf_xfrm_info *)
        "bpf_skb_set_xfrm_info" => CallProto::with_args([
            PtrToCtx, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),
        "bpf_skb_get_xfrm_info" => CallProto::with_args([
            PtrToCtx, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_task_under_cgroup ----
        // long bpf_task_under_cgroup(struct task_struct *task,
        //                            struct cgroup *ancestor)
        // Used by test_task_under_cgroup.c. task / ancestor are
        // Anything to accept PtrToTask/PtrToCgroup minted by the
        // existing acquire kfuncs.
        "bpf_task_under_cgroup" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- testmod cross-module kfuncs (test_ksyms_module.c) ----
        //   void bpf_testmod_test_mod_kfunc(int)
        //   void bpf_testmod_invalid_mod_kfunc(void)  (weak — present
        //   only when the test module is loaded; programs guard with
        //   ksym null check)
        "bpf_testmod_test_mod_kfunc" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),
        "bpf_testmod_invalid_mod_kfunc" => CallProto::with_args([
            DontCare, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Void),

        // ---- bpf_copy_from_user_str ----
        // int bpf_copy_from_user_str(void *dst, u32 size,
        //                            const void *unsafe_ptr, u64 flags)
        // Used by test_attach_probe.c sleepable uprobes. Modeled with
        // a writable pointer + size pair so the bounds check matches
        // the kernel's KF_ARG_PTR_TO_UNINIT_MEM rules.
        "bpf_copy_from_user_str" => CallProto::with_args([
            PtrToUninitMem, ConstSizeOrZero, Anything, Anything, DontCare,
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::COPY_FROM_USER_STR)
        // KF_SLEEPABLE: rejects calls inside preempt-disabled or
        // IRQ-disabled regions. Kernel `fn->might_sleep`. Without
        // this flag, irq.c::irq_sleepable_kfunc and
        // preempt_lock.c::preempt_sleepable_kfunc would PASS→FA.
        .flags(CallFlags::MIGHT_SLEEP),

        // int bpf_copy_from_user_task(void *dst, u32 size,
        //                              const void __user *src,
        //                              struct task_struct *task,
        //                              u64 flags)
        // Same as bpf_copy_from_user but reads from another task's
        // address space. KF_SLEEPABLE.
        "bpf_copy_from_user_task" => CallProto::with_args([
            PtrToUninitMem, ConstSize, Anything,
            PtrToBtfIdNamed { type_name: "task_struct" },
            Anything,
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::COPY_FROM_USER_STR)
        .flags(CallFlags::MIGHT_SLEEP),

        // int bpf_copy_from_user_task_str(void *dst, u32 size,
        //                                  const void __user *src,
        //                                  struct task_struct *task,
        //                                  u64 flags)
        // String variant — null-terminates and bounds the read.
        "bpf_copy_from_user_task_str" => CallProto::with_args([
            PtrToUninitMem, ConstSize, Anything,
            PtrToBtfIdNamed { type_name: "task_struct" },
            Anything,
        ])
        .ret(RetKind::Scalar)
        .mem_size_pairs(&pairs::COPY_FROM_USER_STR)
        .flags(CallFlags::MIGHT_SLEEP),

        // ---- bpf_sock_destroy (sock_destroy_prog.c) ----
        // int bpf_sock_destroy(struct sock_common *sk)
        // KF_TRUSTED_ARGS — invokes the kernel's sock-destroy path on
        // a trusted sock_common pointer (typically obtained from a
        // bpf_iter/tcp or bpf_iter/udp ctx). Returns negative errno or 0.
        // Kernel registers it for BPF_PROG_TYPE_TRACING/BPF_TRACE_ITER
        // only — programs in sock_destroy_prog.c use SEC("iter/{tcp,udp}")
        // which we type as Tracing kind. Anything-arg accepts both
        // PtrToBtfId{sock_common} (from iter ctx) and (struct sock_common
        // *) casts of typed sock pointers.
        "bpf_sock_destroy" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_get_kmem_cache (kmem_cache_iter.c) ----
        // struct kmem_cache *bpf_get_kmem_cache(u64 addr)
        // Returns a kernel slab cache pointer. Programs only use it
        // for null-check + map-lookup-by-pointer-value (no field
        // access on the returned pointer in test corpus), so a
        // Scalar return is sufficient.
        "bpf_get_kmem_cache" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_sock_addr_set_sun_path ----
        // int bpf_sock_addr_set_sun_path(struct bpf_sock_addr_kern *,
        //                                const __u8 *sun_path,
        //                                __u32 sun_path__sz)
        // Used by connect_unix_prog.c, getsockname_unix_prog.c,
        // getpeername_unix_prog.c, sendmsg_unix_prog.c,
        // recvmsg_unix_prog.c. Programs only use the int return for
        // an early-return; sa_kern field access still depends on
        // bpf_core_cast typing (separate gap).
        "bpf_sock_addr_set_sun_path" => CallProto::with_args([
            Anything, Anything, Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_get_fsverity_digest ----
        // int bpf_get_fsverity_digest(struct file *,
        //                             struct bpf_dynptr *digest_ptr)
        // Used by test_fsverity.c, test_sig_in_xattr.c. file arg is
        // Anything to accept the BPF_PROG-entry PtrToBtfId{file}.
        "bpf_get_fsverity_digest" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar),

        // ---- bpf_verify_pkcs7_signature ----
        // int bpf_verify_pkcs7_signature(struct bpf_dynptr *data,
        //                                struct bpf_dynptr *sig,
        //                                struct bpf_key *trusted_keyring)
        // Used by test_verify_pkcs7_sig.c, test_kfunc_dynptr_param.c,
        // test_sig_in_xattr.c. KF_SLEEPABLE per kernel registration.
        // First two args are dynptrs (consumer shape — slot must be
        // initialized); third is a refcounted bpf_key from
        // bpf_lookup_user_key / bpf_lookup_system_key.
        "bpf_verify_pkcs7_signature" => CallProto::with_args([
            DynptrArg { uninit: false, rdwr_only: false },
            DynptrArg { uninit: false, rdwr_only: false },
            Anything, DontCare, DontCare,
        ])
        .ret(RetKind::Scalar)
        .flags(CallFlags::MIGHT_SLEEP),

        // ---- bpf_rdonly_cast / bpf_core_cast ----
        // void *bpf_rdonly_cast(const void *obj, __u32 btf_id)
        // The kernel returns a pointer with the BTF type identified
        // by R2, with PTR_TRUSTED|MEM_RDONLY flags. R0 typing is
        // post-call: kfunc.rs reads R2's fixed value, looks up the
        // struct name in BTF, and stamps R0 as PtrToBtfId{name,
        // TRUSTED}. Used by sock_iter_batch.c, type_cast.c, and
        // the *_unix_prog family (via bpf_core_cast macro).
        // Registered as RetKind::Unknown so apply_call_proto_r0
        // doesn't clobber R0; the post-call hook sets it.
        "bpf_rdonly_cast" => CallProto::with_args([
            Anything, Anything, DontCare, DontCare, DontCare,
        ]),

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
        // R0 typed in kfunc.rs by per-ProgramKind kernel-ctx mapping
        // (kernel verifier `find_kern_ctx_type_id` /
        // `BPF_PROG_TYPE_*` table). Without that, programs that cast
        // via `bpf_cast_to_kern_ctx` then deref the kern struct's
        // fields (sa_kern->uaddrlen on bpf_sock_addr_kern, etc.) FR
        // on the deref. RetKind::Unknown defers R0 typing to the
        // post-call hook.
        "bpf_cast_to_kern_ctx" => CallProto::with_args([
            Anything, DontCare, DontCare, DontCare, DontCare,
        ]),

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
    // ARG_CONST_SIZE_OR_ZERO: kernel admits size=0 (no buffer access),
    // mirrors `bpf_get_stack`'s `ARG_CONST_SIZE_OR_ZERO` flag at the
    // helper proto. The previous `MemSizePair::new` (allow_zero=false)
    // was incorrect — it rejected `bpf_get_stack(ctx, buf, 0, flags)`
    // even though the kernel accepts.
    pub static GET_STACK: [MemSizePair; 1] = [MemSizePair::new_nullable(Reg::R2, Reg::R3)];
    pub static PERF_EVENT_OUTPUT: [MemSizePair; 1] = [MemSizePair::new(Reg::R4, Reg::R5)];
    pub static GET_CURRENT_COMM: [MemSizePair; 1] = [MemSizePair::new(Reg::R1, Reg::R2)];
    pub static PERF_EVENT_READ_VALUE: [MemSizePair; 1] = [MemSizePair::new(Reg::R3, Reg::R4)];
    pub static PERF_PROG_READ_VALUE: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];

    // ---- Local-cluster dynptr kfuncs (W4.2e) ----
    pub static DYNPTR_FROM_MEM: [MemSizePair; 1] = [MemSizePair::new(Reg::R1, Reg::R2)];
    // size=0 accepted (kernel runtime no-ops on zero-len read/write).
    pub static DYNPTR_READ: [MemSizePair; 1] = [MemSizePair::new_nullable(Reg::R1, Reg::R2)];
    pub static DYNPTR_WRITE: [MemSizePair; 1] = [MemSizePair::new_nullable(Reg::R3, Reg::R4)];

    // ---- Slice cluster (W4.2g) ----
    // R3 (`buffer__opt`) is the kernel's `__opt` scratch buffer: NULL is
    // allowed regardless of R4 (the helper just returns NULL when the
    // slow copy path would have been needed).
    pub static DYNPTR_SLICE: [MemSizePair; 1] = [MemSizePair::new_optional(Reg::R3, Reg::R4)];

    // ---- bpf_cpumask_populate(R1=dst, R2=src, R3=src__sz) ----
    pub static CPUMASK_POPULATE: [MemSizePair; 1] = [MemSizePair::new(Reg::R2, Reg::R3)];

    // ---- bpf_copy_from_user_str(R1=dst, R2=size, R3=unsafe_ptr, R4=flags) ----
    // size=0 accepted (kernel returns 0 / no-op).
    pub static COPY_FROM_USER_STR: [MemSizePair; 1] = [MemSizePair::new_nullable(Reg::R1, Reg::R2)];
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
        // bpf_snprintf: R1=buf (UNINIT_MEM_OR_NULL) paired with R2=size,
        //               R4=data (MEM_OR_NULL) paired with R5=data_len.
        constants::BPF_SNPRINTF => match ptr_arg_index {
            0 => Some(1),
            3 => Some(4),
            _ => None,
        },
        // Add other helpers with PTR_OR_NULL + SIZE_OR_ZERO pairs
        _ => None,
    }
}
