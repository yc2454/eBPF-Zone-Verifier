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
use crate::analysis::machine::stack_state::DynptrKind;
use crate::common::constants;

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
    /// Must run inside an RCU read-side critical section.
    pub const RCU: Self = Self(1 << 4);
    /// Callable only from sleepable programs.
    pub const SLEEPABLE: Self = Self(1 << 5);
    /// Destructive kfunc (KF_DESTRUCTIVE).
    pub const DESTRUCTIVE: Self = Self(1 << 6);

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
        ]),

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
        ]),

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
        ]),

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
        ]),

        constants::BPF_SKB_SET_TUNNEL_KEY => CallProto::with_args([
            PtrToCtx,  // R1: skb
            PtrToMem,  // R2: key
            ConstSize, // R3: size
            Anything,  // R4: flags
            DontCare,
        ]),

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
        ]),

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
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL)),

        constants::BPF_SK_LOOKUP_TCP => CallProto::with_args([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ])
        .ret(RetKind::PtrToSocket)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL)),

        constants::BPF_SK_LOOKUP_UDP => CallProto::with_args([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ])
        .ret(RetKind::PtrToSocket)
        .flags(CallFlags::ACQUIRE.union(CallFlags::RET_NULL)),

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
            CallProto::with_args([PtrToCtx, Anything, Anything, PtrToUninitMem, ConstSize])
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
        ]),

        constants::BPF_PROBE_READ_KERNEL => CallProto::with_args([
            PtrToUninitMem,  // R1: dst (output buffer)
            ConstSizeOrZero, // R2: size
            Anything,        // R3: unsafe_ptr (kernel address, not validated)
            DontCare,
            DontCare,
        ]),

        constants::BPF_PERF_EVENT_READ_VALUE => CallProto::with_args([
            ConstMapPtr,     // R1: map
            Anything,        // R2: flags
            PtrToUninitMem,  // R3: buf
            ConstSizeOrZero, // R4: buf_size
            DontCare,
        ]),

        constants::BPF_PERF_PROG_READ_VALUE => CallProto::with_args([
            PtrToCtx,        // R1: ctx
            PtrToUninitMem,  // R2: buf
            ConstSizeOrZero, // R3: buf_size
            DontCare,        // R4: flags (not verified here)
            DontCare,
        ]),

        // ---- Spin lock related ----
        constants::BPF_SPIN_LOCK => {
            CallProto::with_args([Anything, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_SPIN_UNLOCK => {
            CallProto::with_args([Anything, DontCare, DontCare, DontCare, DontCare])
        }

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

        // ---- Information helpers ----
        constants::BPF_KTIME_GET_NS => {
            CallProto::with_args([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Process info helpers ----
        constants::BPF_GET_TASK_STACK => CallProto::with_args([
            PtrToBtfId,
            PtrToUninitMem,
            ConstSizeOrZero,
            Anything,
            DontCare,
        ]),

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

        constants::BPF_GET_CGROUP_CLASS_ID => {
            CallProto::with_args([PtrToCtx, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_GET_CURRENT_COMM => CallProto::with_args([
            PtrToUninitMem, // R1: buf (output buffer for comm string)
            ConstSize,      // R2: size_of_buf
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_PERF_EVENT_OUTPUT => CallProto::with_args([
            PtrToCtx,    // R1: ctx
            ConstMapPtr, // R2: map
            Anything,    // R3: flags
            PtrToMem,    // R4: data
            ConstSize,   // R5: size
        ]),

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

        _ => return None,
    })
}

/// Returns all pointer-size pairs for a given helper.
/// Returns empty slice if helper has no such pairs (e.g., map ops use fixed sizes).
pub fn get_mem_size_pairs(helper: u32) -> &'static [MemSizePair] {
    use Reg::*;

    // Define static arrays for each helper pattern
    static PROBE_READ: [MemSizePair; 1] = [MemSizePair::new_nullable(R1, R2)];

    static SKB_LOAD_BYTES: [MemSizePair; 1] = [MemSizePair::new(R3, R4)];

    static SKB_STORE_BYTES: [MemSizePair; 1] = [MemSizePair::new(R3, R4)];

    static SKB_GET_TUNNEL_KEY: [MemSizePair; 1] = [MemSizePair::new(R2, R3)];

    static SKB_SET_TUNNEL_KEY: [MemSizePair; 1] = [MemSizePair::new(R2, R3)];

    static CSUM_DIFF: [MemSizePair; 2] = [
        MemSizePair::new_nullable(R1, R2),
        MemSizePair::new_nullable(R3, R4),
    ];

    static SK_LOOKUP_TCP: [MemSizePair; 1] = [MemSizePair::new(R2, R3)];

    static SK_LOOKUP_UDP: [MemSizePair; 1] = [MemSizePair::new(R2, R3)];

    static GET_SOCKOPT: [MemSizePair; 1] = [MemSizePair::new(R4, R5)];

    static GET_TASK_STACK: [MemSizePair; 1] = [MemSizePair::new(R2, R3)];

    static GET_STACK: [MemSizePair; 1] = [MemSizePair::new(R2, R3)];

    static PERF_EVENT_OUTPUT: [MemSizePair; 1] = [MemSizePair::new(R4, R5)];

    static GET_CURRENT_COMM: [MemSizePair; 1] = [MemSizePair::new(R1, R2)];

    static PERF_EVENT_READ_VALUE: [MemSizePair; 1] = [MemSizePair::new(R3, R4)];

    static PERF_PROG_READ_VALUE: [MemSizePair; 1] = [MemSizePair::new(R2, R3)];

    static EMPTY: [MemSizePair; 0] = [];

    match helper {
        constants::BPF_PROBE_READ
        | constants::BPF_PROBE_READ_STR
        | constants::BPF_PROBE_READ_USER
        | constants::BPF_PROBE_READ_KERNEL => &PROBE_READ,

        constants::BPF_SKB_LOAD_BYTES => &SKB_LOAD_BYTES,

        constants::BPF_SKB_STORE_BYTES => &SKB_STORE_BYTES,

        constants::BPF_SKB_GET_TUNNEL_KEY => &SKB_GET_TUNNEL_KEY,

        constants::BPF_SKB_SET_TUNNEL_KEY => &SKB_SET_TUNNEL_KEY,

        constants::BPF_CSUM_DIFF => &CSUM_DIFF,

        constants::BPF_SK_LOOKUP_TCP => &SK_LOOKUP_TCP,

        constants::BPF_SK_LOOKUP_UDP => &SK_LOOKUP_UDP,

        constants::BPF_GET_SOCKOPT => &GET_SOCKOPT,

        constants::BPF_GET_TASK_STACK => &GET_TASK_STACK,

        constants::BPF_GET_STACK => &GET_STACK,

        constants::BPF_PERF_EVENT_OUTPUT => &PERF_EVENT_OUTPUT,

        constants::BPF_PERF_EVENT_READ_VALUE => &PERF_EVENT_READ_VALUE,

        constants::BPF_PERF_PROG_READ_VALUE => &PERF_PROG_READ_VALUE,

        constants::BPF_GET_CURRENT_COMM => &GET_CURRENT_COMM,

        // Note: BPF_RINGBUF_OUTPUT mem-size pair check is skipped because
        // the kernel allows reading uninitialized stack data in privileged mode.
        // TODO: Add privileged/unprivileged mode support to enable this check.
        _ => &EMPTY,
    }
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
