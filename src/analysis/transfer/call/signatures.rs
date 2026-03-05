// src/analysis/transfer/call/signatures.rs

use crate::analysis::machine::reg::Reg;
use crate::common::constants;

// ============================================================================
// BPF Argument Types
// ============================================================================

/// BPF helper function argument type constraints.
/// Based on Linux kernel's `enum bpf_arg_type` from include/linux/bpf.h
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum BpfArgType {
    /// Unused argument in helper function
    DontCare,

    // ---- Map-related argument types ----
    /// const argument used as pointer to bpf_map
    ConstMapPtr,
    /// pointer to stack used as map key
    PtrToMapKey,
    /// pointer to stack used as map value
    PtrToMapValue,
    /// pointer to valid memory used to store a map value (output)
    PtrToUninitMapValue,

    // ---- Memory access argument types ----
    /// pointer to valid memory (stack, packet, map value)
    PtrToMem,
    /// pointer to memory that doesn't need to be initialized (helper fills it)
    PtrToUninitMem,
    /// pointer to dynamically allocated memory
    PtrToAllocMem,

    // ---- Size argument types ----
    /// number of bytes accessed from memory
    ConstSize,
    /// number of bytes accessed from memory or 0
    ConstSizeOrZero,
    /// number of allocated bytes requested
    ConstAllocSizeOrZero,

    // ---- Context and general types ----
    /// pointer to context (sk_buff, xdp_md, etc.)
    PtrToCtx,
    /// any (initialized) argument is ok
    Anything,

    // ---- Socket types ----
    /// pointer to sock_common
    PtrToSockCommon,
    /// pointer to bpf_sock (fullsock)
    PtrToSocket,
    /// pointer to in-kernel sock_common or bpf-mirrored bpf_sock
    PtrToBTFIdSockCommon,

    // ---- BTF ID types ----
    PtrToBtfId,

    // ---- Stack types ----
    /// pointer to stack
    PtrToStack,

    // ---- Nullable variants ----
    /// PTR_TO_CTX | PTR_MAYBE_NULL
    PtrToCtxOrNull,
    /// PTR_TO_MEM | PTR_MAYBE_NULL
    PtrToMemOrNull,
    /// PTR_TO_STACK | PTR_MAYBE_NULL
    PtrToStackOrNull,
    /// PTR_TO_MAP_VALUE | PTR_MAYBE_NULL
    PtrToMapValueOrNull,

    // ---- Fixed-size pointer types ----
    /// pointer to initialized long/u64 value (helper reads from it)
    PtrToLong,
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
// Helper Function Signatures
// ============================================================================

/// Maximum number of arguments for a BPF helper function.
pub const MAX_BPF_FUNC_ARGS: usize = 5;

/// Signature of a BPF helper function.
#[derive(Debug, Clone, Copy)]
pub struct HelperSignature {
    /// Argument types for R1-R5 (use DontCare for unused args)
    pub args: [BpfArgType; MAX_BPF_FUNC_ARGS],
}

impl HelperSignature {
    const fn new(args: [BpfArgType; MAX_BPF_FUNC_ARGS]) -> Self {
        Self { args }
    }
}

// Convenience aliases
use BpfArgType::*;

/// Helper function signatures indexed by helper ID.
/// Returns None for unknown helpers.
pub fn get_helper_signature(helper: u32) -> Option<HelperSignature> {
    Some(match helper {
        // ---- Map operations ----
        constants::BPF_MAP_LOOKUP_ELEM => HelperSignature::new([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_MAP_UPDATE_ELEM => HelperSignature::new([
            ConstMapPtr,   // R1: map
            PtrToMapKey,   // R2: key
            PtrToMapValue, // R3: value
            Anything,      // R4: flags
            DontCare,
        ]),

        constants::BPF_MAP_DELETE_ELEM => HelperSignature::new([
            ConstMapPtr, // R1: map
            PtrToMapKey, // R2: key
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_LOCAL_STORAGE => HelperSignature::new([
            ConstMapPtr, // R1: map
            Anything,    // R2: index
            DontCare,
            DontCare,
            DontCare,
        ]),

        // ---- Memory helpers ----
        constants::BPF_GET_STACK => HelperSignature::new([
            PtrToCtx,
            PtrToUninitMem,
            ConstSizeOrZero,
            Anything,
            DontCare,
        ]),

        // ---- Tail call ----
        constants::BPF_TAIL_CALL => HelperSignature::new([
            PtrToCtx,    // R1: ctx
            ConstMapPtr, // R2: prog_array_map
            Anything,    // R3: index
            DontCare,
            DontCare,
        ]),

        // ---- Socket/context helpers ----
        constants::BPF_GET_SOCKET_COOKIE => HelperSignature::new([
            PtrToCtx, // R1: ctx
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_CSUM_UPDATE => HelperSignature::new([
            PtrToCtx, // R1: skb
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_CSUM_DIFF => HelperSignature::new([
            PtrToMemOrNull,  // R1: from
            ConstSizeOrZero, // R2: from_size
            PtrToMemOrNull,  // R3: to
            ConstSizeOrZero, // R4: to_size
            Anything,        // R5: seed
        ]),

        constants::BPF_SKB_ECN_SET_CE => HelperSignature::new([
            PtrToCtxOrNull, // R1: skb (can be NULL)
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_GET_HASH_RECALC => HelperSignature::new([
            PtrToCtx, // R1: ctx
            DontCare, DontCare, DontCare, DontCare,
        ]),

        // ---- SKB data access ----
        constants::BPF_SKB_LOAD_BYTES => HelperSignature::new([
            PtrToCtx,       // R1: skb
            Anything,       // R2: offset
            PtrToUninitMem, // R3: to (destination buffer)
            ConstSize,      // R4: len
            DontCare,
        ]),

        constants::BPF_SKB_VLAN_PUSH => HelperSignature::new([
            PtrToCtx, // R1: skb
            Anything, // R2: vlan_proto
            Anything, // R3: vlan_tci
            DontCare, DontCare,
        ]),

        constants::BPF_SKB_GET_TUNNEL_KEY => HelperSignature::new([
            PtrToCtx,       // R1: skb
            PtrToUninitMem, // R2: key (buffer to store key)
            ConstSize,      // R3: size
            Anything,       // R4: flags
            DontCare,
        ]),

        constants::BPF_SKB_SET_TUNNEL_KEY => HelperSignature::new([
            PtrToCtx,  // R1: skb
            PtrToMem,  // R2: key
            ConstSize, // R3: size
            Anything,  // R4: flags
            DontCare,
        ]),

        constants::BPF_SKB_VLAN_POP => HelperSignature::new([
            PtrToCtx, // R1: skb
            DontCare, DontCare, DontCare, DontCare,
        ]),

        constants::BPF_SKB_STORE_BYTES => HelperSignature::new([
            PtrToCtx,  // R1: skb
            Anything,  // R2: offset
            PtrToMem,  // R3: from (source buffer)
            ConstSize, // R4: len
            DontCare,
        ]),

        // ---- Redirect ----
        constants::BPF_REDIRECT => HelperSignature::new([
            Anything, // R1: ifindex
            Anything, // R2: flags
            DontCare, DontCare, DontCare,
        ]),

        // ---- XDP helpers ----
        constants::BPF_XDP_ADJUST_HEAD
        | constants::BPF_XDP_ADJUST_TAIL
        | constants::BPF_XDP_ADJUST_META => HelperSignature::new([
            PtrToCtx, // R1: xdp_md
            Anything, // R2: delta
            DontCare, DontCare, DontCare,
        ]),

        // ---- Tail modification ----
        constants::BPF_SKB_CHANGE_TAIL => HelperSignature::new([
            PtrToCtx, // R1: skb
            Anything, // R2: len
            Anything, // R3: flags
            DontCare, DontCare,
        ]),

        // ---- Socket lookup ----
        constants::BPF_SKC_LOOKUP_TCP => HelperSignature::new([
            PtrToCtx, // R1: ctx
            PtrToMem, // R2: tuple
            Anything, // R3: tuple_size
            DontCare, DontCare,
        ]),

        constants::BPF_SK_LOOKUP_TCP => HelperSignature::new([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ]),

        constants::BPF_SK_LOOKUP_UDP => HelperSignature::new([
            PtrToCtx,  // R1: ctx
            PtrToMem,  // R2: tuple
            ConstSize, // R3: tuple_size
            Anything,  // R4: netns
            Anything,  // R5: flags
        ]),

        constants::BPF_SK_RELEASE => HelperSignature::new([
            PtrToSocket, // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_SKC_TO_UDP6_SOCK => HelperSignature::new([
            PtrToSocket, // R1: socket
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_SK_FULLSOCK => HelperSignature::new([
            PtrToSockCommon, // R1: sock_common
            DontCare,
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_TCP_SOCK => {
            HelperSignature::new([PtrToSockCommon, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Socket storage helpers ----
        constants::BPF_SK_STORAGE_GET => HelperSignature::new([
            ConstMapPtr,
            PtrToBTFIdSockCommon,
            PtrToMapValueOrNull,
            Anything,
            DontCare,
        ]),

        constants::BPF_GET_SOCKOPT => {
            HelperSignature::new([PtrToCtx, Anything, Anything, PtrToUninitMem, ConstSize])
        }

        // ---- FIB lookup ----
        constants::BPF_FIB_LOOKUP => HelperSignature::new([
            PtrToCtx, // R1: ctx
            PtrToMem, // R2: params (bpf_fib_lookup struct)
            Anything, // R3: plen
            Anything, // R4: flags
            DontCare,
        ]),

        constants::BPF_PROBE_READ
        | constants::BPF_PROBE_READ_STR
        | constants::BPF_PROBE_READ_USER => HelperSignature::new([
            PtrToUninitMem,  // R1: dst
            ConstSizeOrZero, // R2: size
            Anything,        // R3: unsafe_ptr (user address)
            DontCare,
            DontCare,
        ]),

        constants::BPF_PROBE_READ_KERNEL => HelperSignature::new([
            PtrToUninitMem,  // R1: dst (output buffer)
            ConstSizeOrZero, // R2: size
            Anything,        // R3: unsafe_ptr (kernel address, not validated)
            DontCare,
            DontCare,
        ]),

        constants::BPF_PERF_EVENT_READ_VALUE => HelperSignature::new([
            ConstMapPtr,     // R1: map
            Anything,        // R2: flags
            PtrToUninitMem,  // R3: buf
            ConstSizeOrZero, // R4: buf_size
            DontCare,
        ]),

        constants::BPF_PERF_PROG_READ_VALUE => HelperSignature::new([
            PtrToCtx,        // R1: ctx
            PtrToUninitMem,  // R2: buf
            ConstSizeOrZero, // R3: buf_size
            DontCare,        // R4: flags (not verified here)
            DontCare,
        ]),

        // ---- Spin lock related ----
        constants::BPF_SPIN_LOCK => {
            HelperSignature::new([Anything, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_SPIN_UNLOCK => {
            HelperSignature::new([Anything, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Ringbuf helpers ----
        constants::BPF_RINGBUF_OUTPUT => HelperSignature::new([
            ConstMapPtr,     // R1: ringbuf map
            PtrToMem,        // R2: data to copy (must be initialized)
            ConstSizeOrZero, // R3: size
            Anything,        // R4: flags
            DontCare,
        ]),

        constants::BPF_RINGBUF_RESERVE => HelperSignature::new([
            ConstMapPtr,
            ConstAllocSizeOrZero,
            Anything,
            DontCare,
            DontCare,
        ]),

        constants::BPF_RINGBUF_SUBMIT => {
            HelperSignature::new([PtrToAllocMem, Anything, DontCare, DontCare, DontCare])
        }

        // ---- Information helpers ----
        constants::BPF_KTIME_GET_NS => {
            HelperSignature::new([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        // ---- Process info helpers ----
        constants::BPF_GET_TASK_STACK => HelperSignature::new([
            PtrToBtfId,
            PtrToUninitMem,
            ConstSizeOrZero,
            Anything,
            DontCare,
        ]),

        // ---- Sockmap operations ----
        constants::BPF_SOCK_MAP_UPDATE => HelperSignature::new([
            PtrToCtx,    // R1: bpf_sock_ops context (SockOps only)
            ConstMapPtr, // R2: sockmap
            PtrToMapKey, // R3: key
            Anything,    // R4: flags
            DontCare,
        ]),

        // ---- Miscellaneous ----
        constants::BPF_GET_PRANDOM_U32 => {
            HelperSignature::new([DontCare, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_TRACE_PRINTK => HelperSignature::new([
            PtrToMem,  // R1: fmt string
            ConstSize, // R2: fmt_size (MUST BE > 0)
            Anything,  // R3: arg1
            Anything,  // R4: arg2
            Anything,  // R5: arg3
        ]),

        constants::BPF_STRTOUL => {
            HelperSignature::new([PtrToMem, ConstSize, Anything, PtrToLong, DontCare])
        }

        constants::BPF_GET_CGROUP_CLASS_ID => {
            HelperSignature::new([PtrToCtx, DontCare, DontCare, DontCare, DontCare])
        }

        constants::BPF_GET_CURRENT_COMM => HelperSignature::new([
            PtrToUninitMem, // R1: buf (output buffer for comm string)
            ConstSize,      // R2: size_of_buf
            DontCare,
            DontCare,
            DontCare,
        ]),

        constants::BPF_PERF_EVENT_OUTPUT => HelperSignature::new([
            PtrToCtx,    // R1: ctx
            ConstMapPtr, // R2: map
            Anything,    // R3: flags
            PtrToMem,    // R4: data
            ConstSize,   // R5: size
        ]),

        constants::BPF_L3_CSUM_REPLACE => HelperSignature::new([
            PtrToCtx, // R1: skb
            Anything, // R2: offset
            Anything, // R3: from
            Anything, // R4: to
            Anything, // R5: flags
        ]),

        constants::BPF_L4_CSUM_REPLACE => HelperSignature::new([
            PtrToCtx, // R1: skb
            Anything, // R2: offset
            Anything, // R3: from
            Anything, // R4: to
            Anything, // R5: flags
        ]),

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
