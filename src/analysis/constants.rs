// src/analysis/constants.rs - Enhanced with full helper catalog

// --- BPF HELPER IDS (u32) ---
// Defined in linux/bpf.h (UAPI) - https://elixir.bootlin.com/linux/latest/source/include/uapi/linux/bpf.h

// Map operations
pub const BPF_MAP_LOOKUP_ELEM: u32 = 1;
pub const BPF_MAP_UPDATE_ELEM: u32 = 2;
pub const BPF_MAP_DELETE_ELEM: u32 = 3;

// Probing
pub const BPF_PROBE_READ: u32 = 4;
pub const BPF_PROBE_READ_STR: u32 = 45;
pub const BPF_PROBE_READ_USER: u32 = 112;
pub const BPF_PROBE_READ_KERNEL: u32 = 113;
pub const BPF_PROBE_READ_USER_STR: u32 = 114;
pub const BPF_PROBE_READ_KERNEL_STR: u32 = 115;

// Time
pub const BPF_KTIME_GET_NS: u32 = 5;
pub const BPF_KTIME_GET_BOOT_NS: u32 = 125;

// Debug/Trace
pub const BPF_TRACE_PRINTK: u32 = 6;
pub const BPF_PERF_EVENT_OUTPUT: u32 = 25;
pub const BPF_PERF_EVENT_READ: u32 = 22;
pub const BPF_GET_STACKID: u32 = 27;

// Random/CPU
pub const BPF_GET_PRANDOM_U32: u32 = 7;
pub const BPF_GET_SMP_PROCESSOR_ID: u32 = 8;
pub const BPF_GET_NUMA_NODE_ID: u32 = 42;

// Packet manipulation (TC/XDP)
pub const BPF_SKB_STORE_BYTES: u32 = 9;
pub const BPF_L3_CSUM_REPLACE: u32 = 10;
pub const BPF_L4_CSUM_REPLACE: u32 = 11;
pub const BPF_TAIL_CALL: u32 = 12;
pub const BPF_CLONE_REDIRECT: u32 = 13;
pub const BPF_SKB_VLAN_PUSH: u32 = 18;
pub const BPF_SKB_VLAN_POP: u32 = 19;
pub const BPF_SKB_LOAD_BYTES: u32 = 26;
pub const BPF_CSUM_DIFF: u32 = 28;
pub const BPF_SKB_CHANGE_PROTO: u32 = 31;
pub const BPF_SKB_CHANGE_TYPE: u32 = 32;
pub const BPF_GET_HASH_RECALC: u32 = 34;
pub const BPF_SKB_CHANGE_TAIL: u32 = 38;
pub const BPF_SKB_PULL_DATA: u32 = 39;
pub const BPF_CSUM_UPDATE: u32 = 40;
pub const BPF_SET_HASH_INVALID: u32 = 41;
pub const BPF_SKB_CHANGE_HEAD: u32 = 43;
pub const BPF_SET_HASH: u32 = 48;
pub const BPF_SKB_ADJUST_ROOM: u32 = 50;

// XDP specific
pub const BPF_XDP_ADJUST_HEAD: u32 = 44;
pub const BPF_XDP_ADJUST_META: u32 = 54;
pub const BPF_XDP_ADJUST_TAIL: u32 = 65;

// Redirect
pub const BPF_REDIRECT: u32 = 23;
pub const BPF_REDIRECT_MAP: u32 = 51;
pub const BPF_REDIRECT_PEER: u32 = 155;
pub const BPF_REDIRECT_NEIGH: u32 = 152;

// Tunnel
pub const BPF_SKB_GET_TUNNEL_KEY: u32 = 20;
pub const BPF_SKB_SET_TUNNEL_KEY: u32 = 21;
pub const BPF_SKB_GET_TUNNEL_OPT: u32 = 29;
pub const BPF_SKB_SET_TUNNEL_OPT: u32 = 30;

// Process/task info
pub const BPF_GET_CURRENT_PID_TGID: u32 = 14;
pub const BPF_GET_CURRENT_UID_GID: u32 = 15;
pub const BPF_GET_CURRENT_COMM: u32 = 16;
pub const BPF_GET_CURRENT_TASK: u32 = 35;

// Cgroup
pub const BPF_GET_CGROUP_CLASSID: u32 = 17;
pub const BPF_SKB_UNDER_CGROUP: u32 = 33;
pub const BPF_CURRENT_TASK_UNDER_CGROUP: u32 = 37;

// Socket
pub const BPF_GET_SOCKET_COOKIE: u32 = 46;
pub const BPF_GET_SOCKET_UID: u32 = 47;
pub const BPF_SETSOCKOPT: u32 = 49;
pub const BPF_GETSOCKOPT: u32 = 57;
pub const BPF_SK_REDIRECT_MAP: u32 = 52;
pub const BPF_SOCK_MAP_UPDATE: u32 = 53;
pub const BPF_SK_LOOKUP_TCP: u32 = 84;
pub const BPF_SK_LOOKUP_UDP: u32 = 85;
pub const BPF_SK_RELEASE: u32 = 86;

// FIB/Routing
pub const BPF_FIB_LOOKUP: u32 = 69;
pub const BPF_GET_ROUTE_REALM: u32 = 24;

// Spin locks
pub const BPF_SPIN_LOCK: u32 = 93;
pub const BPF_SPIN_UNLOCK: u32 = 94;

// Ring buffer
pub const BPF_RINGBUF_OUTPUT: u32 = 130;
pub const BPF_RINGBUF_RESERVE: u32 = 131;
pub const BPF_RINGBUF_SUBMIT: u32 = 132;
pub const BPF_RINGBUF_DISCARD: u32 = 133;
pub const BPF_RINGBUF_QUERY: u32 = 134;

// ============================================================================
// TC Context (__sk_buff) Field Offsets
// ============================================================================
//
// struct __sk_buff {
//     __u32 len;              // 0
//     __u32 pkt_type;         // 4
//     __u32 mark;             // 8   - WRITABLE
//     __u32 queue_mapping;    // 12
//     __u32 protocol;         // 16
//     __u32 vlan_present;     // 20
//     __u32 vlan_tci;         // 24
//     __u32 vlan_proto;       // 28
//     __u32 priority;         // 32  - WRITABLE
//     __u32 ingress_ifindex;  // 36
//     __u32 ifindex;          // 40
//     __u32 tc_index;         // 44  - WRITABLE
//     __u32 cb[5];            // 48-67 - WRITABLE
//     __u32 hash;             // 68
//     __u32 tc_classid;       // 72  - WRITABLE
//     __u32 data;             // 76
//     __u32 data_end;         // 80
//     __u32 napi_id;          // 84
//     __u32 family;           // 88
//     ...
//     __u32 data_meta;        // 140
// };

// Read-only fields
pub const TC_CTX_LEN: i16 = 0;
pub const TC_CTX_PKT_TYPE: i16 = 4;
pub const TC_CTX_QUEUE_MAPPING: i16 = 12;
pub const TC_CTX_PROTOCOL: i16 = 16;
pub const TC_CTX_VLAN_PRESENT: i16 = 20;
pub const TC_CTX_VLAN_TCI: i16 = 24;
pub const TC_CTX_VLAN_PROTO: i16 = 28;
pub const TC_CTX_INGRESS_IFINDEX: i16 = 36;
pub const TC_CTX_IFINDEX: i16 = 40;
pub const TC_CTX_HASH: i16 = 68;
pub const TC_CTX_DATA: i16 = 76;        // 0x4c - packet start
pub const TC_CTX_DATA_END: i16 = 80;    // 0x50 - packet end
pub const TC_CTX_NAPI_ID: i16 = 84;
pub const TC_CTX_FAMILY: i16 = 88;
pub const TC_CTX_DATA_META: i16 = 140;  // 0x8c

// Writable fields (offset, end)
pub const TC_CTX_MARK: i16 = 8;
pub const TC_CTX_MARK_END: i16 = 12;

pub const TC_CTX_PRIORITY: i16 = 32;
pub const TC_CTX_PRIORITY_END: i16 = 36;

pub const TC_CTX_TC_INDEX: i16 = 44;
pub const TC_CTX_TC_INDEX_END: i16 = 48;

pub const TC_CTX_CB_START: i16 = 48;
pub const TC_CTX_CB_END: i16 = 68;      // cb[5] = 5 * 4 = 20 bytes

pub const TC_CTX_TC_CLASSID: i16 = 72;
pub const TC_CTX_TC_CLASSID_END: i16 = 76;

// ============================================================================
// XDP Context (xdp_md) Field Offsets
// ============================================================================
//
// struct xdp_md {
//     __u32 data;             // 0
//     __u32 data_end;         // 4
//     __u32 data_meta;        // 8
//     __u32 ingress_ifindex;  // 12
//     __u32 rx_queue_index;   // 16  - WRITABLE
//     __u32 egress_ifindex;   // 20  - WRITABLE (XDP_REDIRECT)
// };

pub const XDP_CTX_DATA: i16 = 0;
pub const XDP_CTX_DATA_END: i16 = 4;
pub const XDP_CTX_DATA_META: i16 = 8;
pub const XDP_CTX_INGRESS_IFINDEX: i16 = 12;

// Writable fields
pub const XDP_CTX_RX_QUEUE_INDEX: i16 = 16;
pub const XDP_CTX_RX_QUEUE_INDEX_END: i16 = 20;

pub const XDP_CTX_EGRESS_IFINDEX: i16 = 20;
pub const XDP_CTX_EGRESS_IFINDEX_END: i16 = 24;

// --- HELPERS THAT INVALIDATE PACKET POINTERS ---
// After calling these, all PTR_TO_PACKET / PTR_TO_PACKET_END must be reloaded
pub const PACKET_INVALIDATING_HELPERS: &[u32] = &[
    BPF_XDP_ADJUST_HEAD,
    BPF_XDP_ADJUST_META,
    BPF_XDP_ADJUST_TAIL,
    BPF_SKB_CHANGE_HEAD,
    BPF_SKB_CHANGE_TAIL,
    BPF_SKB_PULL_DATA,
    BPF_SKB_CHANGE_PROTO,
    BPF_SKB_ADJUST_ROOM,
];

// --- HELPERS THAT RETURN POINTERS ---
// These need special return type handling
pub const POINTER_RETURNING_HELPERS: &[u32] = &[
    BPF_MAP_LOOKUP_ELEM,      // -> PTR_TO_MAP_VALUE_OR_NULL
    BPF_SK_LOOKUP_TCP,        // -> PTR_TO_SOCKET_OR_NULL
    BPF_SK_LOOKUP_UDP,        // -> PTR_TO_SOCKET_OR_NULL
    BPF_RINGBUF_RESERVE,      // -> PTR_TO_MEM_OR_NULL
    BPF_GET_CURRENT_TASK,     // -> PTR_TO_BTF_ID
];

// --- PACKET ACCESS HEURISTICS ---
pub const MAX_PACKET_HEADER_ACCESS: i64 = 64;
pub const ETH_HEADER_SIZE: i64 = 14;

// --- LIMITS & DEFAULTS ---
pub const DEFAULT_MAP_VALUE_SIZE: i64 = 4096;
pub const MAX_INSN_PROCESSED: usize = 1_000_000;
pub const MAX_TAIL_CALL_DEPTH: u32 = 33;

// Logging Intervals
pub const LOG_HEARTBEAT_INTERVAL: usize = 10_000;

// --- Helper to check if a helper invalidates packets ---
pub fn invalidates_packet_pointers(helper_id: u32) -> bool {
    PACKET_INVALIDATING_HELPERS.contains(&helper_id)
}

// --- Helper to check if a helper returns a pointer ---
pub fn returns_pointer(helper_id: u32) -> bool {
    POINTER_RETURNING_HELPERS.contains(&helper_id)
}