// src/analysis/constants.rs

// ============================================================================
// BPF Helper IDs
// ============================================================================

pub const BPF_MAP_LOOKUP_ELEM: u32 = 1;
pub const BPF_MAP_UPDATE_ELEM: u32 = 2;
pub const BPF_MAP_DELETE_ELEM: u32 = 3;
pub const BPF_PROBE_READ: u32 = 4;
pub const BPF_KTIME_GET_NS: u32 = 5;
pub const BPF_TRACE_PRINTK: u32 = 6;
pub const BPF_GET_PRANDOM_U32: u32 = 7;
pub const BPF_GET_SMP_PROCESSOR_ID: u32 = 8;
pub const BPF_SKB_STORE_BYTES: u32 = 9;
pub const BPF_L3_CSUM_REPLACE: u32 = 10;
pub const BPF_L4_CSUM_REPLACE: u32 = 11;
pub const BPF_TAIL_CALL: u32 = 12;
pub const BPF_CLONE_REDIRECT: u32 = 13;
pub const BPF_REDIRECT: u32 = 23;
pub const BPF_PERF_EVENT_OUTPUT: u32 = 25;
pub const BPF_SKB_LOAD_BYTES: u32 = 26;
pub const BPF_CSUM_DIFF: u32 = 28;
pub const BPF_SKB_PULL_DATA: u32 = 39;
pub const BPF_SKB_CHANGE_HEAD: u32 = 43;
pub const BPF_XDP_ADJUST_HEAD: u32 = 44;
pub const BPF_XDP_ADJUST_META: u32 = 54;
pub const BPF_SKB_CHANGE_TAIL: u32 = 38;
pub const BPF_SKB_CHANGE_PROTO: u32 = 31;
pub const BPF_SKB_ADJUST_ROOM: u32 = 50;
pub const BPF_FIB_LOOKUP: u32 = 69;

// ============================================================================
// TC Context (__sk_buff) Field Offsets
// ============================================================================
//
// struct __sk_buff {
//     __u32 len;              // 0
//     __u32 pkt_type;         // 4
//     __u32 mark;             // 8   - WRITABLE
//     __u32 queue_mapping;    // 12  - WRITABLE
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

pub const TC_CTX_QUEUE_MAPPING: i16 = 12;
pub const TC_CTX_QUEUE_MAPPING_END: i16 = 16;

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

// ============================================================================
// Packet Access Heuristics
// ============================================================================

pub const MAX_PACKET_HEADER_ACCESS: i64 = 64;
pub const ETH_HEADER_SIZE: i64 = 14;

// ============================================================================
// Limits & Defaults
// ============================================================================

pub const DEFAULT_MAP_VALUE_SIZE: i64 = 4096;
pub const MAX_INSN_PROCESSED: usize = 1_000_000;
pub const MAX_TAIL_CALL_DEPTH: u32 = 33;
pub const LOG_HEARTBEAT_INTERVAL: usize = 10_000;