// src/analysis/constants.rs

// ============================================================================
// Basics
// ============================================================================
pub const BPF_STACK_MIN: i64 = -512;
pub const BPF_STACK_MAX: i64 = 0;
pub const BPF_MAX_CALL_FRAMES: usize = 8;

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
pub const BPF_GET_CGROUP_CLASS_ID: u32 = 17;
pub const BPF_REDIRECT: u32 = 23;
pub const BPF_PERF_EVENT_OUTPUT: u32 = 25;
pub const BPF_SKB_LOAD_BYTES: u32 = 26;
pub const BPF_CSUM_DIFF: u32 = 28;
pub const BPF_SKB_CHANGE_PROTO: u32 = 31;
pub const BPF_GET_HASH_RECALC: u32 = 34;
pub const BPF_SKB_CHANGE_TAIL: u32 = 38;
pub const BPF_SKB_PULL_DATA: u32 = 39;
pub const BPF_CSUM_UPDATE: u32 = 40;
pub const BPF_SKB_CHANGE_HEAD: u32 = 43;
pub const BPF_XDP_ADJUST_HEAD: u32 = 44;
pub const BPF_GET_SOCKET_COOKIE: u32 = 46;
pub const BPF_SKB_ADJUST_ROOM: u32 = 50;
pub const BPF_XDP_ADJUST_META: u32 = 54;
pub const BPF_GET_SOCKOPT:u32 = 57;
pub const BPF_FIB_LOOKUP: u32 = 69;
pub const BPF_GET_LOCAL_STORAGE: u32 = 81;
pub const BPF_SK_LOOKUP_TCP: u32 = 84;
pub const BPF_SK_LOOKUP_UDP: u32 = 85;
pub const BPF_SK_RELEASE: u32 = 86;
pub const BPF_SPIN_LOCK: u32 = 93;
pub const BPF_SPIN_UNLOCK: u32 = 94;
pub const BPF_SK_FULLSOCK: u32 = 95;
pub const BPF_TCP_SOCK: u32 = 96;
pub const BPF_SKB_ECN_SET_CE: u32 = 97;
pub const BPF_GET_LISTENER_SOCK: u32 = 98;
pub const BPF_SKC_LOOKUP_TCP: u32 = 99;
pub const BPF_STRTOUL: u32 = 106;
pub const BPF_SK_STORAGE_GET: u32 = 107;
pub const BPF_PROBE_READ_USER: u32 = 112;
pub const BPF_PROBE_READ_KERNEL: u32 = 113;
pub const BPF_SK_ASSIGN: u32 = 124;
pub const BPF_SKC_TO_TCP6_SOCK: u32 = 125;
pub const BPF_SKC_TO_TCP_SOCK: u32 = 126;
pub const BPF_SKC_TO_TCP_TIMEWAIT_SOCK: u32 = 127;
pub const BPF_SKC_TO_TCP_REQUEST_SOCK: u32 = 128;
pub const BPF_SKC_TO_UNIX_SOCK: u32 = 130;
pub const BPF_RINGBUF_RESERVE: u32 = 131;
pub const BPF_RINGBUF_SUBMIT: u32 = 132;
pub const BPF_SKC_TO_UDP6_SOCK: u32 = 140;
pub const BPF_GET_TASK_STACK:u32 = 141;
pub const BPF_D_PATH: u32 = 147;

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
// Cgroup Sock Addr Context (bpf_sock_addr) Field Offsets
// ============================================================================
//
// struct bpf_sock_addr {
//     __u32 user_family;      // 0   - WRITABLE
//     __u32 user_ip4;         // 4   - WRITABLE
//     __u32 user_ip6[4];      // 8-23 - WRITABLE
//     __u32 user_port;        // 24  - WRITABLE
//     __u32 family;           // 28
//     __u32 type;             // 32
//     __u32 protocol;         // 36
//     __u32 msg_src_ip4;      // 40
//     __u32 msg_src_ip6[4];   // 44-59
//     __bpf_md_ptr(sk);       // 60
// };

// Read-only fields
pub const SOCK_ADDR_CTX_FAMILY: i16 = 28;
pub const SOCK_ADDR_CTX_TYPE: i16 = 32;
pub const SOCK_ADDR_CTX_PROTOCOL: i16 = 36;
pub const SOCK_ADDR_CTX_MSG_SRC_IP4: i16 = 40;
pub const SOCK_ADDR_CTX_MSG_SRC_IP6_START: i16 = 44;
pub const SOCK_ADDR_CTX_MSG_SRC_IP6_END: i16 = 60;
pub const SOCK_ADDR_CTX_SK: i16 = 60;

// Writable fields (offset, end)
pub const SOCK_ADDR_CTX_USER_FAMILY: i16 = 0;
pub const SOCK_ADDR_CTX_USER_FAMILY_END: i16 = 4;

pub const SOCK_ADDR_CTX_USER_IP4: i16 = 4;
pub const SOCK_ADDR_CTX_USER_IP4_END: i16 = 8;

pub const SOCK_ADDR_CTX_USER_IP6_START: i16 = 8;
pub const SOCK_ADDR_CTX_USER_IP6_END: i16 = 24;  // 4 * 4 = 16 bytes

pub const SOCK_ADDR_CTX_USER_PORT: i16 = 24;
pub const SOCK_ADDR_CTX_USER_PORT_END: i16 = 28;

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
pub const MAX_PACKET_OFF: i64 = 0xFFFF;
pub const MAX_VAR_OFF: i64 = 1 << 29;

// ============================================================================
// BPF Map Types (from linux/bpf.h)
// ============================================================================
pub const BPF_MAP_TYPE_UNSPEC: u32 = 0;
pub const BPF_MAP_TYPE_HASH: u32 = 1;
pub const BPF_MAP_TYPE_ARRAY: u32 = 2;
pub const BPF_MAP_TYPE_PROG_ARRAY: u32 = 3;
pub const BPF_MAP_TYPE_PERF_EVENT_ARRAY: u32 = 4;
pub const BPF_MAP_TYPE_PERCPU_HASH: u32 = 5;
pub const BPF_MAP_TYPE_PERCPU_ARRAY: u32 = 6;
pub const BPF_MAP_TYPE_STACK_TRACE: u32 = 7;
pub const BPF_MAP_TYPE_CGROUP_ARRAY: u32 = 8;
pub const BPF_MAP_TYPE_LRU_HASH: u32 = 9;
pub const BPF_MAP_TYPE_LRU_PERCPU_HASH: u32 = 10;
pub const BPF_MAP_TYPE_LPM_TRIE: u32 = 11;
pub const BPF_MAP_TYPE_ARRAY_OF_MAPS: u32 = 12;
pub const BPF_MAP_TYPE_HASH_OF_MAPS: u32 = 13;
pub const BPF_MAP_TYPE_DEVMAP: u32 = 14;
pub const BPF_MAP_TYPE_SOCKMAP: u32 = 15;
pub const BPF_MAP_TYPE_CPUMAP: u32 = 16;
pub const BPF_MAP_TYPE_XSKMAP: u32 = 17;
pub const BPF_MAP_TYPE_SOCKHASH: u32 = 18;
pub const BPF_MAP_TYPE_CGROUP_STORAGE: u32 = 19;
pub const BPF_MAP_TYPE_REUSEPORT_SOCKARRAY: u32 = 20;
pub const BPF_MAP_TYPE_PERCPU_CGROUP_STORAGE: u32 = 21;
pub const BPF_MAP_TYPE_QUEUE: u32 = 22;
pub const BPF_MAP_TYPE_STACK: u32 = 23;
pub const BPF_MAP_TYPE_SK_STORAGE: u32 = 24;
pub const BPF_MAP_TYPE_DEVMAP_HASH: u32 = 25;
pub const BPF_MAP_TYPE_STRUCT_OPS: u32 = 26;
pub const BPF_MAP_TYPE_RINGBUF: u32 = 27;
pub const BPF_MAP_TYPE_INODE_STORAGE: u32 = 28;
pub const BPF_MAP_TYPE_TASK_STORAGE: u32 = 29;
pub const BPF_MAP_TYPE_BLOOM_FILTER: u32 = 30;

// Data section names (for identifying synthetic maps)
pub const DATA_SECTION_RODATA: &str = ".rodata";
pub const DATA_SECTION_DATA: &str = ".data";
pub const DATA_SECTION_BSS: &str = ".bss";

// ELF Section Types
pub const SHT_NOBITS: u32 = 8;

// Map Flags
// Program access permissions
pub const BPF_F_RDONLY_PROG: u32      = 1 << 7;  // 0x0080
pub const BPF_F_WRONLY_PROG: u32      = 1 << 8;  // 0x0100
pub const BPF_F_RDWR_PROG: u32        = 1 << 9;  // 0x0200

// ===========================================================================
// BPF Program Types
// ===========================================================================
pub const BPF_PROG_TYPE_UNSPEC: u32 = 0;
pub const BPF_PROG_TYPE_SOCKET_FILTER: u32 = 1;
pub const BPF_PROG_TYPE_KPROBE: u32 = 2;
pub const BPF_PROG_TYPE_SCHED_CLS: u32 = 3;
pub const BPF_PROG_TYPE_SCHED_ACT: u32 = 4;
pub const BPF_PROG_TYPE_TRACEPOINT: u32 = 5;
pub const BPF_PROG_TYPE_XDP: u32 = 6;
pub const BPF_PROG_TYPE_PERF_EVENT: u32 = 7;
pub const BPF_PROG_TYPE_CGROUP_SKB: u32 = 8;
pub const BPF_PROG_TYPE_CGROUP_SOCK: u32 = 9;
pub const BPF_PROG_TYPE_LWT_IN: u32 = 10;
pub const BPF_PROG_TYPE_LWT_OUT: u32 = 11;
pub const BPF_PROG_TYPE_LWT_XMIT: u32 = 12;
pub const BPF_PROG_TYPE_SOCK_OPS: u32 = 13;
pub const BPF_PROG_TYPE_SK_SKB: u32 = 14;
pub const BPF_PROG_TYPE_CGROUP_DEVICE: u32 = 15;
pub const BPF_PROG_TYPE_SK_MSG: u32 = 16;
pub const BPF_PROG_TYPE_RAW_TRACEPOINT: u32 = 17;
pub const BPF_PROG_TYPE_CGROUP_SOCK_ADDR: u32 = 18;
pub const BPF_PROG_TYPE_LWT_SEG6LOCAL: u32 = 19;
pub const BPF_PROG_TYPE_LIRC_MODE2: u32 = 20;
pub const BPF_PROG_TYPE_SK_REUSEPORT: u32 = 21;
pub const BPF_PROG_TYPE_FLOW_DISSECTOR: u32 = 22;
pub const BPF_PROG_TYPE_CGROUP_SYSCTL: u32 = 23;
pub const BPF_PROG_TYPE_RAW_TRACEPOINT_WRITABLE: u32 = 24;
pub const BPF_PROG_TYPE_CGROUP_SOCKOPT: u32 = 25;
pub const BPF_PROG_TYPE_TRACING: u32 = 26;
pub const BPF_PROG_TYPE_STRUCT_OPS: u32 = 27;
pub const BPF_PROG_TYPE_EXT: u32 = 28;
pub const BPF_PROG_TYPE_LSM: u32 = 29;
pub const BPF_PROG_TYPE_SK_LOOKUP: u32 = 30;
pub const BPF_PROG_TYPE_NETFILTER: u32 = 31;

// ==================================================
// BPF Attach types
// ==================================================
pub const BPF_ATTACH_TYPE_UNSPEC: u32 = 0;
pub const BPF_ATTACH_TYPE_NONE: u32 = 1;
pub const BPF_ATTACH_TYPE_SK_SKB: u32 = 2;
pub const BPF_ATTACH_TYPE_SK_MSG: u32 = 3;
pub const BPF_ATTACH_TYPE_SK_REUSEPORT: u32 = 4;
pub const BPF_ATTACH_TYPE_SK_LOOKUP: u32 = 5;
pub const BPF_ATTACH_TYPE_TRACE_RAW_TP: u32 = 24;
pub const BPF_ATTACH_TYPE_TRACE_ITER: u32 = 28;

// ==================================================
// BTF Constants
// ==================================================

pub const BTF_KIND_INT: u8 = 1;
pub const BTF_KIND_STRUCT: u8 = 4;

// ==================================================
// BPF Test flags
// ==================================================
pub const F_NEEDS_EFFICIENT_UNALIGNED_ACCESS: u32 = 1 << 0;
pub const F_LOAD_WITH_STRICT_ALIGNMENT: u32 = 1 << 1;
