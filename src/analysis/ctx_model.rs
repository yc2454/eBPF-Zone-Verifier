// src/analysis/ctx_model.rs
//
// Data-driven BPF context field definitions and access validation.
//
// This module defines the layout of BPF context structures (sk_buff, xdp_md, etc.)
// as data tables, enabling unified validation of both reads and writes.

use log::warn;

use crate::ast::{MemSize, ProgramKind, ContextKind};

// ===========================================================================
// Core Types
// ===========================================================================

/// Abstract identifier for a memory region described by ctx fields.
/// This lets us say: "r6 points into region X, r1 is the end of region X".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemRegionId {
    /// Region used by the Calico debug/metadata buffer pattern:
    ///   r6 = *(ctx + 0x8c)
    ///   r1 = *(ctx + 0x4c)
    ///   check: r6 + 4 <= r1
    CalicoMetaRegion,
    // Future: PacketData, PacketMeta, MapValue0, etc.
}

/// What kind of value a ctx field holds (for type inference after loads).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CtxFieldKind {
    /// Plain scalar (int, flags, etc.). No pointer semantics.
    Scalar,

    /// A pointer into some memory region.
    PtrToMem { region: MemRegionId },

    /// Pointer to the start of the packet data.
    PacketStart,

    /// Pointer to the end of the packet data.
    PacketEnd,
}

/// A field in a BPF context struct.
#[derive(Clone, Copy, Debug)]
pub struct CtxField {
    /// Byte offset from context base
    pub offset: i16,
    /// Required access size
    pub size: MemSize,
    /// What kind of value this field holds
    pub kind: CtxFieldKind,
    /// Whether this field can be written by BPF programs
    pub writable: bool,
}

/// Result of validating a context access.
#[derive(Clone, Copy, Debug)]
pub struct CtxAccessInfo {
    /// What kind of value this field holds
    pub kind: CtxFieldKind,
    /// Whether this field can be written
    pub writable: bool,
}

// ===========================================================================
// Field Tables
// ===========================================================================

/// struct __sk_buff (TC/classifier context)
///
/// Reference: linux/include/uapi/linux/bpf.h
///
/// Note: The __sk_buff struct exposed to BPF is a "view" that the kernel
/// rewrites accesses for. Field offsets here match the BPF-visible layout.
const SK_BUFF_FIELDS: &[CtxField] = &[
    // __u32 len
    CtxField { offset: 0, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 pkt_type
    CtxField { offset: 4, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 mark
    CtxField { offset: 8, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 queue_mapping
    CtxField { offset: 12, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 protocol
    CtxField { offset: 16, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 vlan_present
    CtxField { offset: 20, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 vlan_tci
    CtxField { offset: 24, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 vlan_proto
    CtxField { offset: 28, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 priority
    CtxField { offset: 32, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 ingress_ifindex
    CtxField { offset: 36, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 ifindex
    CtxField { offset: 40, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 tc_index
    CtxField { offset: 44, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 cb[5] (offsets 48-67, 20 bytes) - control buffer, writable
    CtxField { offset: 48, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    CtxField { offset: 52, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    CtxField { offset: 56, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    CtxField { offset: 60, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    CtxField { offset: 64, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 hash
    CtxField { offset: 68, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 tc_classid
    CtxField { offset: 72, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 data
    CtxField { offset: 76, size: MemSize::U32, kind: CtxFieldKind::PacketStart, writable: false },
    // __u32 data_end
    CtxField { offset: 80, size: MemSize::U32, kind: CtxFieldKind::PacketEnd, writable: false },
    // __u32 napi_id
    CtxField { offset: 84, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 family
    CtxField { offset: 88, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 remote_ip4
    CtxField { offset: 92, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 local_ip4
    CtxField { offset: 96, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 remote_ip6[4]
    CtxField { offset: 100, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 104, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 108, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 112, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 local_ip6[4]
    CtxField { offset: 116, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 120, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 124, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 128, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 remote_port
    CtxField { offset: 132, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 local_port
    CtxField { offset: 136, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 data_meta
    CtxField { offset: 140, size: MemSize::U32, kind: CtxFieldKind::PtrToMem { region: MemRegionId::CalicoMetaRegion }, writable: false },
    // Additional fields can be added as needed...
];

/// struct xdp_md (XDP context)
///
/// Reference: linux/include/uapi/linux/bpf.h
const XDP_MD_FIELDS: &[CtxField] = &[
    // __u32 data
    CtxField { offset: 0, size: MemSize::U32, kind: CtxFieldKind::PacketStart, writable: false },
    // __u32 data_end
    CtxField { offset: 4, size: MemSize::U32, kind: CtxFieldKind::PacketEnd, writable: false },
    // __u32 data_meta
    CtxField { offset: 8, size: MemSize::U32, kind: CtxFieldKind::PacketStart, writable: false },
    // __u32 ingress_ifindex
    CtxField { offset: 12, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 rx_queue_index
    CtxField { offset: 16, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 egress_ifindex
    CtxField { offset: 20, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
];

/// struct bpf_sock_addr (cgroup sock_addr context)
///
/// Reference: linux/include/uapi/linux/bpf.h
const SOCK_ADDR_FIELDS: &[CtxField] = &[
    // __u32 user_family
    CtxField { offset: 0, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 user_ip4
    CtxField { offset: 4, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 user_ip6[4] (offsets 8-23)
    CtxField { offset: 8, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    CtxField { offset: 12, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    CtxField { offset: 16, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    CtxField { offset: 20, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 user_port
    CtxField { offset: 24, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: true },
    // __u32 family
    CtxField { offset: 28, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 type
    CtxField { offset: 32, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 protocol
    CtxField { offset: 36, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 msg_src_ip4
    CtxField { offset: 40, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 msg_src_ip6[4]
    CtxField { offset: 44, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 48, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 52, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 56, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __bpf_md_ptr(struct bpf_sock *, sk)
    CtxField { offset: 60, size: MemSize::U64, kind: CtxFieldKind::Scalar, writable: false },
];

/// struct bpf_sk_lookup (SK_LOOKUP context)
///
/// Reference: linux/include/uapi/linux/bpf.h
///
/// struct bpf_sk_lookup {
///     union {
///         __bpf_md_ptr(struct bpf_sock *, sk);
///         __u64 cookie;
///     };                          // 0-8
///     __u32 family;               // 8-12
///     __u32 protocol;             // 12-16
///     __u32 remote_ip4;           // 16-20
///     __u32 remote_ip6[4];        // 20-36
///     __be16 remote_port;         // 36-38 (accessed as u32 at 36)
///     __u16 :16;                  // 38-40 (padding)
///     __u32 local_ip4;            // 40-44
///     __u32 local_ip6[4];         // 44-60
///     __u32 local_port;           // 60-64
/// };
const SK_LOOKUP_FIELDS: &[CtxField] = &[
    // sk/cookie union (0-8): 8-byte read only
    CtxField { offset: 0, size: MemSize::U64, kind: CtxFieldKind::Scalar, writable: false },
    // family (8-12)
    CtxField { offset: 8, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // protocol (12-16)
    CtxField { offset: 12, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // remote_ip4 (16-20)
    CtxField { offset: 16, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // remote_ip6[4] (20-36)
    CtxField { offset: 20, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 24, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 28, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 32, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // remote_port (36-40, includes padding - accessed as u32)
    CtxField { offset: 36, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // local_ip4 (40-44)
    CtxField { offset: 40, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // local_ip6[4] (44-60)
    CtxField { offset: 44, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 48, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 52, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 56, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // local_port (60-64)
    CtxField { offset: 60, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
];

/// struct sk_msg_md (SK_MSG context)
///
/// Reference: linux/include/uapi/linux/bpf.h
///
/// struct sk_msg_md {
///     __bpf_md_ptr(void *, data);           // 0-8
///     __bpf_md_ptr(void *, data_end);       // 8-16
///     __u32 family;                          // 16-20
///     __u32 remote_ip4;                      // 20-24
///     __u32 local_ip4;                       // 24-28
///     __u32 remote_ip6[4];                   // 28-44
///     __u32 local_ip6[4];                    // 44-60
///     __u32 remote_port;                     // 60-64
///     __u32 local_port;                      // 64-68
///     __u32 size;                            // 68-72
///     __bpf_md_ptr(struct bpf_sock *, sk);   // 72-80
/// };
///
/// Note: __bpf_md_ptr creates 8-byte aligned unions. All sk_msg_md fields
/// are read-only; data modifications happen via helpers like bpf_msg_push_data.
const SK_MSG_MD_FIELDS: &[CtxField] = &[
    // __bpf_md_ptr(void *, data) - start of message data
    CtxField { offset: 0, size: MemSize::U64, kind: CtxFieldKind::PacketStart, writable: false },
    // __bpf_md_ptr(void *, data_end) - end of message data
    CtxField { offset: 8, size: MemSize::U64, kind: CtxFieldKind::PacketEnd, writable: false },
    // __u32 family
    CtxField { offset: 16, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 remote_ip4
    CtxField { offset: 20, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 local_ip4
    CtxField { offset: 24, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 remote_ip6[4]
    CtxField { offset: 28, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 32, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 36, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 40, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 local_ip6[4]
    CtxField { offset: 44, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 48, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 52, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    CtxField { offset: 56, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 remote_port
    CtxField { offset: 60, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 local_port
    CtxField { offset: 64, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __u32 size
    CtxField { offset: 68, size: MemSize::U32, kind: CtxFieldKind::Scalar, writable: false },
    // __bpf_md_ptr(struct bpf_sock *, sk) - current socket
    CtxField { offset: 72, size: MemSize::U64, kind: CtxFieldKind::Scalar, writable: false },
];

// ===========================================================================
// Field Lookup
// ===========================================================================

/// Look up field info for a context access.
/// Returns None if no valid field exists at (offset, size).
fn lookup_field(fields: &[CtxField], off: i16, size: MemSize) -> Option<CtxAccessInfo> {
    fields
        .iter()
        .find(|f| f.offset == off && f.size == size)
        .map(|f| CtxAccessInfo {
            kind: f.kind,
            writable: f.writable,
        })
}

/// Get the field table for a given context kind.
fn get_field_table(ctx_kind: ContextKind) -> Option<&'static [CtxField]> {
    match ctx_kind {
        ContextKind::SkBuff => Some(SK_BUFF_FIELDS),
        ContextKind::XdpMd => Some(XDP_MD_FIELDS),
        ContextKind::BpfSockAddr => Some(SOCK_ADDR_FIELDS),
        ContextKind::SkLookup => Some(SK_LOOKUP_FIELDS),
        ContextKind::SkMsgMd => Some(SK_MSG_MD_FIELDS),
        // Unknown context types - return None to indicate we can't validate
        _ => None,
    }
}

// ===========================================================================
// Public API
// ===========================================================================

/// Validate a context access and return field info if valid.
///
/// Returns:
/// - `Some(info)` if the access is valid, with field kind and writability
/// - `None` if the access is invalid (wrong offset, wrong size, or unknown context)
///
/// # Example
/// ```ignore
/// match validate_ctx_access(prog_kind, off, size) {
///     Some(info) => {
///         // For loads: use info.kind to determine destination register type
///         // For stores: check info.writable
///     }
///     None => {
///         // Invalid access - reject the program
///     }
/// }
/// ```
pub fn validate_ctx_access(prog_kind: ProgramKind, off: i16, size: MemSize) -> Option<CtxAccessInfo> {
    let ctx_kind = prog_kind.context_kind();

    // Get the field table for this context type
    let fields = match get_field_table(ctx_kind) {
        Some(f) => f,
        None => {
            warn!("Unknown context type: {:?}", ctx_kind);
            // Unknown context type - be permissive for now
            // This allows forward compatibility with new context types
            return Some(CtxAccessInfo {
                kind: CtxFieldKind::Scalar,
                writable: false,
            });
        }
    };

    lookup_field(fields, off, size)
}

/// Check if a context field is readable at the given offset and size.
///
/// This is a convenience wrapper around `validate_ctx_access` for cases
/// where you only need to check validity without the field info.
pub fn is_valid_ctx_read(prog_kind: ProgramKind, off: i16, size: MemSize) -> bool {
    validate_ctx_access(prog_kind, off, size).is_some()
}

/// Check if a context field is writable at the given offset and size.
///
/// Returns true only if the access is valid AND the field is writable.
pub fn is_valid_ctx_write(prog_kind: ProgramKind, off: i16, size: MemSize) -> bool {
    validate_ctx_access(prog_kind, off, size)
        .map(|info| info.writable)
        .unwrap_or(false)
}
