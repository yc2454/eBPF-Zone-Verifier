// src/ctx_model.rs

use crate::ast::{MemSize, ProgramKind, ContextKind};
use crate::analysis::constants;

/// Abstract identifier for a memory region described by ctx fields.
/// This lets us say: "r6 points into region X, r1 is the end of region X".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemRegionId {
    /// Region used by the Calico debug/metadata buffer pattern:
    ///   r6 = *(ctx + 0x8c)
    ///   r1 = *(ctx + 0x4c)
    ///   check: r6 + 4 <= r1
    CalicoMetaRegion,
    // Later: PacketData, PacketMeta, MapValue0, etc.
}

/// What kind of thing a ctx field is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CtxFieldKind {
    /// Plain scalar (int, flags, etc.). No pointer semantics.
    Scalar,

    /// A pointer into some memory region.
    PtrToMem {
        region: MemRegionId,
    },

    /// An "end" pointer or bound for a memory region.
    /// Typically used in patterns like:
    ///   base = PtrToMem
    ///   end  = MemEnd
    ///   if base + width <= end -> safe deref
    MemEnd {
        region: MemRegionId,
    },

    /// Pointer to the start of the packet data.
    PacketStart,

    /// Pointer to the end of the packet data.
    PacketEnd,
}

/// TC-specific ctx classifier.
///
/// Given an offset and size of a load from PTR_TO_CTX, classify the field.
/// Offsets here are *very* specific to your current Calico program pattern
/// and can be refined later.
/// TC-specific ctx classifier for LOADS.
pub fn classify_sk_buff_field(off: i16, size: MemSize) -> Option<CtxFieldKind> {
    match (off, size) {
        // data (Packet Start)
        (constants::TC_CTX_DATA, MemSize::U32) => Some(CtxFieldKind::PacketStart),

        // data_end (Packet End)
        (constants::TC_CTX_DATA_END, MemSize::U32) => Some(CtxFieldKind::PacketEnd),

        // data_meta (Calico metadata pointer)
        (constants::TC_CTX_DATA_META, MemSize::U32) => Some(CtxFieldKind::PtrToMem {
            region: MemRegionId::CalicoMetaRegion,
        }),

        // Everything else: scalar
        _ => Some(CtxFieldKind::Scalar),
    }
}

/// XDP-specific ctx classifier for LOADS.
pub fn classify_xdp_md_field(off: i16, size: MemSize) -> Option<CtxFieldKind> {
    match (off, size) {
        (constants::XDP_CTX_DATA, MemSize::U32) => Some(CtxFieldKind::PacketStart),
        (constants::XDP_CTX_DATA_END, MemSize::U32) => Some(CtxFieldKind::PacketEnd),
        (constants::XDP_CTX_DATA_META, MemSize::U32) => Some(CtxFieldKind::PacketStart),
        _ => Some(CtxFieldKind::Scalar),
    }
}

/// Check if a TC context field is writable.
pub fn is_sk_buff_field_writable(off: i16, size: MemSize) -> bool {
    let access_size: i16 = match size {
        MemSize::U8 => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    };
    let access_end = off + access_size;

    // mark
    if off >= constants::TC_CTX_MARK && access_end <= constants::TC_CTX_MARK_END {
        return true;
    }

    // queue_mapping
    if off >= constants::TC_CTX_QUEUE_MAPPING && access_end <= constants::TC_CTX_QUEUE_MAPPING_END {
        return true;
    }

    // priority
    if off >= constants::TC_CTX_PRIORITY && access_end <= constants::TC_CTX_PRIORITY_END {
        return true;
    }

    // tc_index
    if off >= constants::TC_CTX_TC_INDEX && access_end <= constants::TC_CTX_TC_INDEX_END {
        return true;
    }

    // cb[5]
    if off >= constants::TC_CTX_CB_START && access_end <= constants::TC_CTX_CB_END {
        return true;
    }

    // tc_classid
    if off >= constants::TC_CTX_TC_CLASSID && access_end <= constants::TC_CTX_TC_CLASSID_END {
        return true;
    }

    false
}

/// Check if an XDP context field is writable.
pub fn is_xdp_md_field_writable(off: i16, size: MemSize) -> bool {
    let access_size: i16 = match size {
        MemSize::U8 => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    };
    let access_end = off + access_size;

    // rx_queue_index
    if off >= constants::XDP_CTX_RX_QUEUE_INDEX && access_end <= constants::XDP_CTX_RX_QUEUE_INDEX_END {
        return true;
    }

    // egress_ifindex
    if off >= constants::XDP_CTX_EGRESS_IFINDEX && access_end <= constants::XDP_CTX_EGRESS_IFINDEX_END {
        return true;
    }

    false
}

pub fn is_sock_addr_field_writable(off: i16, size: MemSize) -> bool {
    let access_size: i16 = match size {
        MemSize::U8 => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    };
    let access_end = off + access_size;

    // 1. user_family (0-4)
    if off >= constants::SOCK_ADDR_CTX_USER_FAMILY && access_end <= constants::SOCK_ADDR_CTX_USER_FAMILY_END {
        return size == MemSize::U32;
    }

    // 2. user_ip4 (4-8)
    if off >= constants::SOCK_ADDR_CTX_USER_IP4 && access_end <= constants::SOCK_ADDR_CTX_USER_IP4_END {
        return size == MemSize::U32;
    }

    // 3. user_ip6 (8-24)
    if off >= constants::SOCK_ADDR_CTX_USER_IP6_START && access_end <= constants::SOCK_ADDR_CTX_USER_IP6_END {
        // Alignment/Size check: usually U32 or U64 is expected here
        return match size {
            MemSize::U32 | MemSize::U64 => true,
            _ => false, 
        };
    }

    // 4. user_port (24-28)
    if off >= constants::SOCK_ADDR_CTX_USER_PORT && access_end <= constants::SOCK_ADDR_CTX_USER_PORT_END {
        return size == MemSize::U32;
    }

    false
}

/// Generic dispatch: is ctx field writable?
pub fn is_ctx_field_writable(prog_kind: ProgramKind, off: i16, size: MemSize) -> bool {
    let ctx_kind = prog_kind.context_kind();
    match ctx_kind {
        ContextKind::SkBuff => is_sk_buff_field_writable(off, size),
        ContextKind::XdpMd => is_xdp_md_field_writable(off, size),
        ContextKind::BpfSockAddr => is_sock_addr_field_writable(off, size),
        _ => false,
    }
}
