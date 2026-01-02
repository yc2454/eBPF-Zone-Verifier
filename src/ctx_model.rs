// src/ctx_model.rs

use crate::ast::{MemSize, ProgramKind};

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
///
/// For now we hard-code just enough to understand:
///   w1 = *(u32 *)(r8 + 0x4c)
///   w6 = *(u32 *)(r8 + 0x8c)
pub fn classify_tc_ctx_field(off: i16, size: MemSize) -> Option<CtxFieldKind> {
    match (off, size) {
        // ctx + 0x4c: treat as "end" pointer / bound of CalicoMetaRegion.
        // This matches the pattern:
        //   r6 = *(ctx + 0x8c)    // start
        //   r1 = *(ctx + 0x4c)    // end
        //   r2 = r6; r2 += 4; if r2 <= r1 ... safe load from r6
        (0x4c, MemSize::U32) => Some(CtxFieldKind::MemEnd {
            region: MemRegionId::CalicoMetaRegion,
        }),

        // ctx + 0x8c: treat as pointer into the same region.
        (0x8c, MemSize::U32) => Some(CtxFieldKind::PtrToMem {
            region: MemRegionId::CalicoMetaRegion,
        }),

        // Everything else: for now, we consider it scalar.
        // You can expand this table as you learn more of __sk_buff / Calico layout.
        _ => Some(CtxFieldKind::Scalar),
    }
}

/// Generic dispatch based on program kind, so exec.rs can just call one function.
/// You can extend this once you add XDP, cgroup, etc.
pub fn classify_ctx_field(
    prog_kind: ProgramKind,
    off: i16,
    size: MemSize,
) -> Option<CtxFieldKind> {
    match prog_kind {
        ProgramKind::Tc => classify_tc_ctx_field(off, size),
        ProgramKind::Xdp => {
            // For now, no special mapping for XDP; everything is scalar.
            // Later you can add a `classify_xdp_ctx_field` similar to TC.
            Some(CtxFieldKind::Scalar)
        }
    }
}
