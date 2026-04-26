// src/analysis/reg_types.rs
use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::reg::Reg;

pub const NUM_REGS: usize = 11;

/// Orthogonal pointer-type flags, modeled after the kernel's `bpf_type_flag`.
///
/// Kernel layout packs these into the high bits of `enum bpf_reg_type`; we keep
/// them in a dedicated field on variants that need them. New variants added by
/// later phases (dynptr, arena, refcounted kptrs, …) grow a `flags` field on
/// demand — not every variant needs one.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct PtrFlags(u16);

impl PtrFlags {
    pub const TRUSTED: PtrFlags = PtrFlags(1 << 0);
    pub const UNTRUSTED: PtrFlags = PtrFlags(1 << 1);
    pub const RCU: PtrFlags = PtrFlags(1 << 2);
    pub const RDONLY: PtrFlags = PtrFlags(1 << 3);
    pub const PERCPU: PtrFlags = PtrFlags(1 << 4);
    pub const MEM_ALLOC: PtrFlags = PtrFlags(1 << 5);
    pub const NON_OWN_REF: PtrFlags = PtrFlags(1 << 6);

    pub const fn empty() -> Self {
        PtrFlags(0)
    }

    pub const fn contains(self, other: PtrFlags) -> bool {
        (self.0 & other.0) == other.0
    }

    pub const fn union(self, other: PtrFlags) -> Self {
        PtrFlags(self.0 | other.0)
    }

    pub const fn difference(self, other: PtrFlags) -> Self {
        PtrFlags(self.0 & !other.0)
    }

    pub const fn bits(self) -> u16 {
        self.0
    }
}

impl std::ops::BitOr for PtrFlags {
    type Output = PtrFlags;
    fn bitor(self, rhs: PtrFlags) -> PtrFlags {
        self.union(rhs)
    }
}

impl std::ops::BitOrAssign for PtrFlags {
    fn bitor_assign(&mut self, rhs: PtrFlags) {
        self.0 |= rhs.0;
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub enum RegType {
    #[default]
    NotInit,
    ScalarValue,
    PtrToCtx,
    PtrToStack {
        frame_level: FrameLevel,
    },
    PtrToPacket,
    PtrToPacketEnd,
    PtrToPacketMeta,
    PtrToMapObject {
        map_idx: usize,
    },
    PtrToMapValueOrNull {
        id: u32,
        map_idx: usize,
    },
    PtrToMapValue {
        id: u32,
        offset: Option<i64>,
        map_idx: usize,
    },
    PtrToSocket {
        ref_id: Option<u32>,
    },
    PtrToSocketOrNull {
        ref_id: Option<u32>,
    },
    PtrToSockCommon {
        ref_id: Option<u32>,
    },
    PtrToSockCommonOrNull {
        ref_id: Option<u32>,
    },
    PtrToTcpSock {
        id: Option<u32>,
    },
    PtrToTcpSockOrNull {
        id: Option<u32>,
    },
    PtrToBtfId {
        type_name: &'static str,
        flags: PtrFlags,
    },
    PtrToBtfIdOrNull {
        id: u32, // For null-tracking across branches
        type_name: &'static str,
        flags: PtrFlags,
    },
    PtrToAllocMemOrNull {
        id: u32,
        mem_size: u64,
    },
    PtrToAllocMem {
        id: u32,
        mem_size: u64,
    },
    /// Refcounted pointer to a `struct bpf_cpumask` (W5.3). Mirrors
    /// `PtrToSocket` ref-tracking: `bpf_cpumask_create` mints a fresh
    /// `ref_id` on the OrNull form; null-check refinement promotes to
    /// the non-null form on the success branch and drops the ref on
    /// the null branch; `bpf_cpumask_release` consumes the ref.
    PtrToCpumask {
        ref_id: Option<u32>,
    },
    PtrToCpumaskOrNull {
        ref_id: Option<u32>,
    },
    /// Pointer to a callback subprogram, produced by `LD_IMM64 BPF_PSEUDO_FUNC`
    /// (W3.4a). Consumed by callback-taking helpers (`bpf_loop`,
    /// `bpf_for_each_map_elem`, `bpf_timer_set_callback`) and by the
    /// `bpf_set_exception_callback` kfunc to register an exception handler.
    /// Not dereferenceable as data; arithmetic on it produces a scalar.
    PtrToCallback {
        subprog_pc: u32,
    },
}

impl RegType {
    pub fn is_pointer(self) -> bool {
        !self.is_scalar()
    }

    // Pointers that will experience null checks or the result of null checks
    pub fn is_null_checked(self) -> bool {
        use RegType::*;
        matches!(
            self,
            PtrToMapValueOrNull { .. }
                | PtrToSocketOrNull { .. }
                | PtrToSockCommonOrNull { .. }
                | PtrToTcpSockOrNull { .. }
                | PtrToCpumaskOrNull { .. }
                | PtrToMapValue { .. }
                | PtrToSocket { .. }
                | PtrToSockCommon { .. }
                | PtrToTcpSock { .. }
                | PtrToCpumask { .. }
        )
    }

    pub fn is_scalar(self) -> bool {
        use RegType::*;
        matches!(self, ScalarValue | NotInit)
    }

    /// Returns the non-null version of a nullable pointer type
    pub fn to_non_null(&self) -> Option<RegType> {
        match *self {
            RegType::PtrToMapValueOrNull { id, map_idx } => Some(RegType::PtrToMapValue {
                offset: Some(0),
                map_idx,
                id,
            }),
            RegType::PtrToSocketOrNull { ref_id: id } => Some(RegType::PtrToSocket { ref_id: id }),
            RegType::PtrToSockCommonOrNull { ref_id: id } => {
                Some(RegType::PtrToSockCommon { ref_id: id })
            }
            RegType::PtrToTcpSockOrNull { id } => Some(RegType::PtrToTcpSock { id }),
            RegType::PtrToCpumaskOrNull { ref_id } => Some(RegType::PtrToCpumask { ref_id }),
            _ => None,
        }
    }

    /// Check if this is a nullable pointer type
    pub fn is_nullable(&self) -> bool {
        matches!(
            self,
            RegType::PtrToMapValueOrNull { .. }
                | RegType::PtrToSocketOrNull { .. }
                | RegType::PtrToSockCommonOrNull { .. }
                | RegType::PtrToTcpSockOrNull { .. }
                | RegType::PtrToCpumaskOrNull { .. }
        )
    }

    pub fn get_ptr_offset(&self) -> Option<i64> {
        match *self {
            RegType::PtrToMapValue {
                offset, map_idx: _, ..
            } => offset,
            _ => None,
        }
    }

    /// Helper to check strict type compatibility
    pub fn is_same_pointer_type(t1: &RegType, t2: &RegType) -> bool {
        // Discriminant check ensures we don't mix PtrToMap with PtrToStack.
        // For PtrToMap*, we also check if they point to the SAME map_idx.
        match (t1, t2) {
            (
                RegType::PtrToMapObject { map_idx: id1, .. },
                RegType::PtrToMapObject { map_idx: id2, .. },
            ) => id1 == id2,
            (
                RegType::PtrToMapValue { map_idx: id1, .. },
                RegType::PtrToMapValue { map_idx: id2, .. },
            ) => id1 == id2,
            _ => std::mem::discriminant(t1) == std::mem::discriminant(t2),
        }
    }

    pub fn is_packet_ptr(&self) -> bool {
        matches!(
            self,
            RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta
        )
    }

    /// Returns the flag set for variants that carry one, else empty.
    pub fn ptr_flags(&self) -> PtrFlags {
        match *self {
            RegType::PtrToBtfId { flags, .. } | RegType::PtrToBtfIdOrNull { flags, .. } => flags,
            _ => PtrFlags::empty(),
        }
    }

    /// True when the pointer is known-trusted (kfunc return, ctx trusted field, …).
    /// Preserves the meaning of the former `trusted: bool` field.
    pub fn is_trusted(&self) -> bool {
        self.ptr_flags().contains(PtrFlags::TRUSTED)
    }

    /// True when the pointer is known-untrusted (e.g. result of a pointer walk).
    pub fn is_untrusted(&self) -> bool {
        self.ptr_flags().contains(PtrFlags::UNTRUSTED)
    }

    /// Returns the ref_id if this type holds a reference
    pub fn get_ref_id(&self) -> Option<u32> {
        match *self {
            RegType::PtrToSocket { ref_id: id }
            | RegType::PtrToSocketOrNull { ref_id: id }
            | RegType::PtrToSockCommon { ref_id: id }
            | RegType::PtrToSockCommonOrNull { ref_id: id }
            | RegType::PtrToTcpSock { id }
            | RegType::PtrToTcpSockOrNull { id }
            | RegType::PtrToCpumask { ref_id: id }
            | RegType::PtrToCpumaskOrNull { ref_id: id } => id,
            _ => None,
        }
    }
}

// For general pointers
pub fn new_ptr_id() -> u32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static PACKET_ID_COUNTER: AtomicU32 = AtomicU32::new(1);
    PACKET_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

// For references (return values of special helper functions)
pub fn new_ref_id() -> u32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static REF_ID_COUNTER: AtomicU32 = AtomicU32::new(1);
    REF_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// Fresh identity token for a scalar value. Two registers/slots that share
/// an id represent the same underlying unknown scalar, so refining one
/// (e.g. via a conditional) can be propagated to the others.
pub fn new_scalar_id() -> u32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static SCALAR_ID_COUNTER: AtomicU32 = AtomicU32::new(1);
    SCALAR_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// Fresh identity token for an open-coded iterator (Phase 3 W3.2b).
/// Minted at `*_new` time and stored on the iterator's stack slot.
/// Subsumption (W3.2c) matches states by this id to recognize "same
/// iterator loop" across revisits.
pub fn new_iter_id() -> u32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static ITER_ID_COUNTER: AtomicU32 = AtomicU32::new(1);
    ITER_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
}

/// Classify types into families. Pointer and pointer-or-null variants
/// of the same kind share a family (e.g. PtrToMapValue and PtrToMapValueOrNull).
pub fn type_family(ty: &RegType) -> u8 {
    use RegType::*;
    match ty {
        NotInit => 0,
        ScalarValue => 1,
        PtrToCtx => 2,
        PtrToStack { .. } => 3,
        PtrToMapValue { .. } | PtrToMapValueOrNull { .. } => 4,
        PtrToMapObject { .. } => 5,
        PtrToPacket => 6,
        PtrToPacketEnd => 7,
        PtrToPacketMeta => 8,
        PtrToSocket { .. } | PtrToSocketOrNull { .. } => 9,
        PtrToSockCommon { .. } | PtrToSockCommonOrNull { .. } => 10,
        PtrToTcpSock { .. } | PtrToTcpSockOrNull { .. } => 11,
        PtrToBtfId { .. } | PtrToBtfIdOrNull { .. } => 12,
        PtrToAllocMem { .. } | PtrToAllocMemOrNull { .. } => 13,
        PtrToCallback { .. } => 14,
        PtrToCpumask { .. } | PtrToCpumaskOrNull { .. } => 15,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeState {
    pub regs: [RegType; NUM_REGS],
}

impl TypeState {
    pub fn new_not_init() -> Self {
        Self {
            regs: [RegType::NotInit; NUM_REGS],
        }
    }

    pub fn get(&self, r: Reg) -> RegType {
        if let Some(i) = crate::analysis::machine::reg::reg_to_index(r) {
            self.regs[i]
        } else {
            RegType::NotInit
        }
    }

    pub fn set(&mut self, r: Reg, ty: RegType) {
        if let Some(i) = crate::analysis::machine::reg::reg_to_index(r) {
            self.regs[i] = ty;
        }
    }

    pub fn reg_types_str(&self) -> String {
        let mut s = String::new();
        for (i, ty) in self.regs.iter().enumerate() {
            s.push_str(&format!("R{}: {:?} ", i, ty));
        }
        s
    }
}

impl Default for TypeState {
    fn default() -> Self {
        Self::new_not_init()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ptr_flags_empty_and_contains() {
        let e = PtrFlags::empty();
        assert!(!e.contains(PtrFlags::TRUSTED));
        assert!(!e.contains(PtrFlags::UNTRUSTED));
        assert_eq!(e.bits(), 0);
    }

    #[test]
    fn ptr_flags_union_and_contains() {
        let f = PtrFlags::TRUSTED | PtrFlags::RCU;
        assert!(f.contains(PtrFlags::TRUSTED));
        assert!(f.contains(PtrFlags::RCU));
        assert!(!f.contains(PtrFlags::UNTRUSTED));
        assert!(f.contains(PtrFlags::TRUSTED | PtrFlags::RCU));
    }

    #[test]
    fn ptr_flags_difference() {
        let f = PtrFlags::TRUSTED | PtrFlags::RCU;
        let d = f.difference(PtrFlags::RCU);
        assert!(d.contains(PtrFlags::TRUSTED));
        assert!(!d.contains(PtrFlags::RCU));
    }

    #[test]
    fn reg_type_is_trusted_matches_flag() {
        let trusted = RegType::PtrToBtfId {
            type_name: "x",
            flags: PtrFlags::TRUSTED,
        };
        let untrusted = RegType::PtrToBtfId {
            type_name: "x",
            flags: PtrFlags::UNTRUSTED,
        };
        let empty = RegType::PtrToBtfId {
            type_name: "x",
            flags: PtrFlags::empty(),
        };
        assert!(trusted.is_trusted());
        assert!(!trusted.is_untrusted());
        assert!(untrusted.is_untrusted());
        assert!(!untrusted.is_trusted());
        assert!(!empty.is_trusted());
        assert!(!empty.is_untrusted());
    }

    #[test]
    fn reg_type_is_trusted_false_for_non_btf_variants() {
        assert!(!RegType::ScalarValue.is_trusted());
        assert!(!RegType::PtrToCtx.is_trusted());
        assert!(!RegType::PtrToMapValue {
            id: 1,
            offset: None,
            map_idx: 0,
        }
        .is_trusted());
    }

    #[test]
    fn reg_type_equality_distinguishes_flags() {
        let a = RegType::PtrToBtfId {
            type_name: "x",
            flags: PtrFlags::TRUSTED,
        };
        let b = RegType::PtrToBtfId {
            type_name: "x",
            flags: PtrFlags::UNTRUSTED,
        };
        assert_ne!(a, b, "flags must participate in PartialEq to preserve old trusted-bool semantics");
    }
}
