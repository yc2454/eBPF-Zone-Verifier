// src/analysis/reg_types.rs
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::frame_stack::FrameLevel;

pub const NUM_REGS: usize = 11; 

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum RegType {
    NotInit,        
    ScalarValue,    
    PtrToCtx,       
    PtrToStack { frame_level: FrameLevel },
    PtrToPacket,    
    PtrToPacketEnd, 
    PtrToPacketMeta,         
    PtrToMapObject { map_idx: usize }, 
    PtrToMapValueOrNull { id: u32, map_idx: usize }, 
    PtrToMapValue { id: u32, offset: Option<i64>, map_idx: usize },
    PtrToSocket { ref_id: Option<u32> },
    PtrToSocketOrNull { ref_id: Option<u32>  },
    PtrToSockCommon { ref_id: Option<u32>  },
    PtrToSockCommonOrNull { ref_id: Option<u32>  },
    PtrToTcpSock { id: Option<u32>  },
    PtrToTcpSockOrNull { id: Option<u32>  },
    PtrToBtfId { 
        type_name: &'static str,
        trusted: bool,
    },
    PtrToBtfIdOrNull { 
        id: u32,  // For null-tracking across branches
        type_name: &'static str,
        trusted: bool,
    },
    PtrToAllocMemOrNull {
    id: u32,
    mem_size: u64,
    },
    PtrToAllocMem {
        id: u32,
        mem_size: u64,
    },
}

impl Default for RegType {
    fn default() -> Self { RegType::NotInit }
}

impl RegType {
    pub fn is_pointer(self) -> bool {
        !self.is_scalar()
    }

    // Pointers that will experience null checks or the result of null checks
    pub fn is_null_checked(self) -> bool {
        use RegType::*;
        matches!(self, PtrToMapValueOrNull { .. } | 
                       PtrToSocketOrNull { .. } | 
                       PtrToSockCommonOrNull { .. } | 
                       PtrToTcpSockOrNull { .. } |
                       PtrToMapValue { .. } | 
                       PtrToSocket { .. } | 
                       PtrToSockCommon { .. } | 
                       PtrToTcpSock { .. })
    }

    pub fn is_scalar(self) -> bool {
        use RegType::*;
        matches!(self, ScalarValue | NotInit)
    }

    /// Returns the non-null version of a nullable pointer type
    pub fn to_non_null(&self) -> Option<RegType> {
        match *self {
            RegType::PtrToMapValueOrNull { id, map_idx } => {
                Some(RegType::PtrToMapValue { offset: Some(0), map_idx, id })
            }
            RegType::PtrToSocketOrNull { ref_id: id } => {
                Some(RegType::PtrToSocket { ref_id: id })
            }
            RegType::PtrToSockCommonOrNull { ref_id: id } => {
                Some(RegType::PtrToSockCommon { ref_id: id })
            }
            RegType::PtrToTcpSockOrNull { id } => {
                Some(RegType::PtrToTcpSock { id })
            }
            _ => None,
        }
    }
    
    /// Check if this is a nullable pointer type
    pub fn is_nullable(&self) -> bool {
        matches!(self, 
            RegType::PtrToMapValueOrNull { .. } |
            RegType::PtrToSocketOrNull { .. } |
            RegType::PtrToSockCommonOrNull { .. } |
            RegType::PtrToTcpSockOrNull { .. }
        )
    }

    pub fn get_ptr_offset(&self) -> Option<i64> {
        match *self {
            RegType::PtrToMapValue { offset, map_idx: _, .. } => offset,
            _ => None
        }
    }

    /// Helper to check strict type compatibility
    pub fn is_same_pointer_type(t1: &RegType, t2: &RegType) -> bool {
        // Discriminant check ensures we don't mix PtrToMap with PtrToStack.
        // For PtrToMap*, we also check if they point to the SAME map_idx.
        match (t1, t2) {
            (RegType::PtrToMapObject { map_idx: id1, .. }, RegType::PtrToMapObject { map_idx: id2, .. }) => 
                id1 == id2,
            (RegType::PtrToMapValue { map_idx: id1, .. }, RegType::PtrToMapValue { map_idx: id2, .. }) => 
                id1 == id2,
            _ => std::mem::discriminant(t1) == std::mem::discriminant(t2),
        }
    }

    pub fn is_packet_ptr(&self) -> bool {
        matches!(self, RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta)
    }

    /// Returns the ref_id if this type holds a reference
    pub fn get_ref_id(&self) -> Option<u32> {
        match *self {
            RegType::PtrToSocket { ref_id: id } |
            RegType::PtrToSocketOrNull { ref_id: id } |
            RegType::PtrToSockCommon { ref_id: id } |
            RegType::PtrToSockCommonOrNull { ref_id: id } |
            RegType::PtrToTcpSock { id } |
            RegType::PtrToTcpSockOrNull { id } => id,
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

/// Classify types into families. Pointer and pointer-or-null variants
/// of the same kind share a family (e.g. PtrToMapValue and PtrToMapValueOrNull).
pub fn type_family(ty: &RegType) -> u8 {
    use RegType::*;
    match ty {
        NotInit                                          => 0,
        ScalarValue                                      => 1,
        PtrToCtx                                         => 2,
        PtrToStack { .. }                                => 3,
        PtrToMapValue { .. } | PtrToMapValueOrNull { .. } => 4,
        PtrToMapObject { .. }                            => 5,
        PtrToPacket { .. }                               => 6,
        PtrToPacketEnd                                   => 7,
        PtrToPacketMeta                                  => 8,
        PtrToSocket { .. } | PtrToSocketOrNull { .. }    => 9,
        PtrToSockCommon { .. } | PtrToSockCommonOrNull { .. } => 10,
        PtrToTcpSock { .. } | PtrToTcpSockOrNull { .. }  => 11,
        PtrToBtfId { .. } | PtrToBtfIdOrNull { .. } => 12,
        PtrToAllocMem { .. } | PtrToAllocMemOrNull { .. } => 13,
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
