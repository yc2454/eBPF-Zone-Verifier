// src/analysis/reg_types.rs
use std::collections::{BTreeMap};
use crate::zone::domain::Reg;
use crate::analysis::ctx_model::MemRegionId;

pub const NUM_REGS: usize = 11; 

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum RegType {
    NotInit,        
    ScalarValue,    
    PtrToCtx,       
    PtrToStack { offset: Option<i64> },  
    PtrToPacket { 
        id: u32,
        is_base: bool,
    },    
    PtrToPacketEnd, 
    PtrToPacketMeta,
    PtrToMem { region: MemRegionId, range: u64 },           
    PtrToMapObject { map_idx: usize }, 
    PtrToMapValueOrNull { id: u32, map_idx: usize }, 
    PtrToMapValue { id: u32, offset: Option<i64>, map_idx: usize },
    PtrToSocket { id: u32 },
    PtrToSocketOrNull { id: u32 },
    PtrToSockCommon { id: u32 },
    PtrToSockCommonOrNull { id: u32 },
    PtrToTcpSock { id: u32 },
    PtrToTcpSockOrNull { id: u32 },
}

impl Default for RegType {
    fn default() -> Self { RegType::NotInit }
}

impl RegType {
    pub fn is_pointer(self) -> bool {
        use RegType::*;
        matches!(self, 
            PtrToCtx | PtrToStack { .. } | PtrToMapValue { .. } | 
            PtrToPacket { .. } | PtrToPacketEnd | 
            PtrToMem { .. } | PtrToMapValueOrNull { .. }
        )
    }

    pub fn is_scalar(self) -> bool {
        use RegType::*;
        matches!(self, ScalarValue | NotInit)
    }

    pub fn is_init(self) -> bool {
        !matches!(self, RegType::NotInit)
    }

    /// Returns the non-null version of a nullable pointer type
    pub fn to_non_null(&self) -> Option<RegType> {
        match *self {
            RegType::PtrToMapValueOrNull { id, map_idx } => {
                Some(RegType::PtrToMapValue { offset: Some(0), map_idx, id })
            }
            RegType::PtrToSocketOrNull { id } => {
                Some(RegType::PtrToSocket { id })
            }
            RegType::PtrToSockCommonOrNull { id } => {
                Some(RegType::PtrToSockCommon { id })
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

    pub fn get_offset(&self) -> Option<i64> {
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

    /// Returns the ref_id if this type holds a reference
    pub fn get_ref_id(&self) -> Option<u32> {
        match *self {
            RegType::PtrToSocket { id } |
            RegType::PtrToSocketOrNull { id } |
            RegType::PtrToSockCommon { id } |
            RegType::PtrToSockCommonOrNull { id } |
            RegType::PtrToTcpSock { id } |
            RegType::PtrToTcpSockOrNull { id } => Some(id),
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeState {
    pub regs: [RegType; NUM_REGS],
    pub stack: BTreeMap<i16, RegType>,
}

impl TypeState {
    pub fn new_not_init() -> Self {
        Self {
            regs: [RegType::NotInit; NUM_REGS],
            stack: BTreeMap::new(),
        }
    }

    pub fn get(&self, r: Reg) -> RegType {
        if let Some(i) = crate::zone::domain::reg_to_index(r) {
            self.regs[i]
        } else {
            RegType::NotInit 
        }
    }

    pub fn set(&mut self, r: Reg, ty: RegType) {
        if let Some(i) = crate::zone::domain::reg_to_index(r) {
            self.regs[i] = ty;
        }
    }

    pub fn get_stack(&self, off: i16) -> RegType {
        *self.stack.get(&off).unwrap_or(&RegType::ScalarValue)
    }

    pub fn set_stack(&mut self, off: i16, ty: RegType) {
        self.stack.insert(off, ty);
    }

    pub fn print(&self) {
        println!("Register Types:");
        for (i, ty) in self.regs.iter().enumerate() {
            print!("  R{}: {:?} ", i, ty);
        }
        println!();
    }

    pub fn reg_types_str(&self) -> String {
        let mut s = String::new();
        for (i, ty) in self.regs.iter().enumerate() {
            s.push_str(&format!("R{}: {:?} ", i, ty));
        }
        s
    }
}
