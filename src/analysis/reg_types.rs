// src/analysis/reg_types.rs
use std::collections::BTreeMap;
use crate::domain::Reg;
use crate::ctx_model::MemRegionId;

pub const NUM_REGS: usize = 11; 

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum RegType {
    NotInit,        
    ScalarValue,    
    PtrToCtx,       
    PtrToStack,     
    PtrToPacket { id: u32, range: u64 },    
    PtrToPacketEnd, 
    PtrToMem { region: MemRegionId },           
    PtrToMapObject { map_idx: usize }, 
    PtrToMapValueOrNull { id: u32, map_idx: usize }, 
    PtrToMapValue { offset: Option<i64>, map_idx: usize },                                    
}

impl Default for RegType {
    fn default() -> Self { RegType::NotInit }
}

impl RegType {
    pub fn is_pointer(self) -> bool {
        use RegType::*;
        matches!(self, 
            PtrToCtx | PtrToStack | PtrToMapValue { .. } | 
            PtrToPacket { .. } | PtrToPacketEnd | 
            PtrToMem { .. } | PtrToMapValueOrNull { .. }
        )
    }
}

pub fn new_packet_id() -> u32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static PACKET_ID_COUNTER: AtomicU32 = AtomicU32::new(1);
    PACKET_ID_COUNTER.fetch_add(1, Ordering::SeqCst)
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
        if let Some(i) = crate::domain::reg_to_index(r) {
            self.regs[i]
        } else {
            RegType::NotInit 
        }
    }

    pub fn set(&mut self, r: Reg, ty: RegType) {
        if let Some(i) = crate::domain::reg_to_index(r) {
            self.regs[i] = ty;
        }
    }

    pub fn get_stack(&self, off: i16) -> RegType {
        *self.stack.get(&off).unwrap_or(&RegType::ScalarValue)
    }

    pub fn set_stack(&mut self, off: i16, ty: RegType) {
        self.stack.insert(off, ty);
    }
}
