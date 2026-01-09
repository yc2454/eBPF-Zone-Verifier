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
    PtrToPacketMeta,
    PtrToPacketEnd, 
    PtrToMem { region: MemRegionId },       
    Unknown,        
    PtrToMapObject { map_idx: usize }, 
    PtrToMapValueOrNull { id: u32, map_idx: usize }, 
    PtrToMapValue { offset: Option<i64>, map_idx: usize },   
    PtrToMapKey,                                    
}

impl Default for RegType {
    fn default() -> Self { RegType::NotInit }
}

impl RegType {
    pub fn is_pointer(self) -> bool {
        use RegType::*;
        matches!(self, 
            PtrToCtx | PtrToStack | PtrToMapValue { .. } | PtrToMapKey | 
            PtrToPacket { .. } | PtrToPacketMeta | PtrToPacketEnd | 
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

    // --- Join Logic ---

    /// Merges `other` into `self`. Returns true if `self` changed.
    /// This is the Lattice Join operation (Least Upper Bound).
    pub fn join_in_place(&mut self, other: &TypeState) -> bool {
        let mut changed = false;

        // 1. Join Registers
        for i in 0..NUM_REGS {
            let t1 = self.regs[i];
            let t2 = other.regs[i];
            let joined = Self::merge_types(t1, t2);
            if joined != t1 {
                self.regs[i] = joined;
                changed = true;
            }
        }

        // 2. Join Stack
        // We iterate over keys present in EITHER map.
        // A stack slot is only valid if it is valid in BOTH paths (intersection of validity),
        // but the type itself is the union of the two valid types.
        let mut all_keys: Vec<i16> = self.stack.keys().cloned().collect();
        for k in other.stack.keys() {
            if !self.stack.contains_key(k) {
                all_keys.push(*k);
            }
        }

        for k in all_keys {
            let t1 = *self.stack.get(&k).unwrap_or(&RegType::NotInit);
            let t2 = *other.stack.get(&k).unwrap_or(&RegType::NotInit);
            
            let joined = Self::merge_types(t1, t2);

            if joined == RegType::NotInit {
                // If result is NotInit (incompatible or empty), remove it from the stack
                if self.stack.contains_key(&k) {
                    self.stack.remove(&k);
                    changed = true;
                }
            } else {
                // Update/Insert the joined type
                if let Some(existing) = self.stack.get(&k) {
                    if *existing != joined {
                        self.stack.insert(k, joined);
                        changed = true;
                    }
                } else {
                    self.stack.insert(k, joined);
                    changed = true;
                }
            }
        }
        
        changed
    }

    /// Helper: Merges two single types.
    /// Rules:
    /// - Same type -> Same type
    /// - One is NotInit -> The other (Initialization wins)
    /// - One is Scalar -> Scalar (Safety downgrade)
    /// - Ptr vs Ptr -> Specific merging (e.g. min range) or Scalar if incompatible
    fn merge_types(t1: RegType, t2: RegType) -> RegType {
        use RegType::*;
        
        if t1 == t2 { return t1; }

        // Initialization Logic
        if let NotInit = t1 { return t2; }
        if let NotInit = t2 { return t1; }

        // Scalar dominates (Downgrade to safe scalar if conflict)
        if let ScalarValue = t1 { return ScalarValue; }
        if let ScalarValue = t2 { return ScalarValue; }

        match (t1, t2) {
            // --- Packet Pointers ---
            // We take the MINIMUM range to be safe. 
            // If path A has range 10 and path B has range 20, the joined path only guarantees 10.
            (PtrToPacket { id: _, range: r1 }, PtrToPacket { id: id2, range: r2 }) => 
                PtrToPacket { id: id2, range: r1.min(r2) }, 

            (PtrToPacket { id, range }, _) => PtrToPacket { id, range },
            (_, PtrToPacket { id, range }) => PtrToPacket { id, range },

            // --- Map Pointers ---
            (PtrToMapValue { offset: o1, map_idx: m1 }, PtrToMapValue { offset: o2, map_idx: m2 }) => {
                if m1 == m2 {
                    // If offsets differ, we lose offset precision (Unknown Offset)
                    let new_off = if o1 == o2 { o1 } else { None };
                    PtrToMapValue { offset: new_off, map_idx: m1 }
                } else {
                    // Different maps? Incompatible.
                    ScalarValue
                }
            },

            // Nullable Pointers
            (PtrToMapValueOrNull { map_idx, id }, PtrToMapValueOrNull { .. }) => 
                PtrToMapValueOrNull { map_idx, id },

            // Safe vs Nullable -> Downgrade to Nullable (Must check again)
            (PtrToMapValue { map_idx, .. }, PtrToMapValueOrNull { id, .. }) => 
                PtrToMapValueOrNull { map_idx, id },
            (PtrToMapValueOrNull { map_idx, id }, PtrToMapValue { .. }) => 
                PtrToMapValueOrNull { map_idx, id },

            // --- Other Pointers ---
            (PtrToStack, PtrToStack) => PtrToStack,
            (PtrToCtx, PtrToCtx) => PtrToCtx,
            (PtrToPacketEnd, PtrToPacketEnd) => PtrToPacketEnd,
            (PtrToMem { region: r1 }, PtrToMem { region: r2 }) if r1 == r2 => t1,

            // Default: Incompatible pointers become Scalar
            _ => ScalarValue,
        }
    }
}
