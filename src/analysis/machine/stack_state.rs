use crate::analysis::machine::reg_types::RegType;
use crate::zone::tnum::Tnum;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarBounds {
    pub min: i64,
    pub max: i64,
}

/// Snapshot of a register's abstract state at spill time
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpilledReg {
    pub reg_type: RegType,
    pub tnum: Tnum,
    pub bounds: ScalarBounds,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StackState {
    /// Spilled registers, keyed by stack offset
    pub slots: BTreeMap<i16, SpilledReg>,
}

impl std::fmt::Display for StackState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut entries: Vec<String> = Vec::new();
        for (offset, spilled) in &self.slots {
            entries.push(format!("offset {}: type={:?}, bounds=[{}, {}]", 
                offset, spilled.reg_type, spilled.bounds.min, spilled.bounds.max));
        }
        write!(f, "StackState {{\n  {}\n}}", entries.join("\n  "))
    }
}

impl StackState {
    pub fn new() -> Self {
        Self {
            slots: BTreeMap::new(),
        }
    }

    pub fn invalidate_ref(&mut self, id: u32) {
        for (_, spilled) in self.slots.iter_mut() {
            if spilled.reg_type.get_ref_id() == Some(id) {
                spilled.reg_type = RegType::ScalarValue;
            }
        }
    }

    pub fn is_slot_initialized(&self, offset: i16) -> bool {
        self.slots.contains_key(&offset)
    }

    pub fn get_slot_type(&self, offset: i16) -> RegType {
        if let Some(spilled) = self.slots.get(&offset) {
            spilled.reg_type
        } else {
            RegType::ScalarValue
        }
    }

    pub fn get_slot(&self, offset: i16) -> Option<&SpilledReg> {
        self.slots.get(&offset)
    }

    pub fn slot_offsets(&self) -> Vec<i16> {
        self.slots.keys().cloned().collect()
    }

    pub fn set_slot_type(&mut self, offset: i16, reg_type: RegType) {
        if let Some(spilled) = self.slots.get_mut(&offset) {
            spilled.reg_type = reg_type;
        } else {
            self.slots.insert(offset, SpilledReg {
                reg_type,
                tnum: Tnum::unknown(),
                bounds: ScalarBounds { min: i64::MIN, max: i64::MAX },
            });
        }
    }

    pub fn invalidate_packet_pointers(&mut self) {
        for (_, spilled) in self.slots.iter_mut() {
            match spilled.reg_type {
                RegType::PtrToPacket { .. } => {
                    spilled.reg_type = RegType::ScalarValue;
                }
                _ => {}
            }
        }
    }

    pub fn insert(&mut self, offset: i16, spilled: SpilledReg) {
        self.slots.insert(offset, spilled);
    }

    pub fn clear_slot(&mut self, offset: i16) {
        self.slots.remove(&offset);
    }

    pub fn invalidate_slot(&mut self, offset: i16) {
        self.slots.insert(offset, SpilledReg {
                reg_type: RegType::ScalarValue,
                tnum: Tnum::unknown(),
                bounds: ScalarBounds { min: i64::MIN, max: i64::MAX },
            });
    }
}
