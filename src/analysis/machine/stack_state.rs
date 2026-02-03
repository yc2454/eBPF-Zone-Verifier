use crate::analysis::machine::reg_types::RegType;
use crate::zone::tnum::Tnum;
use std::collections::BTreeMap;

#[derive(Clone, Debug)]
struct ScalarBounds {
    pub min: i64,
    pub max: i64,
}

/// Snapshot of a register's abstract state at spill time
#[derive(Clone, Debug)]
pub struct SpilledReg {
    pub reg_type: RegType,
    pub tnum: Tnum,
    pub bounds: ScalarBounds,
}

#[derive(Clone, Debug)]
pub struct StackState {
    /// Spilled registers, keyed by stack offset
    pub slots: BTreeMap<i16, SpilledReg>,
}
