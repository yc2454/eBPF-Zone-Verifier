// src/analysis/transfer/alu/helpers.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::common::constants;

/// Tightens DBM bounds using information from Tnum.
pub(crate) fn sync_tnum_to_dbm(state: &mut State, reg: Reg) {
    let tnum = state.get_tnum(reg);
    let tnum_min = tnum.min_value();
    let tnum_max = tnum.max_value();

    // Only sync if tnum bounds fit in signed i64 range
    if tnum_max <= i64::MAX as u64 {
        let (dbm_lo, dbm_hi) = state.domain.get_interval(reg);

        // Tighten lower bound
        if dbm_lo == i64::MIN || (tnum_min as i64) > dbm_lo {
            state.domain.assume_ge_imm(reg, tnum_min as i64);
        }

        // Tighten upper bound
        if dbm_hi == i64::MAX || (tnum_max as i64) < dbm_hi {
            state.domain.assume_le_imm(reg, tnum_max as i64);
        }
    }
}

/// Check pointer bounds after arithmetic operations.
pub(crate) fn check_ptr_bounds(state: &mut State, reg: Reg) {
    match state.types.get(reg) {
        RegType::PtrToPacket => {
            let packet_start_reg_op = crate::analysis::machine::reg::REG_ENV
                .all()
                .iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacket));
            if let Some(packet_start_reg) = packet_start_reg_op {
                let (_, hi) = state.domain.get_distance_interval(reg, *packet_start_reg);
                if hi != i64::MAX && hi > constants::MAX_PACKET_OFF {
                    state.domain.forget(reg);
                }
            }
        }
        RegType::PtrToPacketMeta => {
            let packet_start_reg_op = crate::analysis::machine::reg::REG_ENV
                .all()
                .iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacketMeta));
            if let Some(packet_start_reg) = packet_start_reg_op {
                let (_, hi) = state.domain.get_distance_interval(reg, *packet_start_reg);
                if hi != i64::MAX && hi > constants::MAX_PACKET_OFF {
                    state.domain.forget(reg);
                }
            }
        }
        _ => {}
    }
}
