// src/analysis/transfer/alu/helpers.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::common::constants;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{
    assume_ge_imm, assume_le_imm, forget, get_distance_interval, get_interval,
};

/// Apply W32 truncation to a register's bounds.
/// If the current bounds exceed [0, 0xFFFFFFFF], widen to that range.
pub(crate) fn apply_w32_truncation(dbm: &mut Dbm, dst: Reg) {
    let (lo, hi) = get_interval(dbm, dst);

    let safe = lo >= 0 && hi <= 0xFFFFFFFF;

    if !safe {
        // Check if the lower 32 bits form a non-wrapping range.
        // This is true when lo and hi fall in the same 2^32 "page",
        // i.e. their upper 32 bits are identical.
        let tight = if lo != i64::MIN && hi != i64::MAX {
            let l_u = lo as u64;
            let h_u = hi as u64;
            (l_u >> 32) == (h_u >> 32)
        } else {
            false
        };

        if tight {
            let new_lo = (lo as u64 & 0xFFFFFFFF) as i64;
            let new_hi = (hi as u64 & 0xFFFFFFFF) as i64;
            forget(dbm, dst);
            assume_ge_imm(dbm, dst, new_lo);
            assume_le_imm(dbm, dst, new_hi);
        } else {
            forget(dbm, dst);
            assume_ge_imm(dbm, dst, 0);
            assume_le_imm(dbm, dst, 0xFFFFFFFF);
        }
    }
}

/// Tightens DBM bounds using information from Tnum.
pub(crate) fn sync_tnum_to_dbm(state: &mut State, reg: Reg) {
    let tnum = state.get_tnum(reg);
    let tnum_min = tnum.min_value();
    let tnum_max = tnum.max_value();

    // Only sync if tnum bounds fit in signed i64 range
    if tnum_max <= i64::MAX as u64 {
        let (dbm_lo, dbm_hi) = get_interval(&state.dbm, reg);

        // Tighten lower bound
        if dbm_lo == i64::MIN || (tnum_min as i64) > dbm_lo {
            assume_ge_imm(&mut state.dbm, reg, tnum_min as i64);
        }

        // Tighten upper bound
        if dbm_hi == i64::MAX || (tnum_max as i64) < dbm_hi {
            assume_le_imm(&mut state.dbm, reg, tnum_max as i64);
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
                let (_, hi) = get_distance_interval(&state.dbm, reg, *packet_start_reg);
                if hi != i64::MAX
                    && hi > constants::MAX_PACKET_OFF {
                        forget(&mut state.dbm, reg);
                    }
            }
        }
        RegType::PtrToPacketMeta => {
            let packet_start_reg_op = crate::analysis::machine::reg::REG_ENV
                .all()
                .iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacketMeta));
            if let Some(packet_start_reg) = packet_start_reg_op {
                let (_, hi) = get_distance_interval(&state.dbm, reg, *packet_start_reg);
                if hi != i64::MAX
                    && hi > constants::MAX_PACKET_OFF {
                        forget(&mut state.dbm, reg);
                    }
            }
        }
        _ => {}
    }
}
