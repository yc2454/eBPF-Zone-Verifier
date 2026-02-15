// src/analysis/transfer/alu/helpers.rs

use crate::analysis::machine::state::State;
use crate::analysis::machine::reg::Reg;
use crate::zone::domain::{forget, get_bounds, assume_ge_const, assume_le_const, get_relative_bound};
use crate::zone::dbm::{Dbm};
use crate::analysis::machine::reg_types::{RegType};
use crate::common::constants;

/// Apply W32 truncation to a register's bounds.
/// If the current bounds exceed [0, 0xFFFFFFFF], widen to that range.
pub(crate) fn apply_w32_truncation(dbm: &mut Dbm, dst: Reg) {
    let (lo, hi) = get_bounds(dbm, dst);

    let safe = match (lo, hi) {
        (Some(l), Some(h)) => l >= 0 && h <= 0xFFFFFFFF,
        _ => false,
    };

    if !safe {
        // Check if the lower 32 bits form a non-wrapping range.
        // This is true when lo and hi fall in the same 2^32 "page",
        // i.e. their upper 32 bits are identical.
        let tight = match (lo, hi) {
            (Some(l), Some(h)) => {
                let l_u = l as u64;
                let h_u = h as u64;
                (l_u >> 32) == (h_u >> 32)
            }
            _ => false,
        };

        if tight {
            let new_lo = (lo.unwrap() as u64 & 0xFFFFFFFF) as i64;
            let new_hi = (hi.unwrap() as u64 & 0xFFFFFFFF) as i64;
            forget(dbm, dst);
            assume_ge_const(dbm, dst, new_lo);
            assume_le_const(dbm, dst, new_hi);
        } else {
            forget(dbm, dst);
            assume_ge_const(dbm, dst, 0);
            assume_le_const(dbm, dst, 0xFFFFFFFF);
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
        let (dbm_lo, dbm_hi) = get_bounds(&state.dbm, reg);
        
        // Tighten lower bound
        match dbm_lo {
            None => assume_ge_const(&mut state.dbm, reg, tnum_min as i64),
            Some(l) if (tnum_min as i64) > l => {
                assume_ge_const(&mut state.dbm, reg, tnum_min as i64)
            }
            _ => {}
        }
        
        // Tighten upper bound
        match dbm_hi {
            None => assume_le_const(&mut state.dbm, reg, tnum_max as i64),
            Some(h) if (tnum_max as i64) < h => {
                assume_le_const(&mut state.dbm, reg, tnum_max as i64)
            }
            _ => {}
        }
    }
}

/// Check pointer bounds after arithmetic operations.
pub(crate) fn check_ptr_bounds(
    state: &mut State,
    reg: Reg,
) { 
    match state.types.get(reg) {
        RegType::PtrToPacket { .. } => {
            let packet_start_reg_op = crate::analysis::machine::reg::REG_ENV.all().iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacket));
            if let Some(packet_start_reg) = packet_start_reg_op {
                if let (Some(_), Some(packet_offset)) = get_relative_bound(&state.dbm, reg, *packet_start_reg) {
                    if packet_offset > constants::MAX_PACKET_OFF as i64 {
                        forget(&mut state.dbm, reg);
                    }
                }
            }
        }
        RegType::PtrToPacketMeta { .. } => {
            let packet_start_reg_op = crate::analysis::machine::reg::REG_ENV.all().iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacketMeta));
            if let Some(packet_start_reg) = packet_start_reg_op {
                if let (Some(_), Some(packet_offset)) = get_relative_bound(&state.dbm, reg, *packet_start_reg) {
                    if packet_offset > constants::MAX_PACKET_OFF as i64 {
                        forget(&mut state.dbm, reg);
                    }
                }
            }
        }
        _ => {}
    }
}
