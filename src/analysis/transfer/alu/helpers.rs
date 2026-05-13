// src/analysis/transfer/alu/helpers.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::common::constants;
use crate::refinement::symbolic::RegBounds;

/// Build a [`RegBounds`] snapshot for `reg` from the current numeric
/// domain. Used by BCF transfer-function mirrors to materialize register
/// expressions in kernel-shape (with the right `fit_u32` / `fit_s32`
/// fast-paths).
///
/// Callers typically snapshot **before** the abstract-domain op runs (for
/// the dst/src expressions that go INTO the ALU op) and then take a
/// second snapshot **after** the op (for the post-narrowness flags
/// `op_u32` / `op_s32`). Mirrors kernel's pattern at verifier.c:16178-16181.
pub(crate) fn bcf_reg_bounds(state: &State, reg: Reg) -> RegBounds {
    let (smin, smax) = state.domain.get_interval(reg);
    let (mut s32_min, mut s32_max) = state.domain.get_s32_bounds(reg);
    let (mut u32_min, mut u32_max) = state.domain.get_u32_bounds(reg);
    let const_val = state.domain.get_fixed_value(reg).map(|v| v as u64);
    // Tighten the 32-bit bounds from the 64-bit interval when the
    // abstract domain hasn't propagated them itself (Zone mode doesn't
    // always sync s32/u32 fields for pointer regs). The kernel's
    // bcf_reg_expr cares about fit_u32/fit_s32 to choose 32- vs 64-bit
    // BCF ops; failing to tighten here forces us into 64-bit ops even
    // when the value provably fits, which causes structural divergence
    // from the kernel's DAG.
    if (s32_min, s32_max) == (i32::MIN, i32::MAX)
        && smin >= i32::MIN as i64
        && smax <= i32::MAX as i64
    {
        s32_min = smin as i32;
        s32_max = smax as i32;
    }
    if (u32_min, u32_max) == (0, u32::MAX)
        && smin >= 0
        && smax <= u32::MAX as i64
    {
        u32_min = smin as u32;
        u32_max = smax as u32;
    }
    RegBounds {
        const_val,
        smin,
        smax,
        s32_min,
        s32_max,
        u32_min,
        u32_max,
    }
}

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
