// src/analysis/transfer/branch/outcome.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Operand, Width};

/// Check if a branch condition can be determined at analysis time.
/// Returns:
///   Some(true)  - condition is ALWAYS true (only then-branch reachable)
///   Some(false) - condition is ALWAYS false (only else-branch reachable)
///   None        - condition could go either way
pub(crate) fn condition_outcome(
    state: &State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: &Operand,
) -> Option<bool> {
    // Special case for NULL check
    if matches!(op, CmpOp::Eq | CmpOp::Ne) && matches!(right, Operand::Imm(0)) {
        let left_ty = state.types.get(left);
        if left_ty.is_null_checked() && !left_ty.is_nullable() {
            return Some(matches!(op, CmpOp::Ne));
        }
    }

    // Don't eliminate paths based on pointer comparisons
    if state.types.get(left).is_pointer() {
        return None;
    }

    // Get combined bounds from tnum and DBM
    let (min, max) = get_combined_bounds(state, left, width)?;

    match right {
        Operand::Imm(imm) => {
            let imm_val = match width {
                Width::W32 => (*imm as u32) as u64,
                Width::W64 => *imm as u64,
            };

            match op {
                CmpOp::ULt => {
                    if max < imm_val {
                        Some(true)
                    }
                    // always true
                    else if min >= imm_val {
                        Some(false)
                    }
                    // always false
                    else {
                        None
                    }
                }
                CmpOp::UGe => {
                    if min >= imm_val {
                        Some(true)
                    } else if max < imm_val {
                        Some(false)
                    } else {
                        None
                    }
                }
                CmpOp::ULe => {
                    if max <= imm_val {
                        Some(true)
                    } else if min > imm_val {
                        Some(false)
                    } else {
                        None
                    }
                }
                CmpOp::UGt => {
                    if min > imm_val {
                        Some(true)
                    } else if max <= imm_val {
                        Some(false)
                    } else {
                        None
                    }
                }
                CmpOp::Eq => {
                    if min == max && min == imm_val {
                        Some(true)
                    } else if min > imm_val || max < imm_val {
                        Some(false)
                    } else {
                        None
                    }
                }
                CmpOp::Ne => {
                    if min > imm_val || max < imm_val {
                        Some(true)
                    } else if min == max && min == imm_val {
                        Some(false)
                    } else {
                        None
                    }
                }
                // Signed comparisons - only if we can trust the bounds
                CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe => {
                    // More complex - need signed interpretation
                    // Skip for now, or handle carefully
                    None
                }
                CmpOp::Test => {
                    // 1. Get the Abstract State (TNum)
                    // TNum tells us which bits are definitely 1 (value) and which are unknown (mask).
                    let mut tnum = state.get_tnum(left);

                    // 2. Handle 32-bit Width
                    // If this is a W32 check, we must ignore the upper 32 bits of the register.
                    if width == Width::W32 {
                        tnum = tnum.trunc32();
                    }

                    // 3. Check for Definite Outcomes
                    if (tnum.value & imm_val) != 0 {
                        Some(true)
                    } else if ((tnum.value | tnum.mask) & imm_val) == 0 {
                        Some(false)
                    } else {
                        None
                    }
                }
            }
        }
        Operand::Reg(_r) => None,
    }
}

/// Get combined bounds from tnum and DBM, as unsigned values.
/// Returns None if we can't safely determine bounds.
pub(crate) fn get_combined_bounds(state: &State, reg: Reg, width: Width) -> Option<(u64, u64)> {
    // Tnum bounds
    let tnum = match width {
        Width::W32 => state.get_tnum(reg).trunc32(),
        Width::W64 => state.get_tnum(reg),
    };
    let tnum_min = tnum.min_value();
    let tnum_max = tnum.max_value();

    // DBM bounds
    let (dbm_lo, dbm_hi) = state.domain.get_interval(reg);

    // Combine bounds
    if dbm_lo != i64::MIN && dbm_hi != i64::MAX {
        let lo = dbm_lo;
        let hi = dbm_hi;
        // For unsigned comparison, DBM bounds only useful if non-negative
        if lo >= 0 {
            let dbm_min = lo as u64;
            let dbm_max = hi as u64;

            // For W32, also check DBM is in u32 range
            if width == Width::W32 && dbm_max > 0xFFFFFFFF {
                return Some((tnum_min, tnum_max));
            }

            // Intersect the ranges
            let combined_min = tnum_min.max(dbm_min);
            let combined_max = tnum_max.min(dbm_max);

            // Sanity check - ranges should overlap
            if combined_min <= combined_max {
                Some((combined_min, combined_max))
            } else {
                Some((tnum_min, tnum_max))
            }
        } else {
            Some((tnum_min, tnum_max))
        }
    } else {
        Some((tnum_min, tnum_max))
    }
}

pub(crate) fn fits_in_i32(bounds: (i64, i64)) -> bool {
    bounds.0 >= i32::MIN as i64 && bounds.1 <= i32::MAX as i64
}

pub(crate) fn fits_in_u32(bounds: (i64, i64)) -> bool {
    bounds.0 >= 0 && bounds.1 <= 0xFFFFFFFF
}

/// Get combined signed bounds for a register using both DBM and tnum.
/// Returns (lo, hi) as signed i64 values, using the tighter bound from each source.
pub(crate) fn get_combined_signed_bounds(state: &State, reg: Reg) -> (i64, i64) {
    let (dbm_lo, dbm_hi) = state.domain.get_interval(reg);
    let tnum = state.get_tnum(reg);
    let tnum_min = tnum.min_value();
    let tnum_max = tnum.max_value();

    let lo = if tnum_min > i64::MAX as u64 {
        let tnum_lo = tnum_min as i64;
        if dbm_lo != i64::MIN {
            dbm_lo.max(tnum_lo)
        } else {
            tnum_lo
        }
    } else {
        dbm_lo
    };

    let hi = if tnum_max <= i64::MAX as u64 {
        let tnum_hi = tnum_max as i64;
        if dbm_hi != i64::MAX {
            dbm_hi.min(tnum_hi)
        } else {
            tnum_hi
        }
    } else {
        dbm_hi
    };

    (lo, hi)
}
