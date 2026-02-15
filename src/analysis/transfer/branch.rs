// src/analysis/transfer/branch.rs
//
// If/branch handling, constraint application, interval checks

use log::{warn};

use either::Either::{self, Left, Right};

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::state::State;
use crate::ast::{Instr, CmpOp, Operand, Width};
use crate::analysis::machine::reg::Reg;
use crate::zone::domain::{
    assign_eq, assume_eq_const, assume_ge_const, 
    assume_ge_var, assume_gt_var, assume_le_const, 
    assume_le_var, assume_le_var_plus_const, assume_less_than, 
    get_bounds, get_constant_value
};
use crate::zone::dbm::{Dbm};
use crate::zone::tnum::Tnum;
use crate::analysis::machine::env::VerificationError;

use super::refinement::{refine_branch};
use super::common::{check_reg_readable, check_operand_readable};

/// Transfer function for conditional branch instructions.
pub(crate) fn transfer_if(
    env: &mut VerifierEnv,
    state: State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: Operand,
    target: usize,
) -> Vec<State> {
    // Check operand readability
    if !check_reg_readable(env, &state, left) {
        return vec![];
    }
    if !check_operand_readable(env, &state, &right) {
        return vec![];
    }
    
    // --- STEP 1: Abstract Interpretation (Constraint Refinement) ---
    let mut state_then = state.clone();
    let mut state_else = state.clone();

    state_then.pc = target;
    state_else.pc = state.pc + 1;

    // Apply constraints to refine the DBM in the destination states
    match &right {
        Operand::Imm(imm) => 
            apply_jmp_constraints(&mut state_then, &mut state_else, left, op, width, Right(*imm)),
        Operand::Reg(r) => 
            apply_jmp_constraints(&mut state_then, &mut state_else, left, op, width, Left(*r)),
    }

    // Branch Type Refinement (For map and socket pointers)
    let instr = Instr::If { width, left, op, right: right.clone(), target };
    refine_branch(&mut state_then, &instr, true);
    refine_branch(&mut state_else, &instr, false);

    let backward_jump_forbidden = |st: &State| -> bool {
        if target >= st.pc {
            return false;
        }
        let on_path = st.history_idx
            .map(|idx| env.history.path_contains_pc(idx, target))
            .unwrap_or(false);
        let already_explored = env.explored_states.contains_key(&target);
        !on_path && !already_explored
    };

    // Check for statically determined branches
    if let Some(outcome) = condition_outcome(&state, width, left, op, &right) {
        return if outcome {
            if backward_jump_forbidden(&state_then) {
                env.fail(VerificationError::BackEdge { pc: state.pc, target });
                vec![]
            } else {
                vec![state_then]
            }
        } else {
            vec![state_else]
        };
    }

    if backward_jump_forbidden(&state_then) {
        env.fail(VerificationError::BackEdge { pc: state.pc, target });
        return vec![];
    }

    // Return only consistent states
    let mut out = Vec::new();
    if !state_else.dbm.is_inconsistent() { out.push(state_else); } else { warn!("Else branch is inconsistent") }
    if !state_then.dbm.is_inconsistent() { out.push(state_then); } else { warn!("Then branch is inconsistent") }
    out
}

/// Check if a branch condition can be determined at analysis time.
/// Returns:
///   Some(true)  - condition is ALWAYS true (only then-branch reachable)
///   Some(false) - condition is ALWAYS false (only else-branch reachable)
///   None        - condition could go either way
fn condition_outcome(
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
                    if max < imm_val { Some(true) }      // always true
                    else if min >= imm_val { Some(false) } // always false
                    else { None }
                }
                CmpOp::UGe => {
                    if min >= imm_val { Some(true) }
                    else if max < imm_val { Some(false) }
                    else { None }
                }
                CmpOp::ULe => {
                    if max <= imm_val { Some(true) }
                    else if min > imm_val { Some(false) }
                    else { None }
                }
                CmpOp::UGt => {
                    if min > imm_val { Some(true) }
                    else if max <= imm_val { Some(false) }
                    else { None }
                }
                CmpOp::Eq => {
                    if min == max && min == imm_val { Some(true) }
                    else if min > imm_val || max < imm_val { Some(false) }
                    else { None }
                }
                CmpOp::Ne => {
                    if min > imm_val || max < imm_val { Some(true) }
                    else if min == max && min == imm_val { Some(false) }
                    else { None }
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
                        // Assuming your TNum has a truncate or you can do it manually:
                        tnum = tnum.trunc32(); 
                        // Or manually:
                        // tnum.value &= 0xFFFF_FFFF;
                        // tnum.mask &= 0xFFFF_FFFF;
                    }

                    // 3. Check for Definite Outcomes
                    
                    // Case A: ALWAYS TRUE (Jump Taken)
                    // Do we have a bit that is KNOWN to be 1 in 'left' AND is set in 'right'?
                    // If yes, the result of (left & right) is definitely non-zero.
                    if (tnum.value & imm_val) != 0 {
                        Some(true)
                    }
                    // Case B: ALWAYS FALSE (Jump Not Taken)
                    // Do we know for a fact that 'left' can NEVER have a 1 where 'right' has a 1?
                    // 'tnum.value | tnum.mask' represents all bits that COULD possibly be 1.
                    // If the intersection with 'imm_val' is 0, the result is always 0.
                    else if ((tnum.value | tnum.mask) & imm_val) == 0 {
                        Some(false)
                    }
                    // Case C: Indeterminate
                    // The mask hits some "Unknown" bits in the register. We can't be sure.
                    else {
                        None
                    }
                }
            }
        }
        Operand::Reg(_r) => {
            // Could compare ranges of two registers
            // For now, conservative
            None
        }
    }
}

/// Get combined bounds from tnum and DBM, as unsigned values.
/// Returns None if we can't safely determine bounds.
fn get_combined_bounds(state: &State, reg: Reg, width: Width) -> Option<(u64, u64)> {
    // Tnum bounds
    let tnum = match width {
        Width::W32 => state.get_tnum(reg).trunc32(),
        Width::W64 => state.get_tnum(reg),
    };
    let tnum_min = tnum.min_value();
    let tnum_max = tnum.max_value();
    
    // DBM bounds
    let (dbm_lo, dbm_hi) = get_bounds(&state.dbm, reg);
    
    // Combine bounds
    match (dbm_lo, dbm_hi) {
        (Some(lo), Some(hi)) => {
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
                    // Contradiction - shouldn't happen if state is consistent
                    // Return tnum bounds as fallback
                    Some((tnum_min, tnum_max))
                }
            } else {
                // DBM has negative values - can't safely use for unsigned comparison
                Some((tnum_min, tnum_max))
            }
        }
        _ => {
            // No DBM bounds, use tnum only
            Some((tnum_min, tnum_max))
        }
    }
}

fn fits_in_i32(bounds: (i64, i64)) -> bool {
    bounds.0 >= i32::MIN as i64 && bounds.1 <= i32::MAX as i64
}

fn fits_in_u32(bounds: (i64, i64)) -> bool {
    bounds.0 >= 0 && bounds.1 <= 0xFFFFFFFF
}

/// Check if value is known to be in u32 range [0, 0xFFFFFFFF]
fn fits_in_u32_range(dbm: &Dbm, reg: Reg) -> bool {
    let (lo, hi) = get_bounds(dbm, reg);
    match (lo, hi) {
        (Some(l), Some(h)) => fits_in_u32((l, h)),
        _ => false,
    }
}

/// Get combined signed bounds for a register using both DBM and tnum.
/// Returns (lo, hi) as signed i64 values, using the tighter bound from each source.
fn get_combined_signed_bounds(state: &State, reg: Reg) -> (i64, i64) {
    let (dbm_lo, dbm_hi) = get_bounds(&state.dbm, reg);
    let tnum = state.get_tnum(reg);
    let tnum_min = tnum.min_value();
    let tnum_max = tnum.max_value();

    // Tnum gives unsigned bounds. We can derive signed info from it:
    // If max_value <= i64::MAX as u64, the value is non-negative in signed terms.
    // If min_value > i64::MAX as u64, the value is negative in signed terms.
    let lo = if tnum_min > i64::MAX as u64 {
        // Definitely negative: tnum_min as signed
        let tnum_lo = tnum_min as i64;
        match dbm_lo {
            Some(d) => d.max(tnum_lo),
            None => tnum_lo,
        }
    } else {
        dbm_lo.unwrap_or(i64::MIN)
    };

    let hi = if tnum_max <= i64::MAX as u64 {
        // Definitely non-negative: tnum_max as signed
        let tnum_hi = tnum_max as i64;
        match dbm_hi {
            Some(d) => d.min(tnum_hi),
            None => tnum_hi,
        }
    } else {
        dbm_hi.unwrap_or(i64::MAX)
    };

    (lo, hi)
}

/// Whether it's safe to apply DBM constraints for this comparison
fn can_apply_dbm_constraint(
    state: &State,
    left: Reg,
    op: CmpOp,
    width: Width,
    right_bounds: (i64, i64),  // (lo, hi) of right operand
    right: Either<Reg, i64>,
) -> bool {
    let dominated_by_signed = matches!(op, CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe);
    let dominated_by_unsigned = matches!(op, CmpOp::ULt | CmpOp::ULe | CmpOp::UGt | CmpOp::UGe);

    if width == Width::W32 {
        let left_bounds = get_combined_signed_bounds(state, left);
        if dominated_by_signed {
            return fits_in_i32(left_bounds) && fits_in_i32(right_bounds);
        } else if dominated_by_unsigned {
            return fits_in_u32(left_bounds) && fits_in_u32(right_bounds);
        }
    }

    if dominated_by_unsigned {
        // For 64-bit unsigned, both sides must be non-negative for signed DBM.
        // Check both DBM and tnum for non-negativity.
        // If a side is fully unbounded (no DBM lower bound, tnum spans signed range),
        // allow it — this covers pointer-vs-pointer comparisons where both sides
        // lack absolute bounds but have valid relative (difference) constraints.
        let left_bounds = get_combined_signed_bounds(state, left);
        let left_nonneg = left_bounds.0 >= 0;
        let left_unbounded = {
            let (lo, _) = get_bounds(&state.dbm, left);
            let tnum = state.get_tnum(left);
            lo.is_none() && tnum.max_value() > i64::MAX as u64
        };
        let right_nonneg = right_bounds.0 >= 0;
        let right_is_pointer = match right {
            Either::Left(reg) => state.types.get(reg).is_pointer(),
            _ => false,
        };
        return (left_nonneg || left_unbounded) && (right_nonneg || right_is_pointer);
    }

    true
}

/// Core constraint application - no safety checks, just applies constraints
fn apply_cmp_to_dbm(
    then_dbm: &mut Dbm,
    else_dbm: &mut Dbm,
    left: Reg,
    op: CmpOp,
    right: Either<Reg, i64>,
) {
    match (op, right) {
        (CmpOp::Eq, Either::Right(imm)) => {
            assume_eq_const(then_dbm, left, imm);
        }
        (CmpOp::Eq, Either::Left(reg)) => {
            assign_eq(then_dbm, left, reg);
        }
        (CmpOp::Ne, Either::Right(imm)) => {
            assume_eq_const(else_dbm, left, imm);
        }
        (CmpOp::Ne, Either::Left(reg)) => {
            assign_eq(else_dbm, left, reg);
        }
        (CmpOp::UGe, Either::Right(imm)) => {
            assume_ge_const(then_dbm, left, imm);
            assume_less_than(else_dbm, left, imm);
            if imm > 0 {
                assume_ge_const(else_dbm, left, 0);
            }
        }
        (CmpOp::SGe, Either::Right(imm)) => {
            assume_ge_const(then_dbm, left, imm);
            assume_less_than(else_dbm, left, imm);
        }
        (CmpOp::UGe, Either::Left(reg)) => {
            assume_ge_var(then_dbm, left, reg);
            assume_le_var_plus_const(else_dbm, left, reg, -1);
            assume_ge_const(else_dbm, left, 0);
        }
        (CmpOp::SGe, Either::Left(reg)) => {
            assume_ge_var(then_dbm, left, reg);
            assume_le_var_plus_const(else_dbm, left, reg, -1);
        }
        (CmpOp::UGt, Either::Right(imm)) => {
            assume_ge_const(then_dbm, left, imm + 1);
            assume_le_const(else_dbm, left, imm);
            assume_ge_const(else_dbm, left, 0);
        }
        (CmpOp::SGt, Either::Right(imm)) => {
            assume_ge_const(then_dbm, left, imm + 1);
            assume_le_const(else_dbm, left, imm);
        }
        (CmpOp::UGt, Either::Left(reg)) => {
            assume_gt_var(then_dbm, left, reg);
            assume_le_var(else_dbm, left, reg);
            assume_ge_const(else_dbm, left, 0);
        }
        (CmpOp::SGt, Either::Left(reg)) => {
            assume_gt_var(then_dbm, left, reg);
            assume_le_var(else_dbm, left, reg);
        }
        (CmpOp::ULe, Either::Right(imm)) => {
            assume_le_const(then_dbm, left, imm);
            assume_ge_const(then_dbm, left, 0);
            assume_ge_const(else_dbm, left, imm + 1);
        }
        (CmpOp::SLe, Either::Right(imm)) => {
            assume_le_const(then_dbm, left, imm);
            assume_ge_const(else_dbm, left, imm + 1);
        }
        (CmpOp::ULe, Either::Left(reg)) => {
            assume_le_var(then_dbm, left, reg);
            assume_ge_const(then_dbm, left, 0);
            assume_gt_var(else_dbm, left, reg);
        }
        (CmpOp::SLe, Either::Left(reg)) => {
            assume_le_var(then_dbm, left, reg);
            assume_gt_var(else_dbm, left, reg);
        }
        (CmpOp::ULt, Either::Right(imm)) => {
            assume_less_than(then_dbm, left, imm);
            if imm > 0 {
                assume_ge_const(then_dbm, left, 0);
            }
            assume_ge_const(else_dbm, left, imm);
        }
        (CmpOp::SLt, Either::Right(imm)) => {
            assume_less_than(then_dbm, left, imm);
            assume_ge_const(else_dbm, left, imm);
        }
        (CmpOp::ULt, Either::Left(reg)) => {
            assume_le_var_plus_const(then_dbm, left, reg, -1);
            assume_ge_const(then_dbm, left, 0);
            assume_ge_var(else_dbm, left, reg);
        }
        (CmpOp::SLt, Either::Left(reg)) => {
            assume_le_var_plus_const(then_dbm, left, reg, -1);
            assume_ge_var(else_dbm, left, reg);
        }
        (CmpOp::Test, _) => {}
    }
}

/// Update tnum and type info for equality comparisons
fn apply_eq_refinements(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    op: CmpOp,
    imm: Option<i64>,
) {
    match (op, imm) {
        (CmpOp::Eq, Some(v)) => {
            then_s.set_tnum(left, Tnum::constant(v as u64));
        }
        (CmpOp::Ne, Some(v)) => {
            else_s.set_tnum(left, Tnum::constant(v as u64));
        }
        _ => {}
    }
}

fn apply_test_constraints(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    width: Width,
    right: Either<Reg, i64>,
) {
    let mask = match right {
        Either::Right(imm) => {
            if width == Width::W32 {
                (imm as u32) as u64
            } else {
                imm as u64
            }
        }
        Either::Left(reg) => {
            // If right is a register, check if it's a known constant
            if let Some(val) = get_constant_value(&then_s.dbm, reg) {
                if width == Width::W32 {
                    (val as u32) as u64
                } else {
                    val as u64
                }
            } else {
                // Can't derive much without knowing the mask
                return;
            }
        }
    };
    
    // Not-taken branch: left & mask == 0
    // Those bits are definitely zero in left
    let else_tnum = else_s.get_tnum(left);
    let refined = Tnum {
        value: else_tnum.value & !mask,  // Those bits are 0
        mask: else_tnum.mask & !mask,    // Those bits are known (not uncertain)
    };
    else_s.set_tnum(left, refined);
    
    // Taken branch: left & mask != 0
    // At least one bit is set, but we don't know which
    // Limited tnum refinement possible
    
    // Special case: power of 2 mask (single bit test)
    if mask.is_power_of_two() {
        let bit_pos = mask.trailing_zeros();
        
        // Taken: that specific bit is set
        let then_tnum = then_s.get_tnum(left);
        let refined = Tnum {
            value: then_tnum.value | mask,  // That bit is 1
            mask: then_tnum.mask & !mask,   // That bit is known
        };
        then_s.set_tnum(left, refined);
        
        // DBM constraints for sign bit tests
        if width == Width::W32 && bit_pos == 31 {
            // Testing 32-bit sign bit
            if fits_in_u32_range(&then_s.dbm, left) {
                // Taken: bit 31 set -> value in [0x80000000, 0xFFFFFFFF]
                assume_ge_const(&mut then_s.dbm, left, 0x80000000);
                // Not taken: bit 31 clear -> value in [0, 0x7FFFFFFF]
                assume_le_const(&mut else_s.dbm, left, 0x7FFFFFFF);
            }
        } else if width == Width::W64 && bit_pos == 63 {
            // Testing 64-bit sign bit
            // Taken: negative (in signed terms)
            // Not taken: non-negative
            assume_less_than(&mut then_s.dbm, left, 0);
            assume_ge_const(&mut else_s.dbm, left, 0);
        }
    }
}

/// Resolve right operand: truncate for 32-bit, extract constant if possible
fn resolve_right_operand(
    dbm: &Dbm,
    right: Either<Reg, i64>,
    width: Width,
    op: CmpOp,
) -> (Either<Reg, i64>, (i64, i64)) {
    let is_signed = matches!(op, CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe);
    
    let truncate = |val: i64| -> i64 {
        if width == Width::W32 {
            if is_signed {
                (val as u32) as i32 as i64  // sign-extend
            } else {
                (val as u32) as i64  // zero-extend
            }
        } else {
            val
        }
    };
    
    match right {
        Either::Right(imm) => {
            let eff = truncate(imm);
            (Either::Right(eff), (eff, eff))
        }
        Either::Left(reg) => {
            if let Some(val) = get_constant_value(dbm, reg) {
                let eff = truncate(val);
                (Either::Right(eff), (eff, eff))
            } else {
                let bounds = get_bounds(dbm, reg);
                let bounds = (bounds.0.unwrap_or(i64::MIN), bounds.1.unwrap_or(i64::MAX));
                (Either::Left(reg), bounds)
            }
        }
    }
}

// ============ Public entry points ============

pub fn apply_jmp_constraints(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    op: CmpOp,
    width: Width,
    right: Either<Reg, i64>,
) {
    if op == CmpOp::Test {
        apply_test_constraints(then_s, else_s, left, width, right);
        return;
    }
    
    // Resolve operand (truncate, extract constant)
    let (resolved, right_bounds) = resolve_right_operand(&then_s.dbm, right, width, op);
    // Apply DBM constraints if safe
    if can_apply_dbm_constraint(then_s, left, op, width, right_bounds, resolved) {
        apply_cmp_to_dbm(&mut then_s.dbm, &mut else_s.dbm, left, op, resolved);
    } else if width == Width::W64 && matches!(op, CmpOp::UGt | CmpOp::UGe | CmpOp::ULt | CmpOp::ULe) {
        // Fallback: derive signed constraints from unsigned 64-bit comparison
        // when one operand is a known constant.
        // Only for W64: 32-bit comparisons truncate, so 64-bit DBM constraints would be wrong.
        apply_unsigned_const_fallback(then_s, else_s, left, op, resolved);
    }
    
    // Apply type/tnum refinements
    let imm_val = match resolved {
        Either::Right(v) => Some(v),
        Either::Left(_) => None,
    };
    apply_eq_refinements(then_s, else_s, left, op, imm_val);
}

/// Fallback for unsigned comparisons that can't use the standard signed DBM path.
/// When one operand is a known constant, we can still derive useful signed ranges
/// from unsigned comparisons (e.g., `x <u 0x8000000000000000` → `x >= 0` signed).
fn apply_unsigned_const_fallback(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    op: CmpOp,
    right: Either<Reg, i64>,
) {
    // Try to find a known constant on either side.
    // Check both DBM and tnum since the DBM can't represent x >= i64::MIN.
    let left_const = get_constant_value(&then_s.dbm, left)
        .or_else(|| {
            let t = then_s.get_tnum(left);
            if t.is_const() { Some(t.value as i64) } else { None }
        });

    match (left_const, right) {
        (Some(k), Either::Left(reg)) => {
            // left = K (known), right = reg (unknown): "K op reg"
            // Flip to "reg flipped_op K"
            let flipped = flip_unsigned_cmp(op);
            apply_unsigned_range_constraint(
                &mut then_s.dbm, &mut else_s.dbm, reg, flipped, k as u64,
            );
        }
        (_, Either::Right(imm)) => {
            // right = K (known), left = reg (unknown): "left op K"
            apply_unsigned_range_constraint(
                &mut then_s.dbm, &mut else_s.dbm, left, op, imm as u64,
            );
        }
        _ => {} // both unknown
    }
}

/// Flip an unsigned comparison: `a op b` ↔ `b flipped_op a`
fn flip_unsigned_cmp(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::UGt => CmpOp::ULt,
        CmpOp::UGe => CmpOp::ULe,
        CmpOp::ULt => CmpOp::UGt,
        CmpOp::ULe => CmpOp::UGe,
        other => other,
    }
}

/// Apply signed DBM constraints derived from "reg op K" (unsigned),
/// but only when the resulting range is representable as a signed interval.
fn apply_unsigned_range_constraint(
    then_dbm: &mut Dbm,
    else_dbm: &mut Dbm,
    reg: Reg,
    op: CmpOp, // "reg op K" in unsigned
    k: u64,
) {
    match op {
        CmpOp::UGt => {
            // Then: reg >u K → reg in [K+1, U64_MAX]
            if k < u64::MAX {
                apply_signed_from_unsigned_range(then_dbm, reg, k + 1, u64::MAX);
            }
            // Else: reg <=u K → reg in [0, K]
            apply_signed_from_unsigned_range(else_dbm, reg, 0, k);
        }
        CmpOp::UGe => {
            // Then: reg >=u K → reg in [K, U64_MAX]
            apply_signed_from_unsigned_range(then_dbm, reg, k, u64::MAX);
            // Else: reg <u K → reg in [0, K-1]
            if k > 0 {
                apply_signed_from_unsigned_range(else_dbm, reg, 0, k - 1);
            }
        }
        CmpOp::ULt => {
            // Then: reg <u K → reg in [0, K-1]
            if k > 0 {
                apply_signed_from_unsigned_range(then_dbm, reg, 0, k - 1);
            }
            // Else: reg >=u K → reg in [K, U64_MAX]
            apply_signed_from_unsigned_range(else_dbm, reg, k, u64::MAX);
        }
        CmpOp::ULe => {
            // Then: reg <=u K → reg in [0, K]
            apply_signed_from_unsigned_range(then_dbm, reg, 0, k);
            // Else: reg >u K → reg in [K+1, U64_MAX]
            if k < u64::MAX {
                apply_signed_from_unsigned_range(else_dbm, reg, k + 1, u64::MAX);
            }
        }
        _ => {}
    }
}

/// Apply signed DBM constraints for [lo_u, hi_u] unsigned, but only when
/// the range doesn't cross the sign boundary (i.e., representable as a
/// contiguous signed interval).
fn apply_signed_from_unsigned_range(dbm: &mut Dbm, reg: Reg, lo_u: u64, hi_u: u64) {
    if lo_u > hi_u {
        return; // empty range
    }

    let lo_s = lo_u as i64;
    let hi_s = hi_u as i64;

    if hi_u <= i64::MAX as u64 {
        // Entirely non-negative in signed: [0..i64::MAX]
        assume_ge_const(dbm, reg, lo_s);
        assume_le_const(dbm, reg, hi_s);
    } else if lo_u >= 0x8000000000000000 {
        // Entirely negative in signed: [i64::MIN..-1]
        assume_ge_const(dbm, reg, lo_s);
        assume_le_const(dbm, reg, hi_s);
    }
    // else: crosses sign boundary, can't represent as single signed interval
}
