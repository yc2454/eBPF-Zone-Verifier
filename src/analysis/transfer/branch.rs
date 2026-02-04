// src/analysis/transfer/branch.rs
//
// If/branch handling, constraint application, interval checks

use log::{warn};

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::state::State;
use crate::ast::{Instr, CmpOp, Operand, Width};
use crate::zone::domain::{
    Reg, get_bounds, assume_eq_const, assume_ge_const, assume_le_const,
    assume_less_than, assume_ge_var, assume_le_var, assume_gt_var,
    assume_le_var_plus_const, assign_eq, nonneg, get_constant_value
};
use crate::zone::dbm::Dbm;
use crate::zone::tnum::Tnum;
use crate::analysis::machine::env::VerificationError;
use crate::analysis::machine::reg_types::RegType;

use super::refinement::{refine_mem_ranges, refine_branch};
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
    // Target cannot be a back edge
    if target < state.pc {
        let on_path = state.history_idx
            .map(|idx| env.history.path_contains_pc(idx, target))
            .unwrap_or(false);
        if !on_path {
            env.fail(VerificationError::BackEdge { pc: state.pc, target });
            return vec![];
        }
    }

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
        Operand::Imm(imm) => apply_imm_constraints(&mut state_then, &mut state_else, left, op, width, *imm),
        Operand::Reg(r) => apply_reg_constraints(&mut state_then, &mut state_else, left, op, width, *r),
    }

    // Branch Type Refinement (For map pointers)
    let instr = Instr::If { width, left, op, right: right.clone(), target };
    refine_branch(&mut state_then, &instr, true);
    refine_branch(&mut state_else, &instr, false);

    // Check for statically determined branches
    if let Some(outcome) = condition_outcome(&state, width, left, op, &right) {
        return if outcome {
            vec![state_then]
        } else {
            vec![state_else]
        };
    }

    // Return only consistent states (the ORIGINAL logic)
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

            println!("min {}, max {}, imm {}", min, max, imm_val);
            
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
                CmpOp::Test => None,
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

/// Check if we can safely apply signed constraints for 32-bit comparisons.
/// This is true when the 64-bit value fits in i32 range, so 32-bit and 64-bit
/// signed interpretations are the same.
fn fits_in_i32_range(dbm: &Dbm, reg: Reg) -> bool {
    let (lo, hi) = get_bounds(dbm, reg);
    match (lo, hi) {
        (Some(l), Some(h)) => l >= i32::MIN as i64 && h <= i32::MAX as i64,
        _ => false,
    }
}

/// Check if value is known to be in u32 range [0, 0xFFFFFFFF]
fn fits_in_u32_range(dbm: &Dbm, reg: Reg) -> bool {
    let (lo, hi) = get_bounds(dbm, reg);
    match (lo, hi) {
        (Some(l), Some(h)) => l >= 0 && h <= 0xFFFFFFFF,
        _ => false,
    }
}

fn apply_imm_constraints(
    then_s: &mut State, 
    else_s: &mut State, 
    left: Reg, 
    op: CmpOp,
    width: Width,
    imm: i64,
) {
    let imm_u64 = imm as u64;
    
    // Handle 32-bit signed comparisons specially
    if width == Width::W32 {
        match op {
            // Special case: 32-bit signed comparison against 0
            // This is common (checking if value is negative)
            CmpOp::SLt if imm == 0 => {
                if fits_in_u32_range(&then_s.dbm, left) {
                    // 32-bit signed < 0 means bit 31 is set: value in [0x80000000, 0xFFFFFFFF]
                    assume_ge_const(&mut then_s.dbm, left, 0x80000000);
                    // 32-bit signed >= 0 means bit 31 is clear: value in [0, 0x7FFFFFFF]
                    assume_le_const(&mut else_s.dbm, left, 0x7FFFFFFF);
                }
                return;
            }
            CmpOp::SGe if imm == 0 => {
                if fits_in_u32_range(&then_s.dbm, left) {
                    // 32-bit signed >= 0 means value in [0, 0x7FFFFFFF]
                    assume_le_const(&mut then_s.dbm, left, 0x7FFFFFFF);
                    // 32-bit signed < 0 means value in [0x80000000, 0xFFFFFFFF]
                    assume_ge_const(&mut else_s.dbm, left, 0x80000000);
                }
                return;
            }
            CmpOp::SLe if imm == -1 => {
                // x <=s32 -1 is same as x <s32 0
                if fits_in_u32_range(&then_s.dbm, left) {
                    assume_ge_const(&mut then_s.dbm, left, 0x80000000);
                    assume_le_const(&mut else_s.dbm, left, 0x7FFFFFFF);
                }
                return;
            }
            CmpOp::SGt if imm == -1 => {
                // x >s32 -1 is same as x >=s32 0
                if fits_in_u32_range(&then_s.dbm, left) {
                    assume_le_const(&mut then_s.dbm, left, 0x7FFFFFFF);
                    assume_ge_const(&mut else_s.dbm, left, 0x80000000);
                }
                return;
            }
            
            // For other signed comparisons, only constrain if value fits in i32
            CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe => {
                if !fits_in_i32_range(&then_s.dbm, left) {
                    return;  // Can't safely add constraints
                }
                // Fall through to standard constraint logic
            }

            CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt => {
                // Unsigned comparisons can always be applied safely in 32-bit
            }

            CmpOp::Eq | CmpOp::Ne => {
                // Equality checks can always be applied safely
            }

            CmpOp::Test => {
                // Test against immediate in 32-bit
                // We can only safely apply constraints if the value fits in u32
                if !fits_in_u32_range(&then_s.dbm, left) {
                    return; // Can't safely add constraints
                }
                // Fall through to standard constraint logic
            }
        }
    }

    let is_unsigned_cmp = matches!(op, CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt);
    
    if is_unsigned_cmp {
        // If imm is negative (when interpreted as signed), it represents a 
        // large unsigned value (>= 2^63). Our signed DBM can't handle this correctly.
        if imm < 0 {
            // Conservative: don't apply any constraints
            // The type refinement (packet ranges, etc.) will still happen
            return;
        }
        
        // Also check if register might have values >= 2^63
        // If so, signed and unsigned comparisons differ
        let (lo, hi) = get_bounds(&then_s.dbm, left);
        if let (Some(l), Some(_h)) = (lo, hi) {
            if l < 0 {
                // Register might be negative (signed) = large (unsigned)
                // Can't safely apply unsigned constraints
                return;
            }
        } else {
            // Unknown bounds, be conservative
            return;
        }
    }
    
    // Standard constraint logic (64-bit or safe 32-bit cases)
    match op {
        CmpOp::Ne => {
            assume_eq_const(&mut else_s.dbm, left, imm);
            else_s.set_tnum(left, Tnum::constant(imm_u64));
            if imm == 0 {
                if let Some(non_null) = then_s.types.get(left).to_non_null() {
                    then_s.types.set(left, non_null);
                }
            }
        }
        CmpOp::Eq => {
            assume_eq_const(&mut then_s.dbm, left, imm);
            then_s.set_tnum(left, Tnum::constant(imm_u64));
            if imm == 0 {
                if let Some(non_null) = else_s.types.get(left).to_non_null() {
                    else_s.types.set(left, non_null);
                }
            }
        }
        CmpOp::UGe | CmpOp::SGe => {
            assume_ge_const(&mut then_s.dbm, left, imm);
            assume_less_than(&mut else_s.dbm, left, imm);
        }
        CmpOp::ULe | CmpOp::SLe => {
            assume_le_const(&mut then_s.dbm, left, imm);
            assume_ge_const(&mut else_s.dbm, left, imm + 1);
        }
        CmpOp::UGt | CmpOp::SGt => {
            assume_ge_const(&mut then_s.dbm, left, imm + 1);
            assume_le_const(&mut else_s.dbm, left, imm);
        }
        CmpOp::ULt | CmpOp::SLt => {
            assume_less_than(&mut then_s.dbm, left, imm);
            assume_ge_const(&mut else_s.dbm, left, imm);
        }
        CmpOp::Test => {
            // x & imm != 0
            // Skip for now
        }
    }
}

fn apply_reg_constraints(
    then_s: &mut State, 
    else_s: &mut State, 
    left: Reg, 
    op: CmpOp,
    width: Width,
    right: Reg
) {
    // Check if operands are packet-related pointers
    let is_packet_related = |t: &RegType| matches!(
        t,
        RegType::PtrToPacket { .. } | 
        RegType::PtrToPacketMeta | 
        RegType::PtrToPacketEnd
    );
    
    let left_is_packet = is_packet_related(&then_s.types.get(left));
    let right_is_packet = is_packet_related(&then_s.types.get(right));
    
    // If one side is packet-related and the other is scalar, 
    // don't add DBM constraints - they could create unsound packet bounds
    // via transitive closure (e.g., scalar derived from packet ptr that exceeded MAX_PACKET_OFF)
    if left_is_packet != right_is_packet {
        // Skip DBM constraints, skip packet range refinement
        return;
    }
    
    // For 32-bit signed reg-reg comparisons, only constrain if both fit in i32
    if width == Width::W32 {
        match op {
            CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe => {
                if !fits_in_i32_range(&then_s.dbm, left) || !fits_in_i32_range(&then_s.dbm, right) {
                    for state in [&mut *then_s, &mut *else_s] {
                        refine_mem_ranges(&state.dbm, &mut state.types, &mut state.stack, left, right);
                        refine_mem_ranges(&state.dbm, &mut state.types, &mut state.stack, right, left);
                    }
                    return;
                }
            }
            _ => {}
        }
        if let Some(right_val) = get_constant_value(&then_s.dbm, right) {
            let right_val_trunc = right_val as u32;
            // Only apply if left fits in u32 (so its truncation is a no-op)
            if fits_in_u32_range(&then_s.dbm, left) {
                apply_imm_constraints(then_s, else_s, left, op, width, right_val_trunc as i64);
                return;
            }
        }
    }
    
    // For unsigned reg-reg comparisons, we can only safely apply signed DBM
    // constraints if BOTH registers are KNOWN to be non-negative
    let is_unsigned_cmp = matches!(op, CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt);
    
    if is_unsigned_cmp {
        if !nonneg(&then_s.dbm, left) || !nonneg(&then_s.dbm, right) {
            // One or both could be negative (signed) = large (unsigned)
            // Cannot safely convert unsigned constraints to signed DBM constraints
            for state in [&mut *then_s, &mut *else_s] {
                refine_mem_ranges(&state.dbm, &mut state.types, &mut state.stack, left, right);
                refine_mem_ranges(&state.dbm, &mut state.types, &mut state.stack, right, left);
            }
            return;
        }
    }
    
    // Standard constraint logic (only reached if safe)
    match op {
        CmpOp::UGe | CmpOp::SGe => { 
            assume_ge_var(&mut then_s.dbm, left, right);
            assume_le_var_plus_const(&mut else_s.dbm, left, right, -1);
        }
        CmpOp::ULe | CmpOp::SLe => { 
            assume_le_var(&mut then_s.dbm, left, right);
            assume_gt_var(&mut else_s.dbm, left, right);
        }
        CmpOp::UGt | CmpOp::SGt => { 
            assume_gt_var(&mut then_s.dbm, left, right);
            assume_le_var(&mut else_s.dbm, left, right);
        }
        CmpOp::ULt | CmpOp::SLt => { 
            assume_le_var_plus_const(&mut then_s.dbm, left, right, -1);
            assume_ge_var(&mut else_s.dbm, left, right);
        }
        CmpOp::Eq => {
            assign_eq(&mut then_s.dbm, left, right);
        }
        CmpOp::Ne => {
            assign_eq(&mut else_s.dbm, left, right);
        }
        CmpOp::Test => {
            // No direct way to express in DBM
        }
    }
    
    // Refine pointer ranges on both states
    for state in [&mut *then_s, &mut *else_s] {
        refine_mem_ranges(&state.dbm, &mut state.types, &mut state.stack, left, right);
        refine_mem_ranges(&state.dbm, &mut state.types, &mut state.stack, right, left);
    }
}
