// src/analysis/transfer/branch.rs
//
// If/branch handling, constraint application, interval checks

use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::ast::{Instr, CmpOp, Operand, Width};
use crate::zone::domain::{
    Reg, get_bounds, assume_eq_const, assume_ge_const, assume_le_const,
    assume_less_than, assume_ge_var, assume_le_var, assume_gt_var,
    assume_le_var_plus_const, assign_eq, nonneg
};
use crate::zone::dbm::Dbm;
use crate::zone::tnum::Tnum;
use crate::analysis::env::VerificationError;
use crate::analysis::reg_types::RegType;

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
    let mut out = Vec::new();
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

    // Return only consistent states
    if !state_else.dbm.is_inconsistent() { out.push(state_else); }
    if !state_then.dbm.is_inconsistent() { out.push(state_then); }
    out
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
                    if let Some(offset) = non_null.get_offset() {
                        assume_eq_const(&mut then_s.dbm, left, offset);
                    }
                }
            }
        }
        CmpOp::Eq => {
            assume_eq_const(&mut then_s.dbm, left, imm);
            then_s.set_tnum(left, Tnum::constant(imm_u64));
            if imm == 0 {
                if let Some(non_null) = else_s.types.get(left).to_non_null() {
                    else_s.types.set(left, non_null);
                    if let Some(offset) = non_null.get_offset() {
                        assume_eq_const(&mut else_s.dbm, left, offset);
                    }
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
                        refine_mem_ranges(&state.dbm, &mut state.types, left, right);
                        refine_mem_ranges(&state.dbm, &mut state.types, right, left);
                    }
                    return;
                }
            }
            _ => {}
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
                refine_mem_ranges(&state.dbm, &mut state.types, left, right);
                refine_mem_ranges(&state.dbm, &mut state.types, right, left);
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
        refine_mem_ranges(&state.dbm, &mut state.types, left, right);
        refine_mem_ranges(&state.dbm, &mut state.types, right, left);
    }
}
