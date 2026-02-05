// src/analysis/transfer/alu.rs
//
// ALU instruction handlers (add, sub, mov, and, or, mul, div, etc.)

use crate::analysis::machine::env::{VerifierEnv, VerificationError};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::ast::{AluOp, Operand, Width};
use crate::zone::domain::{
    Reg, forget, get_bounds, assign_add_imm, assign_add_reg, assign_eq,
    assume_ge_const, assume_le_const, assign_zero, assign_mul_imm,
    assign_and_mask, assign_div_imm, assign_div_reg, bit_and_const,
    assign_neg, assign_sub_reg, assume_eq_const
};
use crate::zone::dbm::{Dbm, INF};
use crate::zone::tnum::Tnum;
use crate::common::constants;
use log::error;

use super::types::update_alu_types;
use super::common::{check_reg_readable, check_operand_readable, check_reg_writable};

/// Transfer function for ALU instructions.
pub(crate) fn transfer_alu(
    env: &mut VerifierEnv,
    mut state: State,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: Operand,
) -> Vec<State> {
    // Check operand readability first
    // For Mov: only src needs to be readable
    // For other ops: dst is read-modify-write, so both need to be readable
    if op != AluOp::Mov {
        if !check_reg_readable(env, &state, dst) {
            return vec![];
        }
    }
    if !check_operand_readable(env, &state, &src) {
        return vec![];
    }

    // Check destination writability
    if !check_reg_writable(env, &state, dst) {
        return vec![];
    }

    let in_types = state.types.clone();

    // Check pointer arithmetics first
    let src_type = match src {
        Operand::Imm(_) => RegType::ScalarValue,
        Operand::Reg(r) => state.types.get(r).clone()
    };
    let dst_type = state.types.get(dst);

    if !check_ptr_arithmetic(env, &state, op, &dst_type, &src_type, &src) {
        env.fail(VerificationError::InvalidPointerArithmetic { pc: state.pc });
        return vec![];
    }

    // Early check for division by zero
    if op == AluOp::Div && is_div_by_zero(&state.dbm, &src) {
        env.fail(VerificationError::DivideByZero { pc: state.pc });
        return vec![];
    }

    update_alu_types(env, &in_types, &mut state.types, width, op, dst, &src, state.pc);

    match op {
        AluOp::Add => handle_add(env, &mut state, &in_types, width, dst, &src),
        AluOp::Sub => handle_sub(env, &mut state, &in_types, width, dst, &src),
        AluOp::Mov => handle_mov(&mut state, width, dst, &src),
        AluOp::And => handle_and(&mut state, width, dst, &src),
        AluOp::Or => handle_or(&mut state, width, dst, &src),
        AluOp::Neg => handle_neg(&mut state, width, dst),
        AluOp::Shr => handle_shr(&mut state, width, dst, &src),
        AluOp::Shl => handle_shl(&mut state, width, dst, &src),
        AluOp::Mul => handle_mul(&mut state, width, dst, &src),
        AluOp::Mod => handle_mod(&mut state, width, dst, &src),
        AluOp::Div => handle_div(&mut state, width, dst, &src),
        AluOp::Arsh => handle_arsh(&mut state, width, dst, &src),
        AluOp::Rsh => handle_rsh(&mut state, width, dst, &src),
        AluOp::Lsh => handle_shl(&mut state, width, dst, &src), // Same as Shl
        AluOp::Xor => forget(&mut state.dbm, dst),
    }

    if state.dbm.is_inconsistent() {
        env.fail(VerificationError::DbmInconsistent { pc: state.pc });
        error!("[Verifier] DBM became inconsistent at pc {}", state.pc);
        state.dbm.dump_matrix();
        vec![]
    } else {
        let next_pc = if env.invalid_pc_set.contains(&(state.pc + 1)) {
            state.pc + 2
        } else {
            state.pc + 1
        };
        state.pc = next_pc;
        vec![state]
    }
}

/// Pure validation of pointer arithmetic rules.
/// Returns Ok(()) if the operation is legal (even if it changes the result type).
/// Returns Err(String) if the operation is strictly forbidden.
pub(crate) fn check_ptr_arithmetic(
    _env: &mut VerifierEnv,
    state: &State,
    op: AluOp,
    dst_type: &RegType,
    src_type: &RegType,
    src: &Operand
) -> bool {
    let dst_is_ptr = dst_type.is_pointer();
    let src_is_ptr = src_type.is_pointer();

    let src_max = match src {
        Operand::Imm(k) => *k,
        Operand::Reg(r) => {
            let (_, max_opt) = get_bounds(&state.dbm, *r);
            match max_opt {
                Some(max) => max,
                None => INF,
            }
        }
    };

    // 1. Scalar <op> Scalar
    // Always allowed.
    if !dst_is_ptr && !src_is_ptr {
        return true;
    }

    // 2. Pointer <op> Pointer
    if dst_is_ptr && src_is_ptr {
        match op {
            // Ptr - Ptr is allowed ONLY if types match.
            // (Result is Scalar, handled by caller)
            AluOp::Sub => {
                RegType::is_same_pointer_type(dst_type, src_type)
            },
            AluOp::Mov => true,
            // Ptr + Ptr, Ptr * Ptr, etc. are invalid
            _ => { false }
        }
    }
    // 3. Pointer <op> Scalar (dst=Ptr, src=Scalar)
    else if dst_is_ptr {
        match op {
            AluOp::Add | AluOp::Sub => {
                if matches!(dst_type, RegType::PtrToMapValue { .. }) {
                    // The verifier identifies 0xFFFFFFFF (4294967295) as a forbidden offset
                    if src_max > i32::MAX as i64 || op == AluOp::Sub {
                        return false;
                    }
                }
                true
            },
            AluOp::Mov | AluOp::And => true, 
            _ => { false }
        }
    }
    // 4. Scalar <op> Pointer (dst=Scalar, src=Ptr)
    else {
        match op {
            // Scalar + Ptr is allowed (Commutative).
            // (Result is Ptr, handled by caller)
            AluOp::Add => true,
            
            // Scalar - Ptr is FORBIDDEN.
            AluOp::Sub => { false }

            // Mov Scalar, Ptr is allowed (dst becomes Ptr).
            AluOp::Mov => true,
            
            // Scalar * Ptr, etc. forbidden.
            _ => { false }
        }
    }
}

/// Check pointer bounds after arithmetic operations.
pub(crate) fn check_ptr_bounds(
    env: &mut VerifierEnv,
    state: &State,
    reg: Reg,
) {
    let (lo, hi) = get_bounds(&state.dbm, reg);
    
    match state.types.get(reg) {
        RegType::PtrToMapValue { map_idx, .. } => {
            if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                let in_bounds = match (lo, hi) {
                    (Some(l), Some(h)) => l >= 0 && h < map_def.value_size as i64,
                    _ => false,
                };
                if !in_bounds {
                    env.fail(VerificationError::PointerOutOfBounds { pc: state.pc });
                }
            } else {
                log::warn!("This should be unreachable")
            }
        }
        RegType::PtrToStack { .. } => {
            let in_bounds = match (lo, hi) {
                (Some(l), Some(h)) => l >= constants::BPF_STACK_MIN && h <= 0,
                _ => false,
            };
            if !in_bounds {
                env.fail(VerificationError::PointerOutOfBounds { pc: state.pc });
            }
        }
        _ => {}
    }
}

// ===============================================
// ALU Handlers
// ===============================================

fn handle_add(
    env: &mut VerifierEnv,
    state: &mut State,
    in_types: &TypeState,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            assign_add_imm(&mut state.dbm, dst, *c);
        }
        Operand::Reg(r) => {
            if is_clean_ptr(in_types, dst) {
                // Special Case: Ptr(Offset 0) += Scalar.
                // NewOffset = 0 + Scalar = Scalar.
                assign_eq(&mut state.dbm, dst, *r);
            } else {
                // Standard Case: Ptr(Offset X) += Scalar OR Scalar += Scalar
                assign_add_reg(&mut state.dbm, dst, *r);
            }
        }
    }
    
    let dst_tnum = state.get_tnum(dst);
    let new_tnum = match src {
        Operand::Imm(c) => dst_tnum.add_imm(*c),
        Operand::Reg(r) => dst_tnum.add(state.get_tnum(*r)),
    };
    let new_tnum = if width == Width::W32 { new_tnum.trunc32() } else { new_tnum };
    state.set_tnum(dst, new_tnum);
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    check_ptr_bounds(env, state, dst);
}

fn handle_sub(
    env: &mut VerifierEnv,
    state: &mut State,
    in_types: &TypeState,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            assign_add_imm(&mut state.dbm, dst, -c);
        }
        Operand::Reg(r) => {
            if is_clean_ptr(in_types, dst) {
                // dst = 0 - r => dst = -r
                assign_eq(&mut state.dbm, dst, *r);
                assign_neg(&mut state.dbm, dst);
            } else {
                // Standard Case: Interval Subtraction
                assign_sub_reg(&mut state.dbm, dst, *r);
            }
        }
    }

    let dst_tnum = state.get_tnum(dst);
    let new_tnum = match src {
        Operand::Imm(c) => dst_tnum.sub_imm(*c),
        Operand::Reg(r) => dst_tnum.sub(state.get_tnum(*r)),
    };
    let new_tnum = if width == Width::W32 { new_tnum.trunc32() } else { new_tnum };
    state.set_tnum(dst, new_tnum);
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    check_ptr_bounds(env, state, dst);
}

fn handle_mov(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    // Tnum update
    match src {
        Operand::Imm(c) => {
            state.set_tnum(dst, Tnum::constant(*c as u64));
        }
        Operand::Reg(r) => {
            let t = state.get_tnum(*r);
            state.set_tnum(dst, t);
        }
    }
    
    // DBM update
    match src {
        Operand::Reg(r) => {
            if width == Width::W32 {
                forget(&mut state.dbm, dst);
                if crate::zone::domain::proven_u32_range(&mut state.dbm, *r, Reg::Zero) {
                    assign_eq(&mut state.dbm, dst, *r);
                } else {
                    assume_ge_const(&mut state.dbm, dst, 0);
                    assume_le_const(&mut state.dbm, dst, 0xFFFFFFFF);
                }
            } else {
                if *r == Reg::R10 {
                    assign_zero(&mut state.dbm, dst);
                } else {
                    assign_eq(&mut state.dbm, dst, *r);
                }
            }
        }
        Operand::Imm(c) => {
            // Handle zero-extension for W32
            let c = if width == Width::W32 { (*c as u32) as i64 } else { *c };
            
            forget(&mut state.dbm, dst);
            assume_le_const(&mut state.dbm, dst, c);
            assume_ge_const(&mut state.dbm, dst, c);
        }
    }
}

fn handle_and(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    let (min_op, max_op) = get_bounds(&state.dbm, dst);
    let input_nonnegative = min_op.map_or(false, |m| m >= 0);

    forget(&mut state.dbm, dst);

    if let Operand::Imm(mask) = src {
        let mask = if width == Width::W32 { (*mask as u32) as i64 } else { *mask };
        if mask >= 0 {
            assign_and_mask(&mut state.dbm, dst, mask);
        } else if input_nonnegative {
            // Negative mask with non-negative input:
            // Safe approximation: [0, input_max]
            assume_ge_const(&mut state.dbm, dst, 0);
            if let Some(max) = max_op {
                assume_le_const(&mut state.dbm, dst, max);
            }
        }
    } else if let Operand::Reg(_) = src {
        // AND with register - result is non-negative if both operands are
        assume_ge_const(&mut state.dbm, dst, 0);
    }
    
    // Tnum update
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(mask) => {
            let mask = if width == Width::W32 { (*mask as u32) as u64 } else { *mask as u64 };
            t.and_imm(mask)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.and(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);
    
    // Cross-validate: if tnum knows the exact value, tell DBM
    if let Some(c) = new_t.const_value() {
        assume_eq_const(&mut state.dbm, dst, c as i64);
    }
}

fn handle_or(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    // Conservative update to the DBM. Just forget it.
    forget(&mut state.dbm, dst);
    
    // Tnum update
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(c) => {
            let c = if width == Width::W32 { (*c as u32) as u64 } else { *c as u64 };
            t.or_imm(c)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.or(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);
    
    // If tnum proves non-zero, inform DBM
    if new_t.is_definitely_nonzero() {
        assume_ge_const(&mut state.dbm, dst, 1);
    }
}

fn handle_neg(
    state: &mut State,
    width: Width,
    dst: Reg,
) {
    // Apply Negate Logic (swaps bounds)
    assign_neg(&mut state.dbm, dst);

    // Handle 32-bit Truncation/Extension
    if width == Width::W32 {
        bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
    }

    // Tnum update
    let t = state.get_tnum(dst);
    let new_t = if width == Width::W32 {
        t.trunc32()
    } else {
        // Conservative
        Tnum::unknown()
    };
    state.set_tnum(dst, new_t);
    
}

fn handle_shr(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            let shift_amount = if width == Width::W32 { k & 0x1F } else { k & 0x3F };
            
            let (old_lo, old_hi) = get_bounds(&state.dbm, dst);
            forget(&mut state.dbm, dst);
            
            // Logical right shift result is always non-negative
            assume_ge_const(&mut state.dbm, dst, 0);
            
            if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                if lo >= 0 {
                    // Non-negative range: shift preserves ordering
                    let new_lo = (lo as u64 >> shift_amount) as i64;
                    let new_hi = (hi as u64 >> shift_amount) as i64;
                    assume_ge_const(&mut state.dbm, dst, new_lo);
                    assume_le_const(&mut state.dbm, dst, new_hi);
                } else if shift_amount > 0 {
                    // Mixed/negative range, but shift reduces magnitude
                    let max_result = u64::MAX >> shift_amount;
                    if max_result <= i64::MAX as u64 {
                        assume_le_const(&mut state.dbm, dst, max_result as i64);
                    }
                }
            }
            
            if width == Width::W32 {
                apply_w32_truncation(&mut state.dbm, dst);
            }
            
            let t = state.get_tnum(dst);
            let new_t = t.shr_imm(shift_amount as u64);
            state.set_tnum(dst, new_t);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            
            // Result is non-negative
            assume_ge_const(&mut state.dbm, dst, 0);
            
            if width == Width::W32 {
                assume_le_const(&mut state.dbm, dst, u32::MAX as i64);
                state.set_tnum(dst, Tnum::u32_unknown());
            } else {
                state.set_tnum(dst, Tnum::unknown());
            }
        }
    }

    sync_tnum_to_dbm(state, dst);
}

fn handle_shl(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            
            // For W32, only lower 5 bits matter; for W64, lower 6 bits
            let shift_amount = if width == Width::W32 { k & 0x1F } else { k & 0x3F };
            
            let (old_lo, old_hi) = get_bounds(&state.dbm, dst);
            forget(&mut state.dbm, dst);
            
            if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                if lo >= 0 && shift_amount < 63 {
                    let max_safe: i64 = i64::MAX >> shift_amount;
                    
                    if hi <= max_safe {
                        assume_ge_const(&mut state.dbm, dst, lo << shift_amount);
                        assume_le_const(&mut state.dbm, dst, hi << shift_amount);
                    }
                }
            }
            
            if width == Width::W32 {
                apply_w32_truncation(&mut state.dbm, dst);
            }
            
            // Tnum update for immediate shift
            let t = state.get_tnum(dst);
            let new_t = t.shl_imm(shift_amount as u64);
            state.set_tnum(dst, new_t);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            
            // Tnum: shift by register = result is unknown
            // For W32: result is in [0, 0xFFFFFFFF]
            // For W64: result is in [0, u64::MAX]
            let new_t = if width == Width::W32 {
                assume_ge_const(&mut state.dbm, dst, 0);
                assume_le_const(&mut state.dbm, dst, u32::MAX as i64);
                Tnum::u32_unknown()
            } else {
                Tnum::unknown()
            };
            state.set_tnum(dst, new_t);
        }
    }

    sync_tnum_to_dbm(state, dst);
}

fn handle_mul(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            assign_mul_imm(&mut state.dbm, dst, *c);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    // Tnum update
    state.set_tnum(dst, Tnum::unknown());
}

fn handle_mod(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            if *c > 0 {
                forget(&mut state.dbm, dst);
                assume_ge_const(&mut state.dbm, dst, 0);
                assume_le_const(&mut state.dbm, dst, c - 1);
            } else {
                forget(&mut state.dbm, dst);
            }
        }
        Operand::Reg(r) => {
            let (r_lo, r_hi) = get_bounds(&state.dbm, *r);
            forget(&mut state.dbm, dst);
            
            match (r_lo, r_hi) {
                (Some(lo), Some(hi)) if lo > 0 => {
                    // Divisor is strictly positive, result is in [0, hi-1]
                    assume_ge_const(&mut state.dbm, dst, 0);
                    assume_le_const(&mut state.dbm, dst, hi - 1);
                }
                (Some(lo), _) if lo > 0 => {
                    // Divisor is positive but unbounded above
                    assume_ge_const(&mut state.dbm, dst, 0);
                }
                _ => {}
            }
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    // Tnum update
    state.set_tnum(dst, Tnum::unknown());
}

fn handle_div(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    // Division by zero already checked
    match src {
        Operand::Imm(imm) => assign_div_imm(&mut state.dbm, dst, *imm),
        Operand::Reg(r_src) => assign_div_reg(&mut state.dbm, dst, *r_src),
    }

    if width == Width::W32 {
        bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
    }

    // Tnum update
    state.set_tnum(dst, Tnum::unknown());
}

fn handle_rsh(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            let shift_amount = if width == Width::W32 { k & 0x1F } else { k & 0x3F };
            
            let (old_lo, old_hi) = get_bounds(&state.dbm, dst);
            forget(&mut state.dbm, dst);
            
            if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                if lo >= 0 {
                    // Logical right shift on non-negative values
                    let new_lo = (lo as u64 >> shift_amount) as i64;
                    let new_hi = (hi as u64 >> shift_amount) as i64;
                    assume_ge_const(&mut state.dbm, dst, new_lo);
                    assume_le_const(&mut state.dbm, dst, new_hi);
                } else {
                    // Mixed or negative range - result is non-negative but hard to bound precisely
                    assume_ge_const(&mut state.dbm, dst, 0);
                    if shift_amount > 0 {
                        assume_le_const(&mut state.dbm, dst, (u64::MAX >> shift_amount) as i64);
                    }
                }
            }
            
            if width == Width::W32 {
                apply_w32_truncation(&mut state.dbm, dst);
            }
            
            let t = state.get_tnum(dst);
            let new_t = t.rsh_imm(shift_amount as u64);
            state.set_tnum(dst, new_t);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            
            // Result is non-negative (logical shift)
            assume_ge_const(&mut state.dbm, dst, 0);
            
            if width == Width::W32 {
                assume_le_const(&mut state.dbm, dst, u32::MAX as i64);
                state.set_tnum(dst, Tnum::u32_unknown());
            } else {
                state.set_tnum(dst, Tnum::unknown());
            }
        }
    }

    sync_tnum_to_dbm(state, dst);
}

fn handle_arsh(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            let shift_amount = if width == Width::W32 { k & 0x1F } else { k & 0x3F };
            
            let old_tnum = state.get_tnum(dst);
            let (old_lo, old_hi) = get_bounds(&state.dbm, dst);
            forget(&mut state.dbm, dst);
            
            // Special case: ARSH 32 when lower 32 bits are known zeros
            // This detects the sign-extension pattern: LSH 32 followed by ARSH 32
            if width == Width::W64 && shift_amount == 32 {
                let lower_32_bits = 0xFFFFFFFF_u64;
                let lower_known_zero = (old_tnum.mask & lower_32_bits) == 0 
                                    && (old_tnum.value & lower_32_bits) == 0;
                if lower_known_zero {
                    // Result is a sign-extended i32
                    assume_ge_const(&mut state.dbm, dst, i32::MIN as i64);
                    assume_le_const(&mut state.dbm, dst, i32::MAX as i64);
                    
                    let new_t = old_tnum.arsh_imm(shift_amount as u64);
                    state.set_tnum(dst, new_t);
                    return;
                }
            }
            
            // Standard case: if we have valid signed bounds, shift them
            if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                let new_lo = lo >> shift_amount;
                let new_hi = hi >> shift_amount;
                assume_ge_const(&mut state.dbm, dst, new_lo);
                assume_le_const(&mut state.dbm, dst, new_hi);
            }
            
            if width == Width::W32 {
                apply_w32_truncation(&mut state.dbm, dst);
            }
            
            let new_t = old_tnum.arsh_imm(shift_amount as u64);
            state.set_tnum(dst, new_t);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            
            if width == Width::W32 {
                assume_ge_const(&mut state.dbm, dst, i32::MIN as i64);
                assume_le_const(&mut state.dbm, dst, i32::MAX as i64);
            }
            
            state.set_tnum(dst, Tnum::unknown());
        }
    }

    sync_tnum_to_dbm(state, dst);
}

/// Apply W32 truncation to a register's bounds.
/// If the current bounds exceed [0, 0xFFFFFFFF], widen to that range.
fn apply_w32_truncation(dbm: &mut Dbm, dst: Reg) {
    let (lo, hi) = get_bounds(dbm, dst);
    
    let safe = match (lo, hi) {
        (Some(l), Some(h)) => l >= 0 && h <= 0xFFFFFFFF,
        _ => false,
    };
    
    if !safe {
        forget(dbm, dst);
        assume_ge_const(dbm, dst, 0);
        assume_le_const(dbm, dst, 0xFFFFFFFF);
    }
}

/// Check if a register holds a "clean" pointer (offset == 0)
fn is_clean_ptr(types: &TypeState, reg: Reg) -> bool {
    match types.get(reg) {
        RegType::PtrToMapValue { offset: Some(0), .. } |
        RegType::PtrToStack { offset: Some(0), .. } |
        RegType::PtrToPacket { .. } => true,
        _ => false,
    }
}

fn is_div_by_zero(_dbm: &Dbm, src: &Operand) -> bool {
    match src {
        Operand::Imm(k) => *k == 0,
        // We don't need to report potential division by zero for register operands here.
        Operand::Reg(_) => false
    }
}

fn sync_tnum_to_dbm(state: &mut State, reg: Reg) {
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
