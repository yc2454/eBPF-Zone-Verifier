// src/analysis/transfer/alu.rs
//
// ALU instruction handlers (add, sub, mov, and, or, mul, div, etc.)

use crate::analysis::machine::env::{VerifierEnv, VerificationError};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType, TypeState };
use crate::ast::{AluOp, Operand, Width};
use crate::zone::domain::{
    REG_ENV, Reg, assign_add_imm, assign_add_reg, assign_and_mask, assign_div_imm, assign_div_reg, assign_eq, assign_mul_imm, assign_neg, assign_sub_reg, assign_zero, assume_eq_const, assume_ge_const, assume_le_const, bit_and_const, forget, get_bounds, get_constant_value, get_relative_bound, link_regs_with_offset, set_bounds
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

    if !check_ptr_arithmetic(env, &state, op, width, dst, &dst_type, &src_type, &src) {
        env.fail(VerificationError::InvalidPointerArithmetic { pc: state.pc });
        return vec![];
    }

    // Early check for division by zero
    if op == AluOp::Div && is_div_by_zero(&state.dbm, &src) {
        env.fail(VerificationError::DivideByZero { pc: state.pc });
        return vec![];
    }

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
        AluOp::Xor => handle_xor(&mut state, width, dst, &src),
    }

    update_alu_types(env, &in_types, &mut state.types, &state.dbm, width, op, dst, &src, state.pc);

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
    env: &mut VerifierEnv,
    state: &State,
    op: AluOp,
    width: Width,
    dst: Reg,
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

    let src_min = match src {
        Operand::Imm(k) => *k,
        Operand::Reg(r) => {
            let (min_opt, _) = get_bounds(&state.dbm, *r);
            match min_opt {
                Some(min) => min,
                None => -INF,
            }
        }
    };

    let (dst_min, dst_max) = get_bounds(&state.dbm, dst);
    let dst_min = dst_min.unwrap_or(-INF);
    let dst_max = dst_max.unwrap_or(INF);

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
                if env.ctx.is_privileged() {
                    return true;
                }
                RegType::is_same_pointer_type(dst_type, src_type) || 
                (matches!(dst_type, RegType::PtrToPacketEnd) && matches!(src_type, RegType::PtrToPacket { .. }))
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
                // 32-bit ALU on pointers yields scalar semantics in this verifier.
                // Type update later forces dst to ScalarValue for W32 ops.
                // Do not apply 64-bit pointer-offset limits in this path.
                if width == Width::W32 {
                    return true;
                }
                if src_min < -constants::MAX_VAR_OFF || src_max > constants::MAX_VAR_OFF {
                    return false;
                }
                if matches!(dst_type, RegType::PtrToMapValue { .. }) {
                    // The verifier identifies 0xFFFFFFFF (4294967295) as a forbidden offset
                    if src_max > i32::MAX as i64 {
                        error!("Forbidden offset {}", src_max);
                        return false;
                    }
                }
                if op == AluOp::Sub && matches!(dst_type, RegType::PtrToStack { .. }) {
                    return  false;
                }
                true
            },
            // Unary negation of a pointer is accepted but scalarizes the result.
            // Type transition is handled in update_alu_types.
            AluOp::Neg => true,
            AluOp::Mov | AluOp::And => true, 
            _ => { false }
        }
    }
    // 4. Scalar <op> Pointer (dst=Scalar, src=Ptr)
    else {
        match op {
            // Scalar + Ptr is allowed (Commutative).
            // (Result is Ptr, handled by caller)
            AluOp::Add => {
                // Keep offset sanitization symmetric with ptr += scalar.
                // If scalar offset is too large, the resulting pointer arithmetic
                // is considered unsafe.
                if dst_min < -constants::MAX_VAR_OFF || dst_max > constants::MAX_VAR_OFF {
                    return false;
                }
                // Packet pointers are more restrictive and must stay within
                // verifier packet offset limits.
                if src_type.is_packet_ptr()
                    && (dst_min < -constants::MAX_PACKET_OFF || dst_max > constants::MAX_PACKET_OFF)
                {
                    return false;
                }
                true
            },
            
            // Scalar - Ptr is FORBIDDEN.
            AluOp::Sub => width == Width::W32,

            // Mov Scalar, Ptr is allowed (dst becomes Ptr).
            AluOp::Mov => true,
            
            // Scalar * Ptr, etc. forbidden.
            _ => false
        }
    }
}

/// Check pointer bounds after arithmetic operations.
pub(crate) fn check_ptr_bounds(
    _env: &mut VerifierEnv,
    state: &mut State,
    reg: Reg,
) { 
    match state.types.get(reg) {
        RegType::PtrToPacket { .. } => {
            let packet_start_reg_op = REG_ENV.all().iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacket));
            if !packet_start_reg_op.is_none()  {
                let packet_start_reg = packet_start_reg_op.unwrap();
                if let (Some(_), Some(packet_offset)) = get_relative_bound(&state.dbm, reg, *packet_start_reg) {
                    if packet_offset > constants::MAX_PACKET_OFF as i64 {
                        forget(&mut state.dbm, reg);
                    }
                }
            }
        }
        RegType::PtrToPacketMeta { .. } => {
            let packet_start_reg_op = REG_ENV.all().iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacketMeta));
            if !packet_start_reg_op.is_none()  {
                let packet_start_reg = packet_start_reg_op.unwrap();
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
            let src_is_ptr = in_types.get(*r).is_pointer();
            let dst_is_ptr = in_types.get(dst).is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr += scalar: preserve relational info if possible
                let (lo, hi) = get_bounds(&state.dbm, *r);
                if lo == hi && lo.is_some() {
                    // Known constant: shift all relations exactly
                    assign_add_imm(&mut state.dbm, dst, lo.unwrap());
                } else {
                    // Non-constant: fall back to interval
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(dst)) {
                        forget(&mut state.dbm, dst);
                        set_bounds(&mut state.dbm, dst, off, off);
                    }
                    assign_add_reg(&mut state.dbm, dst, *r);
                }
            } else if src_is_ptr && !dst_is_ptr {
                // scalar += ptr (test18 pattern)
                let (lo, hi) = get_bounds(&state.dbm, dst);
                if lo == hi && lo.is_some() {
                    link_regs_with_offset(&mut state.dbm, dst, *r, lo.unwrap());
                } else {
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(*r)) {
                        forget(&mut state.dbm, *r);
                        set_bounds(&mut state.dbm, *r, off, off);
                    }
                    forget(&mut state.dbm, dst);
                    if let Some(hi) = hi {
                        state.dbm.add_constraint(dst, *r, hi);
                    }
                    if let Some(lo) = lo {
                        if lo > i64::MIN {
                            state.dbm.add_constraint(*r, dst, -lo);
                        }
                    }
                    state.dbm.close();
                }
            } else {
                // scalar += scalar, ptr += ptr, etc.
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

    sync_tnum_to_dbm(state, dst);
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
            let dst_is_ptr = in_types.get(dst).is_pointer();
            let src_is_ptr = in_types.get(*r).is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr -= scalar: try to preserve relational info
                let const_value = get_constant_value(&state.dbm, *r);
                
                if const_value.is_some() {
                    // Scalar is a known constant: exact relational shift
                    assign_add_imm(&mut state.dbm, dst, -const_value.unwrap());
                } else {
                    // Bounded but not constant: fall back to interval
                    assign_sub_reg(&mut state.dbm, dst, *r);
                }
            } else {
                // scalar -= scalar, scalar -= ptr, ptr -= ptr
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

    let dst_is_ptr = in_types.get(dst).is_pointer();
    let src_is_ptr = match src {
        Operand::Imm(_) => false,
        Operand::Reg(r) => in_types.get(*r).is_pointer()
    };
    if !(dst_is_ptr && src_is_ptr) {
        check_ptr_bounds(env, state, dst);
    }

    sync_tnum_to_dbm(state, dst);
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
            let v = if width == Width::W32 {
                (*c as u32) as u64
            } else {
                *c as u64
            };
            state.set_tnum(dst, Tnum::constant(v));
        }
        Operand::Reg(r) => {
            let t = if width == Width::W32 {
                state.get_tnum(*r).trunc32()
            } else {
                state.get_tnum(*r)
            };
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
                if dst == *r {
                    return;
                }
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

    sync_tnum_to_dbm(state, dst);
}

fn handle_xor(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    // Conservative update to the DBM - forget it
    forget(&mut state.dbm, dst);
    
    // Tnum update
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(c) => {
            let c = if width == Width::W32 { (*c as u32) as u64 } else { *c as u64 };
            t.xor_imm(c)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.xor(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);

    sync_tnum_to_dbm(state, dst);
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
            let old_tnum = state.get_tnum(dst);
            forget(&mut state.dbm, dst);
            
            // For W32, truncate to 32 bits first, then shift
            if width == Width::W32 {
                // Truncate tnum to 32 bits first
                let truncated_tnum = old_tnum.trunc32();
                let trunc_lo = truncated_tnum.min_value();
                let trunc_hi = truncated_tnum.max_value();
                
                // Now shift
                let new_lo = (trunc_lo >> shift_amount) as i64;
                let new_hi = (trunc_hi >> shift_amount) as i64;
                
                assume_ge_const(&mut state.dbm, dst, new_lo);
                assume_le_const(&mut state.dbm, dst, new_hi);
                
                let new_tnum = truncated_tnum.shr_imm(shift_amount as u64);
                state.set_tnum(dst, new_tnum);
            } else {
                // W64: shift full 64-bit value
                assume_ge_const(&mut state.dbm, dst, 0);
                
                if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                    if lo >= 0 {
                        let new_lo = (lo as u64 >> shift_amount) as i64;
                        let new_hi = (hi as u64 >> shift_amount) as i64;
                        assume_ge_const(&mut state.dbm, dst, new_lo);
                        assume_le_const(&mut state.dbm, dst, new_hi);
                    } else if shift_amount > 0 {
                        let max_result = u64::MAX >> shift_amount;
                        if max_result <= i64::MAX as u64 {
                            assume_le_const(&mut state.dbm, dst, max_result as i64);
                        }
                    }
                }
                
                let new_tnum = old_tnum.shr_imm(shift_amount as u64);
                state.set_tnum(dst, new_tnum);
            }
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
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
            let shift_amount = if width == Width::W32 { k & 0x1F } else { k & 0x3F };
            
            let (old_lo, old_hi) = get_bounds(&state.dbm, dst);
            let old_tnum = state.get_tnum(dst);
            forget(&mut state.dbm, dst);
            
            if width == Width::W32 {
                // Truncate to 32 bits first, then shift
                let truncated_tnum = old_tnum.trunc32();
                let trunc_lo = truncated_tnum.min_value();
                let trunc_hi = truncated_tnum.max_value();
                
                // Shift and check for overflow within 32 bits
                if shift_amount < 32 {
                    let max_safe = u32::MAX as u64 >> shift_amount;
                    if trunc_hi <= max_safe {
                        let new_lo = ((trunc_lo << shift_amount) & 0xFFFFFFFF) as i64;
                        let new_hi = ((trunc_hi << shift_amount) & 0xFFFFFFFF) as i64;
                        assume_ge_const(&mut state.dbm, dst, new_lo);
                        assume_le_const(&mut state.dbm, dst, new_hi);
                    } else {
                        // Could overflow, result in [0, 0xFFFFFFFF]
                        assume_ge_const(&mut state.dbm, dst, 0);
                        assume_le_const(&mut state.dbm, dst, u32::MAX as i64);
                    }
                } else {
                    // Shift by 32+ clears everything
                    assume_eq_const(&mut state.dbm, dst, 0);
                }
                
                let new_tnum = truncated_tnum.shl_imm(shift_amount as u64).trunc32();
                state.set_tnum(dst, new_tnum);
            } else {
                // W64
                if shift_amount == 32 {
                // Special case for sign-extension pattern (shl 32 + arsh 32)
                // Preserve bounds if value fits in i32 range (even if negative)
                if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                    if lo >= i32::MIN as i64 && hi <= i32::MAX as i64 {
                        assume_ge_const(&mut state.dbm, dst, lo << 32);
                        assume_le_const(&mut state.dbm, dst, hi << 32);
                    }
                }
            } else if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                if lo >= 0 && shift_amount < 64 {
                    let max_safe: i64 = if shift_amount == 63 { 0 } else { i64::MAX >> shift_amount };
                    if hi <= max_safe {
                        assume_ge_const(&mut state.dbm, dst, lo << shift_amount);
                        assume_le_const(&mut state.dbm, dst, hi << shift_amount);
                    }
                }
            }

            let new_tnum = old_tnum.shl_imm(shift_amount as u64);
            state.set_tnum(dst, new_tnum);
            }
            
            sync_tnum_to_dbm(state, dst);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            
            if width == Width::W32 {
                assume_ge_const(&mut state.dbm, dst, 0);
                assume_le_const(&mut state.dbm, dst, u32::MAX as i64);
                state.set_tnum(dst, Tnum::u32_unknown());
            } else {
                state.set_tnum(dst, Tnum::unknown());
            }
            
            sync_tnum_to_dbm(state, dst);
        }
    }
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
            
            if width == Width::W32 {
                // Truncate to 32 bits, interpret as signed i32, then arithmetic shift
                let truncated_tnum = old_tnum.trunc32();
                
                // For ARSH32, result is sign-extended from 32-bit result
                // Result range is [-2^31, 2^31-1] after sign extension
                // But we can be more precise if we know the input range
                
                let trunc_lo = truncated_tnum.min_value() as u32;
                let trunc_hi = truncated_tnum.max_value() as u32;
                
                // Interpret as signed and shift
                let signed_lo = trunc_lo as i32;
                let signed_hi = trunc_hi as i32;
                
                if signed_lo <= signed_hi {
                    // Normal range
                    let new_lo = (signed_lo >> shift_amount) as u32 as i64;
                    let new_hi = (signed_hi >> shift_amount) as u32 as i64;
                    assume_ge_const(&mut state.dbm, dst, new_lo);
                    assume_le_const(&mut state.dbm, dst, new_hi);
                } else {
                    // Wrapped range (spans sign boundary), be conservative
                    assume_ge_const(&mut state.dbm, dst, 0);
                    assume_le_const(&mut state.dbm, dst, u32::MAX as i64);
                }
                
                // 1. Check the 32-bit sign bit (Bit 31)
                let sign_bit = (truncated_tnum.value >> 31) & 1;
                let sign_unknown = (truncated_tnum.mask >> 31) & 1;

                // 2. Sign-Extend the Tnum to 64 bits
                // We need Bit 63 to match Bit 31 so arsh_imm works correctly.
                let mut sext_tnum = truncated_tnum; 
                let upper_mask = 0xFFFFFFFF00000000;

                if sign_unknown != 0 {
                    // Sign is unknown -> Upper bits become unknown
                    sext_tnum.mask |= upper_mask;
                    sext_tnum.value &= !upper_mask;
                } else if sign_bit != 0 {
                    // Sign is 1 -> Upper bits become 1
                    sext_tnum.value |= upper_mask;
                    // (Mask remains 0 for upper bits because we know they are 1s)
                }
                // If sign is 0, upper bits are already 0 from trunc32, so we do nothing.

                // 3. Perform the 64-bit Arith Shift
                let arsh_result = sext_tnum.arsh_imm(shift_amount as u64);

                // 4. Zero-Extend the result back to 32 bits (BPF Requirement)
                // BPF writes to w0 always zero-extend to r0.
                let new_tnum = arsh_result.trunc32();

                state.set_tnum(dst, new_tnum);
            } else {
                // W64
                // Special case: ARSH 32 when lower 32 bits are known zeros
                // This detects the sign-extension pattern: LSH 32 followed by ARSH 32
                if shift_amount == 32 {
                    let lower_32_bits = 0xFFFFFFFF_u64;
                    let lower_known_zero = (old_tnum.mask & lower_32_bits) == 0 
                                        && (old_tnum.value & lower_32_bits) == 0;
                    if lower_known_zero {
                        // Sign-extension pattern: the result equals the original value
                        // before shl 32, interpreted as a signed 32-bit integer.
                        //
                        // The DBM bounds (old_lo, old_hi) are the bounds AFTER shl 32.
                        // Arithmetic shift them back by 32 to recover original bounds,
                        // clamped to i32 range.
                        let new_lo = match old_lo {
                            Some(lo) => (lo >> 32).max(i32::MIN as i64),
                            None => i32::MIN as i64,
                        };
                        let new_hi = match old_hi {
                            Some(hi) => (hi >> 32).min(i32::MAX as i64),
                            None => i32::MAX as i64,
                        };
                        
                        assume_ge_const(&mut state.dbm, dst, new_lo);
                        assume_le_const(&mut state.dbm, dst, new_hi);
                        
                        let new_tnum = old_tnum.arsh_imm(shift_amount as u64);
                        state.set_tnum(dst, new_tnum);
                        sync_tnum_to_dbm(state, dst);
                        return;
                    }
                }
                
                // Standard case
                if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                    let new_lo = lo >> shift_amount;
                    let new_hi = hi >> shift_amount;
                    assume_ge_const(&mut state.dbm, dst, new_lo);
                    assume_le_const(&mut state.dbm, dst, new_hi);
                }
                
                let new_tnum = old_tnum.arsh_imm(shift_amount as u64);
                state.set_tnum(dst, new_tnum);
            }
            
            sync_tnum_to_dbm(state, dst);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            
            if width == Width::W32 {
                // Result is sign-extended i32
                assume_ge_const(&mut state.dbm, dst, i32::MIN as i64);
                assume_le_const(&mut state.dbm, dst, i32::MAX as i64);
            }
            // For W64 variable ARSH, can't bound without knowing shift amount
            
            state.set_tnum(dst, Tnum::unknown());
            sync_tnum_to_dbm(state, dst);
        }
    }
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

/// Apply W32 truncation to a register's bounds.
/// If the current bounds exceed [0, 0xFFFFFFFF], widen to that range.
fn apply_w32_truncation(dbm: &mut Dbm, dst: Reg) {
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
