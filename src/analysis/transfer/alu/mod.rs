use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/alu/mod.rs

pub mod arithmetic;
pub mod bitwise;
pub mod helpers;
pub mod shift;
pub mod validation;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Operand, SxWidth, Width};
use crate::domains::tnum::Tnum;
use log::error;

use super::common::{check_operand_readable, check_reg_readable, check_reg_writable};
use super::types::update_alu_types;

pub(crate) fn transfer_alu(
    env: &mut VerifierEnv,
    mut state: State,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: Operand,
) -> Vec<State> {
    // 1. Check readability
    if op != AluOp::Mov && !check_reg_readable(env, &state, dst) {
        return vec![];
    }
    if !check_operand_readable(env, &state, &src) {
        return vec![];
    }

    // 2. Check destination writability
    if !check_reg_writable(env, &state, dst) {
        return vec![];
    }

    let in_types = state.types.clone();

    // 3. Pointer arithmetic validation
    let src_type = match src {
        Operand::Imm(_) => RegType::ScalarValue,
        Operand::Reg(r) => state.types.get(r),
    };
    let dst_type = state.types.get(dst);

    if !validation::check_ptr_arithmetic(env, &state, op, width, dst, &dst_type, &src_type, &src) {
        env.fail(VerificationError::InvalidPointerArithmetic { pc: state.pc });
        return vec![];
    }

    // 4. Division by zero check
    if op == AluOp::Div && validation::is_div_by_zero(&src) {
        env.fail(VerificationError::DivideByZero { pc: state.pc });
        return vec![];
    }

    // 5. Execute operation
    match op {
        AluOp::Add => arithmetic::handle_add(env, &mut state, &in_types, width, dst, &src),
        AluOp::Sub => arithmetic::handle_sub(env, &mut state, &in_types, width, dst, &src),
        AluOp::Mov => bitwise::handle_mov(&mut state, width, dst, &src),
        AluOp::And => bitwise::handle_and(&mut state, width, dst, &src),
        AluOp::Or => bitwise::handle_or(&mut state, width, dst, &src),
        AluOp::Neg => arithmetic::handle_neg(&mut state, width, dst),
        AluOp::Shr => shift::handle_shr(&mut state, width, dst, &src),
        AluOp::Shl => shift::handle_shl(&mut state, width, dst, &src),
        AluOp::Mul => arithmetic::handle_mul(&mut state, width, dst, &src),
        AluOp::Mod => arithmetic::handle_mod(&mut state, width, dst, &src),
        AluOp::Div => arithmetic::handle_div(&mut state, width, dst, &src),
        AluOp::Arsh => shift::handle_arsh(&mut state, width, dst, &src),
        AluOp::Rsh => shift::handle_rsh(&mut state, width, dst, &src),
        AluOp::Lsh => shift::handle_shl(&mut state, width, dst, &src),
        AluOp::Xor => bitwise::handle_xor(&mut state, width, dst, &src),
    }

    // 6. Update types
    // Clone domain before mutably borrowing types to avoid borrow conflict
    let domain = state.domain.clone();
    let pc = state.pc;
    update_alu_types(
        env,
        &in_types,
        &mut state.types,
        &domain,
        width,
        op,
        dst,
        &src,
        pc,
    );

    // 6.5 Scalar ID lifecycle: link on identity copies, clear on value changes.
    // Done after update_alu_types so we see the final destination type.
    if state.types.get(dst) == crate::analysis::machine::reg_types::RegType::ScalarValue {
        match (op, &src) {
            (AluOp::Mov, Operand::Reg(r)) if width == crate::ast::Width::W64 => {
                // 64-bit reg→reg copy: dst shares src's scalar id.
                state.link_scalar_id(dst, *r);
            }
            _ => {
                // Immediate copy, 32-bit MOV (zero-extend changes value), or any
                // arithmetic/bitwise/shift op: value at dst is now different from
                // any prior copy chain, so unlink.
                state.clear_scalar_id(dst);
            }
        }
    } else {
        // dst became a pointer — no scalar id.
        state.clear_scalar_id(dst);
    }

    // 7. Post-operation consistency check
    if state.domain.is_inconsistent() {
        env.fail(VerificationError::DbmInconsistent { pc: state.pc });
        let rel = state.domain.relations_str();
        let zone_part = if rel.is_empty() {
            String::new()
        } else {
            format!("  Rel:    {}\n", rel)
        };
        error!(target: "app",
            "[Verifier] Domain became inconsistent at pc {}\n  Ranges: {}\n{}",
            state.pc,
            state.reg_ranges_str(),
            zone_part,
        );
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

/// Sign-extending move (MOVSX, v6.6).
///
/// Width semantics:
/// - MOV64SX (ALU64): sign-extend low `src_bits` of src to full 64-bit dst.
///   Result range: [-(2^(n-1)), 2^(n-1) - 1] where n = src_bits.bits().
/// - MOV32SX (ALU32): sign-extend low `src_bits` of src to a 32-bit value,
///   then zero-extend to the 64-bit dst. The 32-bit result as an unsigned
///   value lies in [0, 2^32 - 1] but its set is disjoint — either the
///   non-negative half of the sign-extended range or a high wrap. We
///   conservatively clamp to the u32 range and rely on tnum imprecision
///   for further reasoning.
///
/// MOVSX always produces a scalar; pointer dst types are scrubbed.
pub(crate) fn transfer_mov_sx(
    env: &mut VerifierEnv,
    mut state: State,
    width: Width,
    src_bits: SxWidth,
    dst: Reg,
    src: Operand,
) -> Vec<State> {
    if !check_operand_readable(env, &state, &src) {
        return vec![];
    }
    if !check_reg_writable(env, &state, dst) {
        return vec![];
    }

    state.types.set(dst, RegType::ScalarValue);
    state.domain.forget(dst);

    match width {
        Width::W64 => {
            let (lo, hi) = match src_bits {
                SxWidth::B8 => (i8::MIN as i64, i8::MAX as i64),
                SxWidth::B16 => (i16::MIN as i64, i16::MAX as i64),
                SxWidth::B32 => (i32::MIN as i64, i32::MAX as i64),
            };
            state.domain.assume_ge_imm(dst, lo);
            state.domain.assume_le_imm(dst, hi);
        }
        Width::W32 => {
            // 32-bit MOVSX: sign-extend src_bits → 32-bit, then zero-extend
            // to 64-bit. The 64-bit view is in [0, 2^32 - 1].
            state.domain.assume_ge_imm(dst, 0);
            state.domain.assume_le_imm(dst, 0xFFFF_FFFF);
        }
    }
    state.set_tnum(dst, Tnum::unknown());
    // MOVSX always produces a fresh unknown scalar — not a copy of src.
    state.alloc_scalar_id(dst);

    let next_pc = if env.invalid_pc_set.contains(&(state.pc + 1)) {
        state.pc + 2
    } else {
        state.pc + 1
    };
    state.pc = next_pc;
    vec![state]
}
