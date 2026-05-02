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

    // Bucket F-D: clear `var_off_contributor[dst]` before the op runs;
    // `handle_add` re-sets it for the `ptr += scalar` case. Any other op
    // (Mov, Sub, And, Mul, etc.) invalidates the contributor link.
    state.var_off_contributor.remove(&dst);

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
    // Also forward-propagate the W2.2 precision mark: any ALU result whose
    // computation drew on a precise operand is itself precision-critical.
    let dst_prev_precise = state.is_reg_precise(dst);
    let src_precise = match &src {
        Operand::Reg(r) => state.is_reg_precise(*r),
        Operand::Imm(_) => false,
    };
    if state.types.get(dst) == crate::analysis::machine::reg_types::RegType::ScalarValue {
        match (op, &src) {
            (AluOp::Mov, Operand::Reg(r)) if width == crate::ast::Width::W64 => {
                // 64-bit reg→reg copy: dst shares src's scalar id.
                state.link_scalar_id(dst, *r);
                // MOV overwrites dst entirely — precision follows src.
                if src_precise {
                    state.mark_reg_precise(dst);
                } else {
                    state.clear_reg_precise(dst);
                }
            }
            (AluOp::Mov, _) => {
                // 32-bit MOV zero-extends (value changes) or MOV with immediate
                // (value is a constant): drop dst's copy chain and any prior
                // precision mark; the new value doesn't depend on the old one.
                state.clear_scalar_id(dst);
                if matches!(&src, Operand::Reg(_)) && src_precise {
                    // 32-bit reg→reg mov: still propagate precision forward
                    // because dst's value is derived from src.
                    state.mark_reg_precise(dst);
                } else {
                    state.clear_reg_precise(dst);
                }
            }
            _ => {
                // Arithmetic/bitwise/shift op: value at dst is now different
                // from any prior copy chain, so unlink.
                state.clear_scalar_id(dst);
                if src_precise || dst_prev_precise {
                    state.mark_reg_precise(dst);
                } else {
                    state.clear_reg_precise(dst);
                }
            }
        }
    } else {
        // dst became a pointer — no scalar id, and precision doesn't apply
        // (we only track scalar precision for W2.3 pruning).
        state.clear_scalar_id(dst);
        state.clear_reg_precise(dst);
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
            // 32-bit MOVSX: sign-extend low src_bits of src → 32-bit signed,
            // then zero-extend to 64-bit.  Conservative default [0, 2^32-1].
            //
            // Precision: when the source interval is entirely within one
            // half of the N-bit signed range we can compute exact bounds:
            //
            //  Positive half [0, 2^(N-1)-1]: sign-extension is a no-op
            //    → result bounds equal source bounds.
            //  Negative half [2^(N-1), 2^N-1]: every value sign-extends to
            //    v | ~mask in 32-bit (i.e., v + (0x1_0000_0000 - 2^N)).
            //    Since the high bits of the result are constant 0xFF…,
            //    the result range is [src_lo + ext, src_hi + ext].
            let n = match src_bits {
                SxWidth::B8 => 8i64,
                SxWidth::B16 => 16i64,
                SxWidth::B32 => 32i64,
            };
            let max_positive = (1i64 << (n - 1)) - 1; // 127 / 32767 / 2^31-1
            let mask = (1i64 << n) - 1;               // 255 / 65535 / 2^32-1
            let sign_bit = 1i64 << (n - 1);            // 128 / 32768 / 2^31
            // Amount to add when zero-extending a negative N-bit value to 32-bit:
            // fills the bits above N with 1s (two's-complement).
            let ext = (0x1_0000_0000i64) - (1i64 << n); // 0xFFFF_FF00 for S8

            let (src_lo, src_hi) = match &src {
                Operand::Reg(r) => state.domain.get_interval(*r),
                Operand::Imm(v) => (*v, *v),
            };

            if src_lo >= 0 && src_hi <= max_positive {
                // Positive half: sign-extension leaves value unchanged.
                state.domain.assume_ge_imm(dst, src_lo);
                state.domain.assume_le_imm(dst, src_hi);
            } else if src_lo >= sign_bit && src_hi <= mask {
                // Negative half: all values have the sign bit set; adding `ext`
                // fills the upper bits with 1s to produce the 32-bit negative
                // representation, then zero-extends to u64.
                state.domain.assume_ge_imm(dst, src_lo + ext);
                state.domain.assume_le_imm(dst, src_hi + ext);
            } else {
                state.domain.assume_ge_imm(dst, 0);
                state.domain.assume_le_imm(dst, 0xFFFF_FFFF);
            }
        }
    }
    state.set_tnum(dst, Tnum::unknown());
    // MOVSX always produces a fresh unknown scalar — not a copy of src.
    state.alloc_scalar_id(dst);
    // The old dst value is gone; any prior precision mark doesn't transfer.
    state.clear_reg_precise(dst);

    let next_pc = if env.invalid_pc_set.contains(&(state.pc + 1)) {
        state.pc + 2
    } else {
        state.pc + 1
    };
    state.pc = next_pc;
    vec![state]
}
