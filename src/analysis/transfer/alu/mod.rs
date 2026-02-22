use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/alu/mod.rs

pub mod arithmetic;
pub mod bitwise;
pub mod shift;
pub mod validation;
pub mod helpers;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType };
use crate::ast::{AluOp, Operand, Width};
use crate::analysis::machine::reg::Reg;
use log::error;

use super::types::update_alu_types;
use super::common::{check_reg_readable, check_operand_readable, check_reg_writable};

// Re-export public transfer function
pub(crate) fn transfer_alu(
    env: &mut VerifierEnv,
    mut state: State,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: Operand,
) -> Vec<State> {
    // 1. Check readability
    if op != AluOp::Mov {
        if !check_reg_readable(env, &state, dst) {
            return vec![];
        }
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
        Operand::Reg(r) => state.types.get(r).clone()
    };
    let dst_type = state.types.get(dst);

    if !validation::check_ptr_arithmetic(env, &state, op, width, dst, &dst_type, &src_type, &src) {
        env.fail(VerificationError::InvalidPointerArithmetic { pc: state.pc });
        return vec![];
    }

    // 4. Division by zero check
    if op == AluOp::Div && validation::is_div_by_zero(&state.dbm, &src) {
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
    update_alu_types(env, &in_types, &mut state.types, &state.dbm, width, op, dst, &src, state.pc);

    // 7. Post-operation consistency check
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
