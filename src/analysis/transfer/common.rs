// src/analysis/transfer/common.rs
//
// Common validation utilities shared across transfer functions

use crate::analysis::machine::env::{VerifierEnv, VerificationError};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::RegType;
use crate::ast::Operand;
use crate::zone::domain::Reg;

/// Checks if a register is readable (has been initialized).
/// Returns true if readable, false if not (and records error).
pub(crate) fn check_reg_readable(
    env: &mut VerifierEnv,
    state: &State,
    reg: Reg,
) -> bool {
    // R10 (frame pointer) is always readable
    if reg == Reg::R10 {
        return true;
    }
    
    let reg_type = state.types.get(reg);
    
    match reg_type {
        RegType::NotInit => {
            env.fail(VerificationError::RegisterNotReadable { pc: state.pc, reg });
            false
        }
        _ => true,
    }
}

/// Checks if an operand is readable.
/// For immediate operands, always returns true.
/// For register operands, checks if the register is initialized.
pub(crate) fn check_operand_readable(
    env: &mut VerifierEnv,
    state: &State,
    operand: &Operand,
) -> bool {
    match operand {
        Operand::Imm(_) => true,
        Operand::Reg(r) => check_reg_readable(env, state, *r),
    }
}

/// Checks that all registers in a slice are readable.
/// Returns true if all are readable, false otherwise.
pub(crate) fn check_regs_readable(
    env: &mut VerifierEnv,
    state: &State,
    regs: &[Reg],
) -> bool {
    let mut all_ok = true;
    for reg in regs {
        if !check_reg_readable(env, state, *reg) {
            all_ok = false;
            // Don't break early - report all errors
        }
    }
    all_ok
}

pub(crate) fn check_reg_writable(
    env: &mut VerifierEnv,
    state: &State,
    reg: Reg,
) -> bool {
    if reg == Reg::R10 {
        env.fail(VerificationError::RegisterNotWritable { pc: state.pc, reg });
        return false
    }
    true
}
