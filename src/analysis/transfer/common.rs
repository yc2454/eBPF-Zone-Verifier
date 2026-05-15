use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/common.rs
//
// Common validation utilities shared across transfer functions

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::Operand;

/// Checks if a register is readable (has been initialized).
/// Returns true if readable, false if not (and records error).
pub(crate) fn check_reg_readable(env: &mut VerifierEnv, state: &State, reg: Reg) -> bool {
    // R10 (frame pointer) is always readable
    if reg == Reg::R10 {
        return true;
    }

    let reg_type = state.types.get(reg);

    match reg_type {
        RegType::NotInit => {
            // BCF set1/0014: the kernel's `check_reg_arg` on `-EACCES`
            // (the `!read_ok` rejection) calls `bcf_prove_unreachable`
            // → `bcf_track(base=NULL)` → `detect_conflict_eq`. Same
            // path-unreachable mechanism as the generic-load site
            // (commit f274132), different rejection site. If the path's
            // accumulated branch conditions are syntactically
            // contradictory, this uninit-reg path is dead — discharge
            // it (no solver, no bundle) by returning unreadable WITHOUT
            // env.fail. Every caller bails `return vec![]` on false, so
            // the path is dropped (the kernel's `goto process_bpf_exit`).
            if let Some(bcf) = state.bcf.as_ref()
                && bcf.has_conflict_eq()
            {
                log::info!(
                    target: "app",
                    "[bcf] detect_conflict_eq: reversed-opcode path conflict at pc {} ({:?} !read_ok) — path unreachable, dropping (no cvc5, no bundle)",
                    state.pc, reg
                );
                env.bcf_path_unreachable = true;
                return false;
            }
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

pub(crate) fn check_reg_writable(env: &mut VerifierEnv, state: &State, reg: Reg) -> bool {
    if reg == Reg::R10 {
        env.fail(VerificationError::RegisterNotWritable { pc: state.pc, reg });
        return false;
    }
    true
}
