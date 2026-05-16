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
            // The kernel's `check_reg_arg` rejects an uninitialized
            // register read with `-EACCES` ("R%d !read_ok")
            // unconditionally. A `has_conflict_eq()` path-unreachable
            // discharge was tried here (BCF set1/0014 framing) but it
            // is UNSOUND for this corpus: `has_conflict_eq` over the
            // full `path_conds` false-positives (structurally-equal
            // but semantically-distinct operands → a fake `r==c ∧ r!=c`
            // contradiction), declaring KERNEL-REACHABLE `!read_ok`
            // paths "unreachable" and silently dropping them →
            // 24 measured false accepts across cilium (sock_addr
            // connect/sendmsg `R1 !read_ok`, overlay `R5 !read_ok`);
            // per-program kernel oracle confirms the kernel REJECTS
            // these. A faithfulness defect outranks the speculative
            // discharge — `!read_ok` ⇒ reject, mirroring the kernel.
            // (`access_path_unreach` discharges via the generic-load
            // site (`access.rs`, commit f274132), NOT here, so it is
            // unaffected.)
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
