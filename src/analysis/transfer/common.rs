use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/common.rs
//
// Common validation utilities shared across transfer functions

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::Operand;

/// Eagerly materialize `reg`'s BCF expression on a source-operand read.
///
/// Faithful mirror of the kernel's `check_reg_arg` SRC_OP hook
/// (verifier.c:4083-4087):
///
/// ```c
/// if (env->bcf.tracking && !tnum_is_const(reg->var_off)) {
///     bcf_reg_expr(env, reg, false);
/// ```
///
/// The kernel binds a non-constant register's `bcf_expr` (emitting its
/// `bcf_bound_reg` bound predicates into `br_conds`) the FIRST time the
/// register is read as a source operand of ANY instruction — including a
/// plain spill/store, NOT only at ALU/branch sites. Without this, zovia
/// only materialized lazily inside the ALU/branch mirrors, so a value
/// spilled before its first branch (e.g. cilium wireguard's pc38 u16
/// load `w1=*(u16*)(r4+4)` spilled at pc39) never got its umax bound
/// pred — diverging from the kernel's leading `JLE(v,65535)` clause.
///
/// Scoped to SCALAR non-const regs: the kernel's `!tnum_is_const`
/// guard skips constants, and pointer regs almost always have a const
/// `var_off` (so the kernel skips them too); the rare PTR_TO_STACK
/// variable-offset case is handled by refine_stack's distance interval,
/// not here. `reg_expr`/`materialize_reg` is idempotent (returns the
/// cached slot if already bound), matching `bcf_reg_expr`'s lazy reuse.
fn bcf_materialize_src(state: &mut State, reg: Reg) {
    if reg == Reg::R10 || state.bcf.is_none() {
        return;
    }
    if !matches!(state.types.get(reg), RegType::ScalarValue) {
        return;
    }
    // Kernel `!tnum_is_const(reg->var_off)` — a known constant is left
    // unmaterialized (handled as a literal at use).
    if state.domain.get_fixed_value(reg).is_some() || state.get_tnum(reg).is_const() {
        return;
    }
    let Some(idx) = reg.bcf_idx() else { return };
    let pc = state.pc;
    let bounds = crate::analysis::transfer::alu::helpers::bcf_reg_bounds(state, reg);
    if let Some(bcf) = state.bcf.as_mut() {
        bcf.set_current_pc(pc);
        bcf.reg_expr(idx, &bounds, false);
    }
}

/// Checks if a register is readable (has been initialized).
/// Returns true if readable, false if not (and records error).
pub(crate) fn check_reg_readable(env: &mut VerifierEnv, state: &mut State, reg: Reg) -> bool {
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
        _ => {
            // Faithful kernel `check_reg_arg` SRC_OP hook: bind the
            // reg's bcf_expr on first source-operand read.
            bcf_materialize_src(state, reg);
            true
        }
    }
}

/// Checks if an operand is readable.
/// For immediate operands, always returns true.
/// For register operands, checks if the register is initialized.
pub(crate) fn check_operand_readable(
    env: &mut VerifierEnv,
    state: &mut State,
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
