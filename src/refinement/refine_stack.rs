//! Refinement callback for the stack-OOB rejection site.
//!
//! Mirrors BCF's `bcf_refine_stack_access` (cheat-sheet §4a). Called from
//! [`crate::analysis::transfer::memory::stack`] at the two `StackOutOfBounds`
//! rejection paths (known-offset and unknown-offset). On Unsat from cvc5,
//! returns the BCF proof bytes — the caller suppresses the rejection.
//!
//! Phase 1 scope: handles the case where the offending pointer reg has a
//! single scalar contributor (`State::var_off_contributor`), and the
//! pointer's constant displacement from r10 is recoverable as
//! `distance_lo - contributor.lo`. This is enough for `shift_constraint`;
//! the four-case template (cheat-sheet §4b) and helper-mem-size case
//! are Phase 2.

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::common::constants;
use crate::refinement::bcf::{BPF_ADD, BPF_JSGT};
use crate::refinement::smtlib;
use crate::refinement::solver;
use crate::refinement::symbolic::SymbolicState;
use log::{debug, warn};

/// Attempt to discharge a stack-OOB rejection via cvc5. Returns the BCF
/// proof bytes on success; `None` if no refinement could be built (no bcf
/// state, no contributor, missing symbolic info) or cvc5 didn't return
/// `unsat`.
pub fn try_refine_stack_oob(
    state: &State,
    base: Reg,
    instruction_offset: i64,
    size: i64,
) -> Option<Vec<u8>> {
    let bcf_ref = state.bcf.as_ref()?;
    let mut sym: SymbolicState = (**bcf_ref).clone();

    // 1. Find the scalar contributor whose symbolic expr we'll use as the
    //    variable part of the offset. Without one, we have nothing
    //    symbolic to feed cvc5 — give up.
    let contributor = *state.var_off_contributor.get(&base)?;
    let c_idx = contributor.bcf_idx()?;
    let contrib_expr = sym.get_reg(c_idx)?;

    // 2. Recover the constant displacement K of `base` from `r10`.
    //    For `r2 = r10 + K + contributor`, distance(r2, r10) ranges over
    //    [K + contributor.lo, K + contributor.hi]; the contributor's own
    //    interval lets us subtract back out to K.
    let (d_lo, d_hi) = state.domain.get_distance_interval(base, Reg::R10);
    let (c_lo, c_hi) = state.domain.get_interval(contributor);
    if d_lo == i64::MIN || d_hi == i64::MAX || c_lo == i64::MIN || c_hi == i64::MAX {
        debug!(
            "[bcf] stack-refine skipped: unbounded interval (d=[{},{}], c=[{},{}])",
            d_lo, d_hi, c_lo, c_hi
        );
        return None;
    }
    let k_lo = d_lo.saturating_sub(c_lo);
    let k_hi = d_hi.saturating_sub(c_hi);
    if k_lo != k_hi {
        debug!(
            "[bcf] stack-refine skipped: K not constant (k_lo={}, k_hi={})",
            k_lo, k_hi
        );
        return None;
    }
    let k = k_lo + instruction_offset;

    // 3. Build off_expr = K + contrib_expr (as 64-bit BV).
    let k_idx = sym.add_val64(k as u64);
    let off_expr = sym.add_alu(BPF_ADD, k_idx, contrib_expr, 64);

    // 4. Build refine_cond per template 4a: the access is in [STACK_MIN, -size],
    //    so OOB is `off > -size` (treated as signed since stack offsets are
    //    negative). We claim this is unsat under path_conds.
    let upper = constants::BPF_STACK_MAX - size; // safe high-bound: -size for stack-r10
    let upper_idx = sym.add_val64(upper as i64 as u64);
    let oob = sym.add_pred(BPF_JSGT, off_expr, upper_idx);
    sym.set_refine_cond(oob);

    // 5. Encode to SMT-LIB + call cvc5.
    let smt = match smtlib::encode(&sym) {
        Ok(s) => s,
        Err(e) => {
            warn!("[bcf] SMT-LIB encode failed: {}", e);
            return None;
        }
    };
    if std::env::var("ZOVIA_BCF_DUMP_SMT").is_ok() {
        eprintln!("---- [bcf] SMT-LIB to cvc5 ----\n{}\n---- end ----", smt);
    }
    match solver::solve(&smt) {
        Ok(bytes) => {
            debug!("[bcf] stack-OOB refinement: cvc5 accepted ({} bytes)", bytes.len());
            Some(bytes)
        }
        Err(e) => {
            debug!("[bcf] stack-OOB refinement: cvc5 declined ({})", e);
            None
        }
    }
}
