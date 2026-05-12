//! Refinement callback for the stack-OOB rejection site.
//!
//! Mirrors BCF's `bcf_refine_stack_access` (cheat-sheet §4a). Called from
//! [`crate::analysis::transfer::memory::stack`] at the two `StackOutOfBounds`
//! rejection paths (known-offset and unknown-offset). On Unsat from cvc5,
//! returns the BCF proof bytes — the caller suppresses the rejection.
//!
//! Two strategies, tried in order:
//!
//! 1. **Direct symbolic offset** (β+, 2026-05-12). When the base pointer
//!    itself has a symbolic expression (built by the unified ptr/scalar
//!    hooks in `handle_add`/`handle_sub`/`handle_mov` with R10 anchored at
//!    const(0)), the offset-from-r10 is already in the DAG — read it
//!    straight out. Handles multi-contributor cases (e.g.
//!    `r1 += r0; r1 += r2`) that the older single-contributor path can't.
//! 2. **Single-contributor reconstruction** (Phase 1 fallback). When the
//!    direct expression isn't available, reconstruct `off = K + contrib`
//!    where K is the constant displacement (`distance.lo - contributor.lo`)
//!    and `contrib` is the scalar from `state.var_off_contributor`. Bails
//!    if K is non-constant (multi-contributor) or intervals are unbounded.

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
/// Returned on success: the goal-root expr-id and the symbolic-state
/// snapshot whose `exprs` table the goal lives in, plus the proof bytes.
pub struct RefineOk {
    pub proof_bytes: Vec<u8>,
    pub goal_root: u32,
    pub sym: SymbolicState,
}

pub fn try_refine_stack_oob(
    state: &State,
    base: Reg,
    instruction_offset: i64,
    size: i64,
) -> Option<RefineOk> {
    let bcf_ref = state.bcf.as_ref()?;
    let mut sym: SymbolicState = (**bcf_ref).clone();

    // Strategy 1: base has a direct symbolic offset from r10.
    let direct_off = base
        .bcf_idx()
        .and_then(|b_idx| sym.get_reg(b_idx));

    let off_expr = if let Some(b_expr) = direct_off {
        if instruction_offset == 0 {
            b_expr
        } else {
            let k_idx = sym.add_val64(instruction_offset as u64);
            sym.add_alu(BPF_ADD, b_expr, k_idx, 64)
        }
    } else {
        // Strategy 2: reconstruct from the recorded scalar contributor.
        let Some(contributor) = state.var_off_contributor.get(&base).copied() else {
            debug!(
                "[bcf] stack-refine skipped: no direct expr and no var_off_contributor for {:?}",
                base
            );
            return None;
        };
        let Some(c_idx) = contributor.bcf_idx() else {
            debug!("[bcf] stack-refine skipped: contributor {:?} has no bcf idx", contributor);
            return None;
        };
        let Some(contrib_expr) = sym.get_reg(c_idx) else {
            debug!(
                "[bcf] stack-refine skipped: contributor {:?} has no symbolic expr",
                contributor
            );
            return None;
        };
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
        let k_idx = sym.add_val64(k as u64);
        sym.add_alu(BPF_ADD, k_idx, contrib_expr, 64)
    };

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
            Some(RefineOk { proof_bytes: bytes, goal_root: oob, sym })
        }
        Err(e) => {
            debug!("[bcf] stack-OOB refinement: cvc5 declined ({})", e);
            None
        }
    }
}
