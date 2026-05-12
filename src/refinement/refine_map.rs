//! Refinement callback for the map-region OOB rejection sites.
//!
//! Mirrors BCF's `bcf_refine_access_bound` (kernel `set1/0014`, cheat-sheet
//! §4b). Three sub-cases dispatched on which operand is variable; the size
//! register comes in via `env.bcf_size_reg` (BCF stashes `bcf->size_regno`
//! in the analogous transient slot in their kernel state).
//!
//! Sub-cases:
//!
//! * **(iii) `size_const` (variable ptr, constant size)** — most common in
//!   our corpus. Refine the pointer's offset: claim `off > limit - size`
//!   (high-side OOB) is unsat, optionally disjoined with `off < 0`
//!   (low-side OOB) when the verifier's interval suggests the low side is
//!   reachable.
//!
//! * **(iv) both variable** — both pointer offset and size are
//!   symbolically tracked. Claim `off + size > limit` ∨ `off < 0` unsat.
//!   This is what unlocks programs like `test_get_stack_rawtp` where
//!   `size = max_len - usize` is a derived expression. We don't replicate
//!   BCF's `bcf->access_checked` two-stage defer — our verifier already
//!   has the full picture at the rejection site.
//!
//! * **(ii) `ptr_const` (constant ptr, variable size)** — refine the size
//!   reg's upper bound: claim `size > limit - off` unsat. Less common
//!   shape; included for completeness.
//!
//! The pointer's symbolic offset comes from `state.bcf.get_reg(base)` (β+
//! tracking, anchor at 0 from `maybe_promote_map_val`). The size's
//! symbolic expression comes from `state.bcf.get_reg(size_reg)` when one
//! is provided; otherwise the static `size: i64` is used as a 64-bit BV
//! constant.

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::refinement::bcf::{BPF_ADD, BPF_JSGT, BPF_JSLT};
use crate::refinement::smtlib;
use crate::refinement::solver;
use crate::refinement::symbolic::SymbolicState;
use log::{debug, warn};

/// Attempt to discharge a map-region OOB rejection via cvc5.
///
/// `base` — the pointer reg whose offset is being checked.
/// `insn_off` — the load/store instruction's static offset.
/// `size` — the access size in bytes (the verifier's static upper bound,
/// already collapsed to a concrete `i64`). Used as the literal access
/// size when `size_reg` is `None`; ignored when `size_reg` is `Some` and
/// has a symbolic expression.
/// `map_limit` — the map value's total size.
/// `size_reg` — the helper-arg size register, when this access came via a
/// helper-mem-region check. The refinement reads its symbolic expression
/// (case iv) or detects a const size from interval+tnum (case iii).
pub fn try_refine_map_access(
    state: &State,
    base: Reg,
    insn_off: i64,
    size: i64,
    map_limit: i64,
    size_reg: Option<Reg>,
) -> Option<super::refine_stack::RefineOk> {
    let bcf_ref = state.bcf.as_ref()?;
    let mut sym: SymbolicState = (**bcf_ref).clone();

    // Pointer offset expression. Bail if missing (e.g., the base reg
    // wasn't anchored — possibly arrived via stack spill/reload).
    let b_idx = base.bcf_idx()?;
    let Some(off_expr) = sym.get_reg(b_idx) else {
        debug!(
            "[bcf] map-refine skipped: base {:?} has no symbolic expr (anchor missing?)",
            base
        );
        return None;
    };

    // Compose `access_off = off + insn_off` as a 64-bit BV expression.
    let access_off_expr = if insn_off == 0 {
        off_expr
    } else {
        let k = sym.add_val64(insn_off as u64);
        sym.add_alu(BPF_ADD, off_expr, k, 64)
    };

    // Decide which size expression to use. If `size_reg` is provided AND
    // it has a symbolic expression, prefer that (case iv). Otherwise use
    // the static `size` (case iii). When we use the symbolic size, we
    // don't have a separate const fallback — but we record the verifier's
    // umax bound as an optional path-cond to keep the formula tight.
    let (size_expr, size_is_symbolic) = if let Some(sz_reg) = size_reg {
        sz_reg
            .bcf_idx()
            .and_then(|si| sym.get_reg(si))
            .map(|e| (e, true))
            .unwrap_or_else(|| (sym.add_val64(size as u64), false))
    } else {
        (sym.add_val64(size as u64), false)
    };

    // High-side: access_off + size_expr > map_limit
    let access_end_expr = sym.add_alu(BPF_ADD, access_off_expr, size_expr, 64);
    let limit_idx = sym.add_val64(map_limit as u64);
    let high_pred = sym.add_pred(BPF_JSGT, access_end_expr, limit_idx);

    // Low-side: access_off < 0
    let zero_idx = sym.add_val64(0);
    let low_pred = sym.add_pred(BPF_JSLT, access_off_expr, zero_idx);

    // Always emit the disjunction. cvc5 prunes trivially-unreachable
    // sides cheaply and the unconditional shape keeps the encoder simple.
    let oob = sym.add_disj(vec![high_pred, low_pred]);
    sym.set_refine_cond(oob);

    // When using a symbolic size, also pin the verifier's interval-known
    // upper bound on the size as a path-cond — this lets cvc5 use what
    // the abstract domain already proved (e.g., from earlier `if size <
    // X` branches) without re-deriving it. BCF's analog: `bcf_bound_reg`
    // seeds interval-known bounds when transitioning into tracking mode.
    if size_is_symbolic {
        if let Some(sz_reg) = size_reg {
            let (smin, smax) = state.domain.get_interval(sz_reg);
            if smin >= 0 {
                // size ≥ smin (unsigned-safe when smin ≥ 0)
                let lo_const = sym.add_val64(smin as u64);
                let p = sym.add_pred(crate::refinement::bcf::BPF_JSGE, size_expr, lo_const);
                sym.add_cond(p);
            }
            if smax != i64::MAX {
                let hi_const = sym.add_val64(smax as u64);
                let p = sym.add_pred(crate::refinement::bcf::BPF_JSLE, size_expr, hi_const);
                sym.add_cond(p);
            }
        }
    }

    let smt = match smtlib::encode(&sym) {
        Ok(s) => s,
        Err(e) => {
            warn!("[bcf] map SMT-LIB encode failed: {}", e);
            return None;
        }
    };
    if std::env::var("ZOVIA_BCF_DUMP_SMT").is_ok() {
        eprintln!("---- [bcf] SMT-LIB to cvc5 (map) ----\n{}\n---- end ----", smt);
    }
    match solver::solve(&smt) {
        Ok(bytes) => {
            debug!(
                "[bcf] map-OOB refinement: cvc5 accepted ({} bytes)",
                bytes.len()
            );
            Some(super::refine_stack::RefineOk { proof_bytes: bytes, goal_root: oob, sym })
        }
        Err(e) => {
            debug!("[bcf] map-OOB refinement: cvc5 declined ({})", e);
            None
        }
    }
}
