//! Refinement callback for the map-region OOB rejection sites.
//!
//! Mirrors BCF's `bcf_refine_access_bound` (cheat-sheet §4b). Phase 2
//! α scope: sub-case (iii) only — variable pointer offset, constant
//! size (the only sub-case that actually fires in our verifier, since
//! the helper-arg layer concretizes size to its `umax` before the
//! access check runs). Sub-cases (ii) and (iv) need upstream changes
//! to preserve the size register through `mem_checks.rs` and are
//! deferred.
//!
//! The refinement reads the base pointer's symbolic offset from
//! `state.bcf.get_reg(base)` (β+ pointer-tracking, anchored at 0 by
//! the map-value promotion hook in `branch/refinement.rs`). The
//! refine_cond expresses the disjunction of the two OOB endpoints:
//!
//! ```text
//! refine_cond = (off + insn_off + size  >  map_limit)   // high-side
//!             ∨ (off + insn_off          <  0)          // low-side
//! ```
//!
//! Both predicates are signed BV comparisons. cvc5 handles the
//! trivially-unreachable side (e.g. low-side when `off ≥ 0` is
//! provable) without extra effort.

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
/// `size` — the access size in bytes (already an upper bound when the
/// helper-arg layer collapsed a variable size reg).
/// `map_limit` — the map value's total size.
pub fn try_refine_map_access(
    state: &State,
    base: Reg,
    insn_off: i64,
    size: i64,
    map_limit: i64,
) -> Option<Vec<u8>> {
    let bcf_ref = state.bcf.as_ref()?;
    let mut sym: SymbolicState = (**bcf_ref).clone();

    // The base must have a symbolic offset expression. Without it the
    // Phase 1 stack-style contributor reconstruction doesn't apply —
    // map-value pointers don't track distance to a fixed anchor like
    // R10. Bail; the existing rejection proceeds.
    let b_idx = base.bcf_idx()?;
    let Some(off_expr) = sym.get_reg(b_idx) else {
        debug!(
            "[bcf] map-refine skipped: base {:?} has no symbolic expr (anchor missing?)",
            base
        );
        return None;
    };

    // Compose `off + insn_off` as a 64-bit BV expression.
    let access_off_expr = if insn_off == 0 {
        off_expr
    } else {
        let k = sym.add_val64(insn_off as u64);
        sym.add_alu(BPF_ADD, off_expr, k, 64)
    };

    // High-side: (access_off + size) > map_limit  →  unsafe upper.
    let access_end_expr = if size == 0 {
        access_off_expr
    } else {
        let s = sym.add_val64(size as u64);
        sym.add_alu(BPF_ADD, access_off_expr, s, 64)
    };
    let limit_idx = sym.add_val64(map_limit as u64);
    let high_pred = sym.add_pred(BPF_JSGT, access_end_expr, limit_idx);

    // Low-side: access_off < 0  →  unsafe lower.
    let zero_idx = sym.add_val64(0);
    let low_pred = sym.add_pred(BPF_JSLT, access_off_expr, zero_idx);

    // refine_cond = high_pred ∨ low_pred. We always emit both, even
    // if one side is trivially unreachable — cvc5 prunes those without
    // significant cost, and the unconditional shape keeps the encoder
    // simple. If this measurably bloats proof sizes on the corpus,
    // narrow it via a domain query.
    let oob = sym.add_disj(vec![high_pred, low_pred]);
    sym.set_refine_cond(oob);

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
            Some(bytes)
        }
        Err(e) => {
            debug!("[bcf] map-OOB refinement: cvc5 declined ({})", e);
            None
        }
    }
}
