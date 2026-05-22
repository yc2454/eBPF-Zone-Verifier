//! Path-unreachable speculation site.
//!
//! Mirrors BCF's `bcf_prove_unreachable` (cheat-sheet §4d). Called from
//! [`crate::analysis::transfer`] at points where zovia accepts natively
//! but the kernel verifier would reject and emit a path-unreachable
//! BCF request — currently only the Mov-from-NotInit case for
//! `unreachable_arsh` (paper §unreachable-arsh).
//!
//! The goal expression is `CONJ(path_conds...)` — no positive-bounds
//! `refine_cond`. cvc5 must prove the conjunction unsatisfiable; on
//! success, the bundle entry is kind=`BCF_BUNDLE_KIND_UNREACHABLE`
//! and the kernel matches it via `bcf_bundle_try_discharge`'s
//! path_cond fallback (commit 39f5104ed029).

use crate::analysis::machine::state::State;
use crate::refinement::smtlib;
use crate::refinement::solver;
use crate::refinement::symbolic::SymbolicState;
use log::{debug, warn};

/// Returned on success: the goal-root expr-id and the symbolic-state
/// snapshot whose `exprs` table the goal lives in, plus the proof bytes.
pub struct UnreachableOk {
    pub proof_bytes: Vec<u8>,
    pub goal_root: u32,
    pub sym: SymbolicState,
}

/// Attempt to speculatively discharge a kernel-rejection site by proving
/// that `path_cond` is unsatisfiable. The bundle entry's `cond_hash`
/// equals the canonical hash of the goal expression; the kernel
/// `bcf_bundle_try_discharge` path-cond fallback computes the same hash
/// when it reaches the corresponding `bcf_prove_unreachable` site.
///
/// Returns `Some(UnreachableOk)` if cvc5 returned `unsat`; `None` otherwise.
/// `base_pc` is the suffix base PC (analogous to `try_refine_*`); pass
/// `None` to keep all accumulated path_conds.
pub fn try_prove_unreachable(
    state: &State,
    base_pc: Option<usize>,
    prev_insn_pc: Option<usize>,
) -> Option<UnreachableOk> {
    let bcf_ref = state.bcf.as_ref()?;
    let mut sym: SymbolicState = (**bcf_ref).clone();

    // Mirror bcf_track's suffix-only emission: drop path_conds emitted
    // strictly before the suffix base. `prev_insn_pc` enables the
    // kernel's `record_path_cond`-at-replay-start mechanism: if the
    // cached base state's immediate predecessor (vstate->last_insn_idx)
    // was a scalar conditional branch, that branch's cond + its var's
    // bound preds get retained even when their source_pc < base_pc.
    if let Some(bp) = base_pc {
        sym.filter_path_conds_from_pc(bp, prev_insn_pc);
    }

    if std::env::var("ZOVIA_BCF_DUMP_PATH_COND_PCS").is_ok() {
        eprintln!(
            "[bcf] path-unreachable: {} path_conds (base_pc={:?})",
            sym.path_conds.len(),
            base_pc
        );
        for (i, (&cond, &pc)) in sym.path_conds.iter().zip(sym.path_cond_pcs.iter()).enumerate() {
            eprintln!("  [{i}] expr_slot={cond} source_pc={pc}");
        }
    }

    if sym.path_conds.is_empty() {
        debug!("[bcf] path-unreachable: no path_conds accumulated, nothing to prove");
        return None;
    }

    // Build the goal root: for path-unreachable the goal is the path_cond
    // CONJ itself (no extra refine_cond). Mirrors kernel `bcf_track`'s
    // construction at verifier.c:24380-24384 (the same path_cond expr the
    // kernel passes to bcf_bundle_try_discharge via the -1 fallback).
    let goal_root = match sym.path_conds.len() {
        0 => return None,
        1 => sym.path_conds[0],
        _ => {
            let pcs = sym.path_conds.clone();
            sym.add_conj(pcs)
        }
    };

    // Don't set sym.refine_cond — leaving it None makes smtlib::encode
    // emit `(assert <path_conds>)` directly (no nested CONJ with a
    // refine_cond), which is what we want for the path-unreachable proof.

    let smt = match smtlib::encode(&sym) {
        Ok(s) => s,
        Err(e) => {
            warn!("[bcf] path-unreachable: SMT-LIB encode failed: {}", e);
            return None;
        }
    };
    if std::env::var("ZOVIA_BCF_DUMP_SMT").is_ok() {
        eprintln!("---- [bcf] SMT-LIB to cvc5 (path-unreachable) ----\n{}\n---- end ----", smt);
    }

    match solver::solve(&smt) {
        Ok(bytes) => {
            debug!("[bcf] path-unreachable: cvc5 accepted ({} bytes)", bytes.len());
            Some(UnreachableOk { proof_bytes: bytes, goal_root, sym })
        }
        Err(e) => {
            debug!("[bcf] path-unreachable: cvc5 declined ({})", e);
            None
        }
    }
}
