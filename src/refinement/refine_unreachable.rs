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
use crate::refinement::symbolic::{RegBounds, SymbolicState};
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
    try_prove_unreachable_inner(state, base_pc, prev_insn_pc, true, None)
}

/// Register-filtered discharge: like [`try_prove_unreachable`] but, after
/// the base_pc suffix filter, also restricts the path_conds to a small
/// register set computed via VAR→reg provenance def-use closure (mirrors
/// the kernel's `bcf_reg_expr` data-dependency selection). This produces
/// the kernel's multi-register reject conjunctions (e.g. hash B
/// `0x4eeecf4b98c670ca`) that the PC-suffix filter alone cannot isolate.
///
/// Returns `None` when no provenance seed exists (no reg-backed branch in
/// the suffix) — the caller falls back to the unfiltered discharges.
/// Emitted ADDITIVELY by the caller and deduped by `cond_hash`; never
/// replaces the unfiltered discharge (which keeps already-matched hashes
/// byte-stable). See [[feedback_byte_level_decode_first]] §2026-05-29.
/// `hops` controls the provenance def-use closure depth (1 → seed + its
/// direct value-deps; 2 → one more layer). PC-independent: selects over
/// the FULL trajectory, since the kernel's bcf_reg_expr materializes a
/// register's recorded condition regardless of how far back it was
/// emitted. Live default-on (see caller in branch/mod.rs); VM ground
/// truth shows it flips the to_hep_*_co-re_v6 family to full-load.
pub fn try_prove_unreachable_reg_filtered(
    state: &State,
    hops: usize,
) -> Option<UnreachableOk> {
    try_prove_unreachable_inner(state, None, None, true, Some(hops))
}

/// Register-filtered discharge with the per-reg fresh-VAR rewrite
/// disabled (mirror of [`try_prove_unreachable_no_rewrite`]).
pub fn try_prove_unreachable_reg_filtered_no_rewrite(
    state: &State,
    hops: usize,
) -> Option<UnreachableOk> {
    try_prove_unreachable_inner(state, None, None, false, Some(hops))
}

/// Like [`try_prove_unreachable`] but with the per-reg fresh-VAR rewrite
/// disabled. Used by the chain emission loop to ALSO push the
/// un-rewritten (aliased-VAR) form, so previously-matched hashes (that
/// the kernel may query via its `bcf_track` replay on this specific
/// reject site) stay in the bundle alongside the kernel-shape rewrites.
/// Without this, the rewrite is destructive for any program whose
/// previously-matched hash happens to be the aliased form.
pub fn try_prove_unreachable_no_rewrite(
    state: &State,
    base_pc: Option<usize>,
    prev_insn_pc: Option<usize>,
) -> Option<UnreachableOk> {
    try_prove_unreachable_inner(state, base_pc, prev_insn_pc, false, None)
}

fn try_prove_unreachable_inner(
    state: &State,
    base_pc: Option<usize>,
    prev_insn_pc: Option<usize>,
    do_fresh_var_rewrite: bool,
    reg_filter_hops: Option<usize>,
) -> Option<UnreachableOk> {
    let bcf_ref = state.bcf.as_ref()?;
    let mut sym: SymbolicState = (**bcf_ref).clone();

    // Mirror bcf_track's suffix-only emission: drop path_conds emitted
    // strictly before the suffix base. `prev_insn_pc` enables the
    // kernel's `record_path_cond`-at-replay-start mechanism: if the
    // cached base state's immediate predecessor (vstate->last_insn_idx)
    // was a scalar conditional branch, that branch's cond + its var's
    // bound preds get retained even when their source_pc < base_pc.
    // Register-filtered vs PC-suffix-filtered selection are MUTUALLY
    // EXCLUSIVE axes. PC-suffix (`base_pc`) keeps conds by source PC,
    // mirroring the kernel's bcf_track suffix replay. Register-filtering
    // (`reg_filter_hops`) keeps conds by register over the FULL trajectory,
    // mirroring the kernel's bcf_reg_expr data-dependency closure — it must
    // see conditions arbitrarily far back (e.g. proto2 ~500 PCs before the
    // reject), so it deliberately skips the PC filter.
    match reg_filter_hops {
        None => {
            if let Some(bp) = base_pc {
                sym.filter_path_conds_from_pc(bp, prev_insn_pc);
            }
        }
        Some(hops) => {
            // Provenance-seeded goal set over the full trajectory: seed =
            // most-recent branch's lhs reg, then `hops` def-use layers via
            // VAR→reg provenance. None ⇒ no reg-backed branch ⇒ skip (the
            // caller's unfiltered discharges already cover this anchor).
            match sym.provenance_goal_set(hops) {
                Some(goal) => {
                    if std::env::var("ZOVIA_DUMP_DISCHARGE").ok().as_deref() == Some("1") {
                        let pre = sym.path_conds.len();
                        sym.filter_path_conds_by_regs(&goal);
                        let mut g: Vec<usize> = goal.into_iter().collect();
                        g.sort_unstable();
                        eprintln!(
                            "[disc-regsel] hops={} goal={:?} path_conds {}→{}",
                            hops, g, pre, sym.path_conds.len()
                        );
                    } else {
                        sym.filter_path_conds_by_regs(&goal);
                    }
                }
                None => return None,
            }
        }
    }

    // Kernel-mirror K==K rewrite: for each branch path_cond that narrowed
    // its LHS to a const K on the taken side, substitute the predicate
    // expression with a fresh `K op K` literal. Mirrors kernel
    // `bcf_track`'s fresh-replay where `bcf_reg_expr` re-materializes
    // the dst via `tnum_is_const → bcf_val(K)` because the replay starts
    // with `bcf_expr = -1`. Ground-truth probe 2026-05-23 confirms PC 1215
    // emits `17 == 17` via this path (calico from_wep_fib_dsr_debug).
    //
    // Done as a graph rewrite (add fresh exprs, swap path_cond slot)
    // rather than a full per-replay rebuild so existing cvc5 contradictions
    // via spill/fill-propagated vars stay intact. The fallback below
    // catches cases where K==K substitution removes a load-bearing
    // constraint — falls back to the un-rewritten form and re-runs cvc5,
    // preserving discharge soundness at the cost of byte-match for that
    // specific entry.
    debug_assert_eq!(sym.path_conds.len(), sym.path_cond_narrowed_const.len());
    let original_path_conds = sym.path_conds.clone();
    let mut orphaned_vars: std::collections::HashSet<u32> = std::collections::HashSet::new();
    for i in 0..sym.path_conds.len() {
        if let Some((k, op_byte, jmp32, lhs_pc)) = sym.path_cond_narrowed_const[i] {
            // Rewrite gate: in a fresh kernel `bcf_track` replay starting
            // at base_pc, the LHS reg's bcf_expr is uncached iff it had
            // never been materialized OR its previous materialization was
            // before base_pc (invisible in the fresh expr table). Skip
            // rewrite if LHS was cached at or after base_pc — kernel
            // would have returned the cached var and emitted `VAR op K`,
            // preserving the binding constraint needed for cvc5 to prove
            // the overall formula unsat (e.g. wepfd PC 1474 R1==6 cached
            // via spill/fill propagation from R7's PC 1467 spill, pairs
            // with R7!=6 at PC 1468 for the contradiction). Conservatively
            // rewrite when base_pc is unknown (mirrors kernel's
            // `base_pc=NULL` keep-all behavior).
            let lhs_uncached_in_fresh_replay = match (lhs_pc, base_pc) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(p), Some(bp)) => p < bp,
            };
            if !lhs_uncached_in_fresh_replay {
                continue;
            }
            // Collect the OLD pred's VAR references before overwriting —
            // these vars are now orphaned in this discharge's canonical
            // encoding (kernel's fresh replay emits `bcf_val(K)` directly
            // and never materializes the VAR, so its bound preds don't
            // exist in kernel's bcf graph). Below we drop matching bound
            // preds from the filtered path_conds for byte-faithful hash.
            let old_pred = sym.path_conds[i];
            for v in sym.collect_vars(old_pred) {
                orphaned_vars.insert(v);
            }
            let lhs = sym.add_val(k, jmp32);
            let rhs = sym.add_val(k, jmp32);
            let new_pred = sym.add_pred(op_byte, lhs, rhs);
            sym.path_conds[i] = new_pred;
        }
    }
    // Drop bound-pred path_conds whose only VAR references are now
    // orphaned by the K==K rewrites above. Mirrors kernel's
    // fresh-replay behavior: when `bcf_reg_expr` takes the
    // `tnum_is_const → bcf_val(K)` path (no `bcf_bound_reg32` call),
    // no bound preds exist for that VAR in the kernel's bcf graph.
    // Zovia inherits the bound preds from its full-trace bcf state
    // (kept by `filter_path_conds_from_pc`'s subset rule for vars(L)),
    // but after we rewrite L to `K op K`, those bound preds become
    // canonical-hash garbage (extra conjuncts kernel doesn't have).
    // Drop only true bound preds (is_branch=false) — branches always
    // stay regardless of var orphanage.
    if !orphaned_vars.is_empty() {
        let mut kept_conds = Vec::with_capacity(sym.path_conds.len());
        let mut kept_pcs = Vec::with_capacity(sym.path_cond_pcs.len());
        let mut kept_is_branch = Vec::with_capacity(sym.path_cond_is_branch.len());
        let mut kept_narrowed = Vec::with_capacity(sym.path_cond_narrowed_const.len());
        let mut kept_lhs_meta = Vec::with_capacity(sym.path_cond_lhs_meta.len());
        for i in 0..sym.path_conds.len() {
            let drop = !sym.path_cond_is_branch[i] && {
                let vars = sym.collect_vars(sym.path_conds[i]);
                !vars.is_empty() && vars.is_subset(&orphaned_vars)
            };
            if !drop {
                kept_conds.push(sym.path_conds[i]);
                kept_pcs.push(sym.path_cond_pcs[i]);
                kept_is_branch.push(sym.path_cond_is_branch[i]);
                kept_narrowed.push(sym.path_cond_narrowed_const[i]);
                kept_lhs_meta.push(sym.path_cond_lhs_meta[i]);
            }
        }
        sym.path_conds = kept_conds;
        sym.path_cond_pcs = kept_pcs;
        sym.path_cond_is_branch = kept_is_branch;
        sym.path_cond_narrowed_const = kept_narrowed;
        sym.path_cond_lhs_meta = kept_lhs_meta;
    }

    if do_fresh_var_rewrite {
    // Per-reg fresh-VAR rewrite (2026-05-27): mirror kernel's bcf_track
    // fresh-replay where bcf_reg_expr(R) materializes a fresh VAR (plus
    // bound preds) for each reg whose bcf_pre=-1. Generalizes the K==K
    // rewrite above to non-narrowing branches. Inserts bound preds for
    // the fresh VAR immediately BEFORE the branch they materialize for —
    // matches kernel order, since bcf_canonical_hash is position-
    // sensitive within CONJ. Calico from_l3_debug_co-re pc=1276:
    // kernel 5-conj 0x5edc has interleaved order [bound_V0, V0!=6,
    // bound_V1, V1!=6, V1==6].
    //
    // ADDITIVE in safety: produces additional canonical-hash bytes
    // for non-narrowing branches; rewritten goals are equi-unsat with
    // the originals (fresh VARs are unconstrained symbolic substitutes
    // for the bounds-narrowed cached exprs). Solver-fallback path
    // below catches any cases where the rewrite weakens unsat.
    {
        use std::collections::HashMap;
        let mut fresh_var_for_reg: HashMap<usize, u32> = HashMap::new();
        let mut newly_orphaned: std::collections::HashSet<u32> = std::collections::HashSet::new();
        // New path_conds list, built in original index order with
        // bound preds inserted at materialization sites.
        let mut new_conds: Vec<u32> = Vec::with_capacity(sym.path_conds.len() + 8);
        let mut new_pcs: Vec<usize> = Vec::with_capacity(sym.path_cond_pcs.len() + 8);
        let mut new_is_branch: Vec<bool> = Vec::with_capacity(sym.path_cond_is_branch.len() + 8);
        let mut new_narrowed: Vec<Option<(u64, u8, bool, Option<usize>)>> = Vec::with_capacity(sym.path_cond_narrowed_const.len() + 8);
        let mut new_lhs_meta: Vec<Option<(usize, Option<usize>, bool, RegBounds)>> = Vec::with_capacity(sym.path_cond_lhs_meta.len() + 8);
        let path_conds_snapshot = sym.path_conds.clone();
        let pcs_snapshot = sym.path_cond_pcs.clone();
        let is_branch_snapshot = sym.path_cond_is_branch.clone();
        let narrowed_snapshot = sym.path_cond_narrowed_const.clone();
        let lhs_meta_snapshot = sym.path_cond_lhs_meta.clone();
        for i in 0..path_conds_snapshot.len() {
            let pred_slot = path_conds_snapshot[i];
            let pc = pcs_snapshot[i];
            let is_branch = is_branch_snapshot[i];
            let narrowed = narrowed_snapshot[i];
            let lhs_meta = lhs_meta_snapshot[i];
            // Decide whether to rewrite this entry.
            let do_rewrite = is_branch
                && narrowed.map(|n| {
                    // K==K already handled (skip if it would have fired)
                    !match (n.3, base_pc) {
                        (None, _) => true,
                        (Some(_), None) => false,
                        (Some(p), Some(bp)) => p < bp,
                    }
                }).unwrap_or(true)
                && lhs_meta.is_some();
            if do_rewrite {
                let (lhs_reg, lhs_pc, jmp32, lhs_bounds) = lhs_meta.unwrap();
                let lhs_uncached_in_fresh_replay = match (lhs_pc, base_pc) {
                    (None, _) => true,
                    (Some(_), None) => false,
                    (Some(p), Some(bp)) => p < bp,
                };
                if lhs_uncached_in_fresh_replay {
                    let (op_with_class, arg0, arg1) = {
                        let Some(e) = sym.expr_at(pred_slot) else {
                            new_conds.push(pred_slot);
                            new_pcs.push(pc);
                            new_is_branch.push(is_branch);
                            new_narrowed.push(narrowed);
                            new_lhs_meta.push(lhs_meta);
                            continue;
                        };
                        if e.args.len() != 2 {
                            new_conds.push(pred_slot);
                            new_pcs.push(pc);
                            new_is_branch.push(is_branch);
                            new_narrowed.push(narrowed);
                            new_lhs_meta.push(lhs_meta);
                            continue;
                        }
                        (e.code, e.args[0], e.args[1])
                    };
                    for v in sym.collect_vars(arg0) {
                        newly_orphaned.insert(v);
                    }
                    // First time seeing this reg → allocate fresh VAR
                    // AND emit its bound preds (mirroring kernel's
                    // bcf_reg_expr → bcf_bound_reg sequence).
                    let (fresh, emit_bounds) = match fresh_var_for_reg.get(&lhs_reg) {
                        Some(&v) => (v, false),
                        None => {
                            let v = sym.add_var_bits(jmp32);
                            fresh_var_for_reg.insert(lhs_reg, v);
                            (v, true)
                        }
                    };
                    if emit_bounds {
                        // Use bound_reg_kernel_shape: routes to the
                        // 32-bit or 64-bit emitter and returns the
                        // emitted pred slots so we can splice them
                        // into the new path_conds list at the right
                        // position (BEFORE the branch).
                        let bound_pred_slots = sym.bound_reg_emit_preds(fresh, &lhs_bounds, jmp32);
                        for bp_slot in bound_pred_slots {
                            new_conds.push(bp_slot);
                            new_pcs.push(pc);
                            new_is_branch.push(false);
                            new_narrowed.push(None);
                            new_lhs_meta.push(None);
                        }
                    }
                    let op = op_with_class & crate::refinement::bcf::BCF_OP_MASK;
                    let new_pred = sym.add_pred(op, fresh, arg1);
                    new_conds.push(new_pred);
                    new_pcs.push(pc);
                    new_is_branch.push(true);
                    new_narrowed.push(narrowed);
                    new_lhs_meta.push(lhs_meta);
                    continue;
                }
            }
            // Default: pass through unmodified.
            new_conds.push(pred_slot);
            new_pcs.push(pc);
            new_is_branch.push(is_branch);
            new_narrowed.push(narrowed);
            new_lhs_meta.push(lhs_meta);
        }
        sym.path_conds = new_conds;
        sym.path_cond_pcs = new_pcs;
        sym.path_cond_is_branch = new_is_branch;
        sym.path_cond_narrowed_const = new_narrowed;
        sym.path_cond_lhs_meta = new_lhs_meta;
        // Drop bound preds whose only-referenced VARs are now orphaned.
        if !newly_orphaned.is_empty() {
            let mut kept_conds = Vec::with_capacity(sym.path_conds.len());
            let mut kept_pcs = Vec::with_capacity(sym.path_cond_pcs.len());
            let mut kept_is_branch = Vec::with_capacity(sym.path_cond_is_branch.len());
            let mut kept_narrowed = Vec::with_capacity(sym.path_cond_narrowed_const.len());
            let mut kept_lhs_meta = Vec::with_capacity(sym.path_cond_lhs_meta.len());
            for i in 0..sym.path_conds.len() {
                let drop = !sym.path_cond_is_branch[i] && {
                    let vars = sym.collect_vars(sym.path_conds[i]);
                    !vars.is_empty() && vars.is_subset(&newly_orphaned)
                };
                if !drop {
                    kept_conds.push(sym.path_conds[i]);
                    kept_pcs.push(sym.path_cond_pcs[i]);
                    kept_is_branch.push(sym.path_cond_is_branch[i]);
                    kept_narrowed.push(sym.path_cond_narrowed_const[i]);
                    kept_lhs_meta.push(sym.path_cond_lhs_meta[i]);
                }
            }
            sym.path_conds = kept_conds;
            sym.path_cond_pcs = kept_pcs;
            sym.path_cond_is_branch = kept_is_branch;
            sym.path_cond_narrowed_const = kept_narrowed;
            sym.path_cond_lhs_meta = kept_lhs_meta;
        }
    }
    } // end do_fresh_var_rewrite

    if std::env::var("ZOVIA_BCF_DUMP_PATH_COND_PCS").is_ok() {
        // Build slot→record-index map (path_conds/args hold SLOTS, exprs is
        // record-indexed; slot advances by slot_len() per record).
        let mut slot_to_idx: std::collections::HashMap<u32, usize> =
            std::collections::HashMap::new();
        {
            let mut s: u32 = 0;
            for (i, e) in sym.exprs.iter().enumerate() {
                slot_to_idx.insert(s, i);
                s += e.slot_len();
            }
        }
        let get = |slot: u32| sym.exprs.get(*slot_to_idx.get(&slot).unwrap_or(&usize::MAX));
        // Decode each path_cond predicate to (reg, op, const) + source_pc.
        let resolve = |mut slot: u32| -> String {
            for _ in 0..12 {
                let Some(e) = get(slot) else { return format!("e{slot}") };
                let base = e.code & 0xf8;
                if base == 0x18 {
                    return match sym.var_origin.get(&slot) {
                        Some(r) => format!("r{r}"),
                        None => format!("V{slot}"),
                    };
                } else if base == 0x08 {
                    return format!("0x{:x}", e.args.first().copied().unwrap_or(0));
                } else if !e.args.is_empty() {
                    slot = e.args[0];
                } else {
                    return format!("e{slot}");
                }
            }
            format!("e{slot}")
        };
        eprintln!(
            "[bcf] PATHCOND-DUMP base_pc={:?} n={}",
            base_pc,
            sym.path_conds.len()
        );
        for (i, (&cond, &pc)) in sym.path_conds.iter().zip(sym.path_cond_pcs.iter()).enumerate() {
            let isb = sym.path_cond_is_branch.get(i).copied().unwrap_or(false);
            let (lhs, op, rhs) = match get(cond) {
                Some(e) if e.args.len() >= 2 => {
                    (resolve(e.args[0]), e.code, resolve(e.args[1]))
                }
                Some(e) => ("?".into(), e.code, "?".into()),
                None => ("?".into(), 0, "?".into()),
            };
            eprintln!("  [{i:>2}] pc={pc:<5} {lhs} op=0x{op:02x} {rhs}  br={isb}");
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
            // Kernel-mirror rewrite (K==K) above may have removed a
            // constraint that was load-bearing for unsat. Fallback: undo
            // the rewrite and retry with the original VAR-form path_conds.
            // Loses byte-match with kernel for this entry but preserves
            // discharge for cases where the K==K rewrite weakens the
            // formula (e.g. when other conjuncts don't independently pin
            // the LHS via spill/fill propagation).
            if sym.path_conds != original_path_conds {
                sym.path_conds = original_path_conds;
                let fallback_goal = match sym.path_conds.len() {
                    0 => return None,
                    1 => sym.path_conds[0],
                    _ => {
                        let pcs = sym.path_conds.clone();
                        sym.add_conj(pcs)
                    }
                };
                let smt2 = match smtlib::encode(&sym) {
                    Ok(s) => s,
                    Err(_) => return None,
                };
                if let Ok(bytes) = solver::solve(&smt2) {
                    debug!("[bcf] path-unreachable: cvc5 accepted fallback ({} bytes)", bytes.len());
                    return Some(UnreachableOk {
                        proof_bytes: bytes,
                        goal_root: fallback_goal,
                        sym,
                    });
                }
            }
            None
        }
    }
}
