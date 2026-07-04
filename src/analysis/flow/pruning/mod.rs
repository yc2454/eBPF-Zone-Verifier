pub mod cache;
// src/analysis/flow/pruning/mod.rs
//
// Pruning orchestration: should_prune, handle_loop_pruning,
// handle_standard_pruning, and supporting bookkeeping.
// Loop detection + widening math live in widening.rs.
// Subsumption predicates live in subsumption.rs.

mod subsumption;
pub(crate) mod widening;

use std::collections::HashSet;

use crate::analysis::machine::env::{SubsumptionMissReason, VerifierEnv};
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{Instr, Program};
use crate::common::config::VerifierConfig;
use subsumption::{iter_active_depths_differ, state_exact_equal, state_subsumed_by};
use widening::{
    arrived_via_back_edge, is_at_loop_point, is_prune_point, loop_body_has_force_checkpoint,
    loop_has_conditional_exit, this_loop_iter_pre_widening,
};

/// Mirrors the kernel's "skip_inf_loop_check" paths in `is_state_visited`
/// (verifier.c v6.15 L19073 / L19111): the inf-loop trap doesn't fire at
/// iter_next kfunc call sites (those are handled by `process_iter_next_call`
/// + iter_active_depths_differ) or at sync-callback-call helper sites
/// (bpf_loop / bpf_for_each_map_elem / bpf_timer_set_callback — the
/// callback's own iteration accounting drives convergence). zovia flags
/// both classes via `force_checkpoint=true` set at the `Call` insn. We
/// gate on the insn kind plus the flag so MayGoto pcs (also
/// force-checkpoint) still run the inf-loop check, matching the kernel's
/// fall-through at L19103-L19109.
fn is_inf_loop_skip_pc(prog: &Program, pc: usize) -> bool {
    matches!(prog.instrs.get(pc), Some(Instr::Call { .. }))
}

/// DIAGNOSTIC (ZOVIA_ZHIT): print every prune HIT in insn window 380-910
/// with a global sequence number, for diffing against the kernel's
/// [ZK phit] sequence (same window, same fields).
fn zhit_seq(pc: usize, state: &State, prev: &State) {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    if !*ON.get_or_init(|| std::env::var("ZOVIA_ZHIT").is_ok()) {
        return;
    }

    static SEQ: AtomicU64 = AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, Ordering::Relaxed);
    use crate::analysis::machine::reg::Reg;
    let r2t = state.types.get(Reg::R2);
    let r2i = state.domain.get_interval(Reg::R2);
    let mut diffs = String::new();
    for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::R9] {
        let ci = state.domain.get_interval(r);
        let pi = prev.domain.get_interval(r);
        if ci != pi || state.types.get(r) != prev.types.get(r) {
            diffs.push_str(&format!(
                " {:?}:cur={:?}[{}..{}]vs prev={:?}[{}..{}]p={}",
                r, state.types.get(r), ci.0, ci.1,
                prev.types.get(r), pi.0, pi.1,
                prev.precise_regs.contains(&r)
            ));
        }
    }
    eprintln!(
        "[zhit] seq={} pc={} curR2={:?}[{}..{}] DIFFS:{}",
        seq, pc, r2t, r2i.0, r2i.1, diffs
    );
}

/// DIAGNOSTIC (ZOVIA_DBG_SKIP_PC): tally children_unsafe prune-skips per pc;
/// dump the top offenders every 50k skips. Finds the cached state(s) whose
/// children_unsafe marking is collapsing convergence and exploding routes.
fn dbg_skip_pc(pc: usize) {
    use std::sync::{Mutex, OnceLock};
    static ON: OnceLock<bool> = OnceLock::new();
    if !*ON.get_or_init(|| std::env::var("ZOVIA_DBG_SKIP_PC").is_ok()) {
        return;
    }
    static T: OnceLock<Mutex<(std::collections::HashMap<usize, u64>, u64)>> = OnceLock::new();
    let m = T.get_or_init(|| Mutex::new((std::collections::HashMap::new(), 0)));
    let mut g = m.lock().unwrap();
    *g.0.entry(pc).or_insert(0) += 1;
    g.1 += 1;
    if g.1 % 3_000 == 0 {
        let mut v: Vec<_> = g.0.iter().map(|(&p, &c)| (c, p)).collect();
        v.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        let top: Vec<String> = v.iter().take(8).map(|(c, p)| format!("pc{}={}", p, c)).collect();
        eprintln!("[skip_pc] total={} top: {}", g.1, top.join(" "));
    }
}

/// Handle pruning decision at a loop point.
/// Returns Some(true) to prune, Some(false) to continue, None if no previous states.
/// Walk cur's `parent_cache_id` lineage and collect the cache_ids of all
/// cached states cur descends from. A prev state whose cache_id is in this
/// set is a true loop-ANCESTOR of cur; one that is not (but is co-active) is
/// a SIBLING. Bounded by a budget to guard against a malformed cycle.
fn collect_ancestor_ids(env: &VerifierEnv, state: &State) -> HashSet<u32> {
    let mut set = HashSet::new();
    let mut next = state.parent_cache_id;
    let mut budget = 16_384u32;
    while let Some(cid) = next {
        if budget == 0 || !set.insert(cid) {
            break;
        }
        budget -= 1;
        match env.state_by_cache_id(cid) {
            Some((_, st)) => next = st.parent_cache_id,
            None => break,
        }
    }
    set
}

fn handle_loop_pruning(
    env: &mut VerifierEnv,
    state: &mut State,
    pc: usize,
    prog: &Program,
    live_regs: &HashSet<Reg>,
    frame_live_slots: &[Option<HashSet<i16>>],
    config: &VerifierConfig,
) -> bool {
    // Loops without conditional exits are infinite - let complexity limit catch them
    if !loop_has_conditional_exit(env, state, pc, prog) {
        env.pruning_stats.loop_no_cond_exit += 1;
        return false;
    }
    env.pruning_stats.loop_walks_attempted += 1;

    // Kernel-faithful iter-loop convergence: in an iterator-style loop
    // (body contains a force-checkpoint), the kernel converges at the
    // iter_next pc itself via `process_iter_next_call` →
    // `widen_imprecise_scalars`. zovia's kfunc-site widening
    // (kfunc.rs::iter_next_fork) is the analog. BUT zovia's
    // `is_at_loop_point` makes EVERY back-edge target a pruning point —
    // a strict superset of kernel's `init_explored_state`'d pcs. If we
    // prune at a non-checkpoint back-edge target before the looped-back
    // state can re-reach the iter_next pc, the kfunc widening never
    // sees a second iter_next visit (`prev_found=false`) and the
    // delayed_precision_mark / loop_state_deps FAs slip through.
    //
    // Defer pruning at non-force-checkpoint pcs INSIDE iter bodies
    // ONLY while iter_next widening hasn't yet fired on at least one
    // active iter slot (depth<2: still on the very first iter_next
    // call). Once widening has fired (depth>=2 on every active iter),
    // resume normal pruning so legitimate iter loops still converge
    // (iter_while_loop / clean_live_states / widen_spill rely on
    // back-edge target subsumption AFTER the widened state stabilises).
    // Unconditional skip breaks those legitimate loops; conditional
    // skip only opens the gate long enough for widening to fire.
    let pc_is_force_checkpoint = env
        .insn_aux_data
        .get(pc)
        .map(|a| a.force_checkpoint)
        .unwrap_or(false);
    // Defer only at an actual back-edge TARGET (kernel-style:
    // `init_explored_state`'d loop head), not at every in-loop body
    // pc — otherwise the body's paths can't prune and the worklist
    // explodes (clean_live_states / iter_nested_deeply_iters with 7
    // nested levels saw 10k+ widening events without convergence).
    if !pc_is_force_checkpoint
        && arrived_via_back_edge(env, state, pc, prog)
        && loop_body_has_force_checkpoint(env, state, pc)
        && this_loop_iter_pre_widening(env, state, pc)
    {
        return false;
    }

    // Pure-subsumption loop pruning: walk prev_states, prune on first
    // hit (kernel `is_state_visited` analog at the loop head). The
    // kernel-absent general-loop widening (per-shape detectors,
    // counter-widening, force_widen_for_may_goto, tnum-only widening,
    // check_loop_convergence) is DELETED — the kernel converges loops
    // via imprecise-scalar-as-wildcard in regsafe + iter-next widening
    // (kfunc.rs::iter_next_fork). For non-iter loops without a
    // wildcard fixpoint, complexity-limit terminates them — matching
    // the kernel's actual behavior (e.g. test_verif_scale_loop3
    // is `should_fail`).
    // cur's ancestor cache_id lineage (walk of the parent_cache_id
    // chain), used to distinguish a true loop-ANCESTOR (cur descends
    // from prev) from a co-active SIBLING at the dfs_paths>0 prune-skip
    // below. Computed lazily — only when an active prev is actually
    // encountered — so converged loops (no active prev) pay nothing.
    let mut ancestor_ids: Option<HashSet<u32>> = None;

    let (hit_idx, miss_idxs, miss_reasons): (
        Option<usize>,
        Vec<usize>,
        Vec<SubsumptionMissReason>,
    ) = if let Some(prev_states) = env.explored_states.get(&pc) {
        let mut h = None;
        let mut m: Vec<usize> = Vec::new();
        let mut r: Vec<SubsumptionMissReason> = Vec::new();
        for (i, prev) in prev_states.iter().enumerate() {
            // Kernel children_unsafe (bcf_refine, verifier.c:24580-81).
            if prev.children_unsafe {
                dbg_skip_pc(pc);
                continue;
            }
            // SCC force_exact: prev is on the current DFS path iff its
            // branches > 0 (cached but DFS through it not yet finished).
            // Kernel-faithful force_exact: the kernel gates RANGE_WITHIN
            // strictness on `incomplete_read_marks(old)` alone
            // (verifier.c v6.15 L20574: `loop = incomplete_read_marks();
            // states_equal(..., loop ? RANGE_WITHIN : NOT_EXACT)`).
            // Earlier zovia ORed in two extra triggers — `prev.branches
            // > 0` and a loop_entry walk — because the SCC machinery
            // was broken (compute_scc misclassified most loop vertices
            // as singletons → callchain=None → backedges never
            // accumulated → incomplete_read_marks always false). With
            // the Tarjan back-prop fix (6f35e7b), incomplete_read_marks
            // is now accurate; the over-broad triggers were forcing
            // RANGE_WITHIN on every non-iter loop iteration whose
            // cached subtree was still open, which prevented imprecise
            // regs (loop counters / accumulators) from short-circuiting
            // in regsafe and caused convergence failure (loop4 → 1M
            // insns / 0 prunes; ksnoop AND mode → 970k bundle entries
            // at one PC).
            let force_exact = crate::analysis::flow::scc::incomplete_read_marks(env, prev);
            // Active-state prune-skip, refined to ANCESTORS ONLY
            // (kernel-faithful; replaces the former base-mode `!env.bcf_enabled`
            // gate and the BCF-only "prune against active ancestors" hack).
            //
            // The kernel's is_state_visited (verifier.c v6.15 L19024) never
            // takes a NOT_EXACT/RANGE_WITHIN prune against an active ancestor
            // (`sl->state.branches>0`) at a plain back-edge — those go
            // `goto miss`. That keeps the EXACT inf-loop trap as the only
            // thing terminating an unbounded loop (conditional_loop / movsx /
            // short_loop1 FA-safety).
            //
            // But "active" in the kernel's strict DFS means specifically an
            // ANCESTOR on the current path (the loop's own prior iterations).
            // A SIBLING that forked earlier in the same iteration (e.g. the
            // two arms of an `if r0==0` inside the loop body) is fully
            // EXPLORED by the kernel before the next arrival collides with it,
            // so the kernel DOES prune against it. zovia's interleaved
            // worklist keeps such siblings co-active (dfs_paths>0) when cur
            // arrives, so a blanket dfs_paths>0 skip wrongly protects them:
            // they accumulate ~one extra state per body-fork per iteration and
            // bounded loops blow up exponentially (measured on from_hep
            // calico_tc_skb_accepted pc293, sparse caching: 108,884
            // cap-evictions → thorough-mode timeout when the skip was
            // unconditional).
            //
            // Refinement: skip ONLY when prev is a true ancestor of cur (its
            // cache_id lies on cur's parent_cache_id lineage). For a co-active
            // sibling, fall through to state_subsumed_by — the prune the
            // kernel's strict DFS would have taken. Ancestors (and any prev
            // with no cache_id, treated conservatively) still skip, so
            // inf-loop FA-safety is preserved by direction. Validated: FA=0
            // and 0 selftest regressions; calico-19 BCF bundles byte-identical
            // to the prior gated HEAD.
            // Kernel blanket branches>0 gate — see the matching comment in
            // handle_standard_pruning. (Ancestors-only was a carve-out for
            // the broken branches accounting, repaired in ee5221c.)
            let skip_active = prev.branches > 0;
            if skip_active {
                if crate::analysis::trace_pc_in_range(pc) {
                    eprintln!(
                        "[SUBSUM_SKIP_ACTIVE] pc={} prev_idx={} prev.dfs_paths={} cache_id={:?}",
                        pc, i, prev.dfs_paths, prev.cache_id,
                    );
                }
                // Record as a miss so the kernel-faithful eviction
                // (record_pruning_misses, n=3 at plain back-edges) keeps the
                // per-pc cache small. Without this the FIFO cap (64) fills
                // with distinct-precise-counter states that all miss, making
                // every back-edge arrival walk 64 entries (O(N·64)) — the
                // dominant cost on big bounded loops like nested_loops.
                m.push(i);
                continue;
            }
            match state_subsumed_by(state, prev, live_regs, frame_live_slots, config, force_exact) {
                Ok(()) => {
                    zhit_seq(pc, state, prev);
                    if crate::analysis::trace_pc_in_range(pc) {
                        eprintln!(
                            "[SUBSUM_HIT] pc={} prev_idx={} prev.dfs_paths={} force_exact={}",
                            pc, i, prev.dfs_paths, force_exact,
                        );
                    }
                    h = Some(i);
                    break;
                }
                Err(reason) => {
                    if crate::analysis::trace_pc_in_range(pc) {
                        eprintln!(
                            "[SUBSUM_MISS] pc={} prev_idx={} reason={:?} prev.dfs_paths={} force_exact={}",
                            pc, i, reason, prev.dfs_paths, force_exact,
                        );
                    }
                    m.push(i);
                    r.push(reason);
                }
            }
        }
        (h, m, r)
    } else {
        env.pruning_stats.loop_walks_no_prev += 1;
        return false;
    };

    if let Some(idx) = hit_idx {
        env.pruning_stats.loop_walks_hit += 1;
        record_pruning_hit(env, pc, idx);
        // Kernel-aligned propagate_precision (verifier.c v6.15 L18828):
        // pull cached's precise-mark set into cur's parent-cache lineage
        // so the path's continuation tracks the same precision contract.
        if let Some(prev) = env.explored_states.get(&pc).and_then(|v| v.get(idx)).cloned() {
            crate::analysis::flow::precision::propagate_precision(env, state, &prev);
            // SCC: at a force_exact hit, propagate prev's loop_entry to
            // cur (verifier.c L19178). cur is about to be pruned and
            // complete_dfs_branch will walk up; carrying the loop_entry
            // lets the propagation reach the parent chain. We also seed
            // from prev's cache_id when prev itself is the entry.
            if prev.branches > 0 {
                let le = prev
                    .cache_id
                    .and_then(|cid| crate::analysis::flow::scc::get_loop_entry(env, cid))
                    .or(prev.cache_id);
                if let Some(lcid) = le {
                    crate::analysis::flow::scc::update_loop_entry(env, state, lcid);
                }
            }
            // Kernel-faithful add_scc_backedge gate (verifier.c v6.15
            // L20671-20686): backedges are only added when `loop` was
            // already true at this hit — i.e. visit.backedges was
            // already non-empty. Earlier zovia gated on `prev.branches
            // > 0` (a strict superset of the kernel's gate), claiming
            // "overcollecting is sound." It is not — overcollecting
            // inflates incomplete_read_marks for non-iter loops, which
            // forces every subsequent pruning attempt into RANGE_WITHIN
            // mode and defeats the regsafe SCALAR imprecise short-
            // circuit. Result: loop4-class loops never converge past
            // their first hit. The kernel's stricter gate means
            // backedges never accumulate from this site on a fresh
            // SCC visit, so non-iter loops stay in NOT_EXACT mode and
            // converge naturally; iter loops handle their own
            // convergence via widen_imprecise_scalars at iter_next
            // (kfunc.rs::iter_next_fork — independent of backedges).
            if crate::analysis::flow::scc::incomplete_read_marks(env, &prev)
                && let Some(prev_cid) = prev.cache_id
            {
                crate::analysis::flow::scc::add_scc_backedge(env, state, prev_cid, pc);
            }
        }
        env.pruning_stats.loop_walks_pruned_via_convergence += 1;
        return true;
    }

    env.pruning_stats.loop_walks_miss += 1;
    record_pruning_misses(env, pc, &miss_idxs);
    record_subsumption_miss_reasons(env, pc, &miss_reasons);

    false
}

/// Handle standard (non-loop) subsumption check.
fn handle_standard_pruning(
    env: &mut VerifierEnv,
    state: &State,
    pc: usize,
    live_regs: &HashSet<Reg>,
    frame_live_slots: &[Option<HashSet<i16>>],
    config: &VerifierConfig,
) -> bool {
    let mut hit_idx: Option<usize> = None;
    let mut miss_idxs: Vec<usize> = Vec::new();
    let mut miss_reasons: Vec<SubsumptionMissReason> = Vec::new();
    let mut local_children_unsafe_skips: u64 = 0;
    // Kernel `is_state_visited` `is_iter_next_insn` branch (verifier.c v6.15
    // L19079): iterator convergence ALWAYS uses `states_equal(RANGE_WITHIN)`,
    // never the looser NOT_EXACT. RANGE_WITHIN range-checks even non-precise
    // scalars (the `!rold->precise && exact==NOT_EXACT` wildcard shortcut does
    // NOT fire), which is exactly what catches iters.c::delayed_precision_mark:
    // at the iter_next call r7 is reachable as -16 and -33 with no precision
    // mark; NOT_EXACT would wildcard r7 and merge the two, dropping the unsafe
    // `*(r10 + r7=-33)` deref. Forcing RANGE_WITHIN keeps them distinct so the
    // widened (unbounded) r7 reaches the access and is rejected. `iter_pc_slot`
    // is populated at every iter_next site by iter_next_fork.
    let iter_next_pc = env.iter_pc_slot.contains_key(&pc);
    let mut ancestor_ids: Option<HashSet<u32>> = None;
    if let Some(prev_states) = env.explored_states.get(&pc) {
        for (i, prev) in prev_states.iter().enumerate() {
            // Kernel children_unsafe (bcf_refine, verifier.c:24580-81):
            // a path-unreachable refinement marked this cached ancestor
            // not-prune-safe. Don't let it subsume a later arrival.
            if prev.children_unsafe {
                local_children_unsafe_skips += 1;
                dbg_skip_pc(pc);
                continue;
            }
            // Kernel `is_state_visited`: a cached state with branches>0
            // NEVER subsumes a normal arrival (`if (sl->state.branches)
            // ... goto miss`, verifier.c v6.15 L19024) — at EVERY prune
            // point, not just loop heads. Same ancestors-only refinement
            // as handle_loop_pruning's skip_active (see the long comment
            // there): a co-active SIBLING under zovia's interleaved
            // worklist is a state the kernel's strict DFS would have
            // fully explored, so it may subsume; a true ANCESTOR on
            // cur's own lineage must not (the kernel's rule — exposed at
            // the pc18/619 outer-loop heads once slot cleaning became
            // read-mark-driven: a descendant merged into its own
            // still-active ancestor 365x where the kernel prunes 6x).
            // Kernel blanket gate: `if (sl->state.branches) ... goto miss`
            // — a cached state whose subtree is still in flight NEVER
            // subsumes a normal arrival, sibling or ancestor. The former
            // ancestors-only carve-out was tuned under the broken
            // dense-caching branches accounting (everything looked
            // permanently active, so a blanket skip skipped everything);
            // with kernel-shape branches (ee5221c) the blanket gate is
            // the faithful rule. Divergence this closes (kernel #37/38):
            // the 584<-521 R1=0 state is added ~100 insns before the
            // TCP-arm wide-R2 arrival compares at 584; the kernel
            // silently misses on branches>0 (zero [ZK sv584] compares
            // against it), zovia's sibling carve-out let the compare run
            // -> imprecise-R2 free-pass -> the sponge-subtree's R2 died
            // at 584 instead of reaching 748.
            if prev.branches > 0 {
                if crate::analysis::trace_pc_in_range(pc) {
                    eprintln!(
                        "[SUBSUM_SKIP_ACTIVE] pc={} prev_idx={} prev.branches={} cache_id={:?} (standard)",
                        pc, i, prev.branches, prev.cache_id,
                    );
                }
                continue;
            }
            // Kernel-faithful force_exact (see matching block above for
            // full rationale and history). At iter_next sites the kernel
            // pins RANGE_WITHIN regardless of read-mark completeness.
            let force_exact =
                iter_next_pc || crate::analysis::flow::scc::incomplete_read_marks(env, prev);
            match state_subsumed_by(state, prev, live_regs, frame_live_slots, config, force_exact) {
                Ok(()) => {
                    zhit_seq(pc, state, prev);
                    hit_idx = Some(i);
                    break;
                }
                Err(reason) => {
                    if crate::analysis::trace_pc_in_range(pc) {
                        eprintln!(
                            "[SUBSUM_MISS] pc={} prev_idx={} reason={:?} prev.dfs_paths={} force_exact={} (non-loop site)",
                            pc, i, reason, prev.dfs_paths, force_exact,
                        );
                    }
                    miss_idxs.push(i);
                    miss_reasons.push(reason);
                }
            }
        }
    }
    env.pruning_stats.children_unsafe_skips =
        env.pruning_stats.children_unsafe_skips.saturating_add(local_children_unsafe_skips);
    if let Some(idx) = hit_idx {
        record_pruning_hit(env, pc, idx);
        // Kernel-aligned propagate_precision (per-path lineage walk).
        if let Some(prev) = env.explored_states.get(&pc).and_then(|v| v.get(idx)).cloned() {
            crate::analysis::flow::precision::propagate_precision(env, state, &prev);
        }
        true
    } else {
        record_pruning_misses(env, pc, &miss_idxs);
        record_subsumption_miss_reasons(env, pc, &miss_reasons);
        false
    }
}

/// Bump the per-PC subsumption-miss histogram. One increment per
/// rejected sub-check, attributed to the *first* sub-check that
/// rejected (later checks short-circuit). Cheap; safe to call on every
/// miss path. The end-of-analysis dump reads this histogram.
fn record_subsumption_miss_reasons(
    env: &mut VerifierEnv,
    pc: usize,
    reasons: &[SubsumptionMissReason],
) {
    if reasons.is_empty() {
        return;
    }
    env.pruning_stats.lifetime_misses += reasons.len() as u64;
    let entry = env
        .subsumption_misses
        .entry(pc)
        .or_insert([0u64; 9]);
    for r in reasons {
        entry[r.idx()] = entry[r.idx()].saturating_add(1);
    }
}

/// Check if we should prune this state (already covered by a previous exploration).
/// For loop heads with conditional exits, applies widening to accelerate convergence.
pub fn should_prune(
    env: &mut VerifierEnv,
    state: &mut State,
    config: &VerifierConfig,
    prog: &Program,
) -> bool {
    let pc = state.pc;

    env.pruning_stats.should_prune_calls += 1;

    if crate::analysis::trace_pc_in_range(pc) {
        let nprev = env.explored_states.get(&pc).map(|v| v.len()).unwrap_or(0);
        eprintln!(
            "[SP_ENTRY] pc={} nprev={} is_prune_point={}",
            pc, nprev, is_prune_point(env, pc)
        );
    }

    if !is_prune_point(env, pc) {
        env.pruning_stats.not_prune_point += 1;
        return false;
    }

    // Kernel `clean_live_states(env, insn_idx)` — called at the top of
    // every `is_state_visited`: LAZILY clean any cached state at this pc
    // whose subtree completed (branches==0) but which was skipped
    // earlier (e.g. its SCC still had pending backedges at eager-clean
    // time). Without the retry, states inside a long-running loop SCC
    // are never cleaned and every later compare runs against the fat
    // state (from_nat_fib pc2200: 1913 Stack misses vs kernel 76/78
    // prune rate — the tail-call epilogue explosion).
    {
        let to_clean: Vec<u32> = env
            .explored_states
            .get(&pc)
            .map(|v| {
                v.iter()
                    .filter(|s| !s.cleaned && s.branches == 0)
                    .filter_map(|s| s.cache_id)
                    .collect()
            })
            .unwrap_or_default();
        for cid in to_clean {
            crate::analysis::flow::pruning::cache::clean_verifier_state(env, cid);
        }
    }

    let is_on_path = state
        .history_idx
        .map(|idx| env.history.is_on_path(idx, pc))
        .unwrap_or(false);

    let in_loop = is_at_loop_point(env, state, pc, prog);

    // iter_next call sites are virtual loop heads: the kernel's
    // is_state_visited runs the RANGE_WITHIN + active-iter check at
    // the iter_next CALL pc (verifier.c v6.15 L19078-L19101), and the
    // cached state at this pc is the convergence target for the loop.
    // Mirror that by NOT shortcut-skipping on `is_on_path && !in_loop`
    // when this pc is a force-checkpointed Call (force_checkpoint at
    // a Call instruction = iter_next or sync-callback helper site).
    // Without this, under ZOVIA_KERNEL_ENGINE=1's sparse caching the
    // iter loop's back-edge target (a body pc) isn't cached, the
    // iter_next call site IS cached but pruning short-circuits via
    // on_path → bpf_iter_num loops never converge → timeout.
    // Generalized to ALL force-checkpoint pcs (iter_next/sync-cb Call sites
    // AND may_goto insns): the kernel's is_state_visited runs at EVERY
    // checkpoint and converges may_goto loops AT the may_goto pc itself
    // (verifier.c L19102, RANGE_WITHIN + depth-differ) — not at the loop's
    // back-edge target. A may_goto pc is a force-checkpoint but NOT a
    // back-edge target, so `in_loop` is false there; without exempting it
    // from the on-path skip, may_goto_range_within_prune never runs and the
    // loop only converges via the (non-kernel) active-ancestor hit.
    let pc_is_force_checkpoint = env
        .insn_aux_data
        .get(pc)
        .map(|a| a.force_checkpoint)
        .unwrap_or(false)
        && matches!(
            prog.instrs.get(pc),
            Some(Instr::Call { .. }) | Some(Instr::MayGoto { .. })
        );

    // DIAG (pc521 d53): when this pc is traced and prev cached states
    // already exist, log the early-decision inputs so we can see WHY a
    // second arm's subsumption is skipped (the kernel compares here and
    // keeps ONE state; zovia forms two).
    if crate::analysis::trace_pc_in_range(pc) {
        let nprev = env.explored_states.get(&pc).map(|v| v.len()).unwrap_or(0);
        if nprev > 0 {
            eprintln!(
                "[SP_GATE] pc={} nprev={} is_on_path={} in_loop={} force_ckpt={} prune_point={} -> would_skip_onpath={}",
                pc, nprev, is_on_path, in_loop, pc_is_force_checkpoint,
                is_prune_point(env, pc),
                is_on_path && !in_loop && !pc_is_force_checkpoint,
            );
        }
    }

    // Re-entry to a PC from a different depth (e.g. repeated call in a loop).
    // Must continue to reach the actual loop back-edge.
    if is_on_path && !in_loop && !pc_is_force_checkpoint {
        env.pruning_stats.on_path_skip += 1;
        return false;
    }

    // Track whether we actually have prev states to compare against.
    // Distinguishes "first visit (no work for cache to do)" from "had
    // prev states; either hit or miss happened downstream".
    if env
        .explored_states
        .get(&pc)
        .map(|v| v.is_empty())
        .unwrap_or(true)
    {
        env.pruning_stats.no_prev_states += 1;
    } else if in_loop {
        env.pruning_stats.loop_pruning_calls += 1;
    } else {
        env.pruning_stats.std_pruning_calls += 1;
    }

    let live_regs = env.insn_aux_data[pc].live_regs.clone();
    // clean_verifier_state analog: the kernel zeroes dead stack slots
    // (clean_func_state → STACK_INVALID) so stacksafe never compares
    // them. zovia's static `live_slots` (sound over-approx MAY-liveness)
    // is the equivalent; threaded into `stack_subsumed_by` so a dead
    // scratch slot can't block a prune (mirrors the existing
    // `live_regs` filtering in types/domain subsumption).
    // Per-frame clean_verifier_state: the kernel cleans EVERY frame at
    // its own ip (clean_func_state via frame_insn_idx, verifier.c:19463),
    // not just the innermost. The innermost frame's ip is `pc`; a caller
    // frame i is paused at its call and resumes at frame[i+1].return_pc,
    // so its slots are dead iff unread from there. `None` = liveness
    // unknown for that frame ⇒ DON'T skip (full compare — the sound
    // direction). Built once (cur's frame shape is fixed; old zips 1:1
    // by callsite).
    // Kernel `stacksafe` has NO in-compare liveness skip: dead slots are
    // removed from CACHED states by `clean_verifier_state` (now driven by
    // the dynamic live-stack marks, see flow::live_stack); an uncleaned
    // state (branches>0 / pending SCC backedges) is compared in FULL.
    // The former static-live_slots skip here was an extra merge-enabler
    // the kernel doesn't have (it hid per-byte slot-kind mismatches the
    // kernel blocks on — from_nat_fib pc1375 fp-24 ZERO-vs-MISC).
    let nframes = state.frames.depth();
    let frame_live_slots: Vec<Option<HashSet<i16>>> = vec![None; nframes];

    // Kernel-faithful infinite-loop trap (verifier.c v6.15 L19114-L19127,
    // `is_state_visited`'s inf-loop check). For any cached state at this
    // pc whose topmost-frame regs are bytewise identical to cur AND whose
    // full state matches EXACT AND iter active depths don't differ AND
    // may_goto_depth matches ⇒ "infinite loop detected".
    //
    // Skipped at iter_next call sites and sync-callback-call helper sites
    // (kernel `is_iter_next_insn` / `calls_callback` short-circuits at
    // L19073 / L19111). MayGoto is NOT skipped: the may_goto_depth
    // equality gate inside the check naturally lets it through (the
    // taken edge bumps the depth, so a recurrence with same depth means
    // no progress on the may_goto counter ⇒ stuck).
    // Only run the inf-loop trap at actual back-edge TARGETS (loop heads).
    // The kernel's is_state_visited fires at every prune point, but
    // zovia's per-state liveness/precision bookkeeping isn't granular
    // enough to mirror the kernel's `live`-flag discrimination — so at
    // mid-loop convergence prune points (`is_at_loop_point=false`) the
    // check over-fires on legitimate cilium loops whose iterations
    // happen to produce byte-identical zovia abstract states even
    // though the kernel sees per-iter progress. Restricting to true
    // loop heads keeps the trap narrow enough to detect genuine
    // verifier-divergent infinite loops (the conditional_loop /
    // infinite_loop_* / mov64sx_s32_varoff_1 family) while avoiding
    // the cilium FR-regression.
    // Additionally skip when ANY frame has an active iterator: the kernel
    // gates iter-loop convergence on `iter_active_depths_differ` + SCC
    // (`loop_entry` / `dfs_depth` / `branches`, verifier.c L1885+). zovia
    // tracks depth-differ but not SCC, so at body pcs inside an iter
    // loop where the depth has stabilized (legit pruning iteration), the
    // EXACT check fires on byte-identical body states that the kernel
    // distinguishes via SCC's per-state `branches` count. Skipping at
    // any-active-iter avoids the false-reject regression on
    // verifier_bits_iter.c::max_words and the like; iter_next sites
    // themselves are already covered by `is_inf_loop_skip_pc` for the
    // kernel's `is_iter_next_insn` short-circuit.
    let any_active_iter = state
        .frames
        .iter()
        .any(|f| f.stack.has_active_iterators());
    if in_loop
        && !any_active_iter
        && pc < prog.instrs.len()
        && let Some(prev_states) = env.explored_states.get(&pc).cloned()
        && !is_inf_loop_skip_pc(prog, pc)
    {
        for prev in prev_states.iter() {
            // Kernel-faithful gate (verifier.c v6.15 L19024): the entire
            // inf-loop check is wrapped in `if (sl->state.branches)`. A
            // cached state with branches==0 (kernel semantics) has had
            // its entire downstream DFS completed — a second arrival
            // that byte-matches it is the normal subsumption case, NOT
            // a stuck loop. Without this gate zovia false-rejects
            // programs like pro_epilogue_goto_start where the first
            // back-edge arrival at the loop head takes a terminating
            // branch (e.g. r1=0 → if r1==0 → exit) and fully completes
            // before a second back-edge arrival via a different
            // predecessor path lands at the same state.
            //
            // Zovia checks `dfs_paths` instead of `branches` because
            // zovia's `branches` field has different (per-push)
            // accounting than the kernel's `branches`; changing it to
            // kernel semantics broke ~125 selftests (iters.c family
            // etc.). `dfs_paths` is the parallel kernel-faithful
            // counter dedicated to this gate. See State::dfs_paths.
            if prev.dfs_paths == 0 {
                continue;
            }
            // Kernel `states_maybe_looping` (verifier.c v6.15 L20137):
            // memcmp(regs, ..., offsetof(struct bpf_reg_state, frameno))
            // compares EVERY field including `reg.parent` (the upward
            // pointer to the predecessor state's matching reg, used by
            // precision back-propagation). Two iters reaching the same
            // PC with identical *values* but distinct DFS parent chains
            // have different `reg.parent` pointers → memcmp non-zero →
            // states_maybe_looping=false → kernel SKIPS the inf-loop
            // check and falls through to the regular subsumption-prune
            // path (where states_equal with RANGE_WITHIN/EXACT acts as
            // a HIT, not a reject).
            //
            // Zovia's `state_exact_equal` only compares VALUES (types,
            // intervals, tnums, scalar_ids) — no parent-pointer
            // equivalent — so it false-positives on sibling-DFS-branch
            // value convergence. To approximate the kernel's
            // discrimination, require prev's cache_id to appear in
            // cur's parent_cache_id lineage: only then is this a TRUE
            // single-path cycle. Convergent siblings get the prune
            // path below (state_exact_equal => subsumption hit).
            //
            // Concretely on calico anchor new_flow_entrypoint (post
            // jmp_history_cnt fix, 2026-05-22): R7 differs at loop
            // head PC 2844 across iterations (R7 increments) but is
            // overwritten to a constant in the loop body, so two iters
            // reach the loop tail PC 3059 with byte-identical reg
            // values. Without the lineage gate the trap fires; with
            // it, sibling-iter convergence falls through to the regular
            // prune path and exploration terminates correctly.
            let prev_cid = prev.cache_id;
            let in_lineage = prev_cid.is_some() && {
                let mut cur_anc = state.parent_cache_id;
                let mut steps = 0usize;
                let mut found = false;
                while let Some(cid) = cur_anc {
                    if Some(cid) == prev_cid {
                        found = true;
                        break;
                    }
                    if steps > 4096 {
                        break;
                    }
                    steps += 1;
                    cur_anc = env
                        .state_by_cache_id(cid)
                        .and_then(|(_, s)| s.parent_cache_id);
                }
                found
            };
            if !in_lineage {
                continue;
            }
            if prev.may_goto_depth != state.may_goto_depth {
                continue;
            }
            if iter_active_depths_differ(prev, state) {
                continue;
            }
            if state_exact_equal(prev, state) {
                // ZOVIA_TRAP_DEBUG=1 — dump prev vs cur side-by-side when the
                // inf-loop trap fires, so we can see which fields kernel
                // treats as distinct that zovia treats as identical.
                if std::env::var("ZOVIA_TRAP_DEBUG").ok().as_deref() == Some("1") {
                    use crate::analysis::machine::reg::Reg;
                    eprintln!("[TRAP] === inf-loop fire at pc={} ===", pc);
                    eprintln!("[TRAP] prev.dfs_paths={} cur.dfs_paths={}", prev.dfs_paths, state.dfs_paths);
                    eprintln!("[TRAP] prev.may_goto_depth={} cur.may_goto_depth={}", prev.may_goto_depth, state.may_goto_depth);
                    eprintln!("[TRAP] depth prev={} cur={}", prev.frames.depth(), state.frames.depth());
                    // Walk full history, count visits to PC, and find any non-linear jumps
                    let mut hist_pcs: Vec<usize> = Vec::new();
                    let mut idx = state.history_idx;
                    let mut visits_to_trap_pc = 0;
                    while let Some(i) = idx {
                        match env.history.get(i) {
                            Some(step) => {
                                if step.pc == pc { visits_to_trap_pc += 1; }
                                hist_pcs.push(step.pc);
                                idx = step.parent_idx;
                                if hist_pcs.len() > 5000 { break; }
                            }
                            None => break,
                        }
                    }
                    eprintln!("[TRAP] cur history len={}  visits_to_pc{}={}", hist_pcs.len(), pc, visits_to_trap_pc);
                    eprintln!("[TRAP] last 15 PCs (most-recent first): {:?}", &hist_pcs[..hist_pcs.len().min(15)]);
                    // find non-linear transitions: prev PC where next != prev+1
                    let mut jumps: Vec<(usize, usize)> = Vec::new();
                    for w in hist_pcs.windows(2) {
                        let (newer, older) = (w[0], w[1]);
                        if newer != older + 1 && newer != older + 2 { // skip LD_IMM64 stride
                            jumps.push((older, newer));
                            if jumps.len() > 20 { break; }
                        }
                    }
                    eprintln!("[TRAP] non-linear jumps in history (older->newer): {:?}", jumps);
                    eprintln!("[TRAP] cur parent_cache_id={:?} prev.cache_id={:?}", state.parent_cache_id, prev.cache_id);
                    for r in Reg::ALL {
                        let pty = prev.types.get(r);
                        let cty = state.types.get(r);
                        let (plo, phi) = prev.domain.get_interval(r);
                        let (clo, chi) = state.domain.get_interval(r);
                        let psid = prev.scalar_ids.get(&r).copied().unwrap_or(0);
                        let csid = state.scalar_ids.get(&r).copied().unwrap_or(0);
                        let same_ty = pty == cty;
                        let same_iv = (plo, phi) == (clo, chi);
                        let same_u32 = prev.domain.get_u32_bounds(r) == state.domain.get_u32_bounds(r);
                        let same_tn = prev.tnums.get(&r) == state.tnums.get(&r);
                        let same_sid = psid == csid;
                        eprintln!(
                            "[TRAP] {:?}: ty={} iv={} u32={} tn={} sid={} | prev_ty={:?} iv=[{}..{}] sid={} | cur_ty={:?} iv=[{}..{}] sid={}",
                            r, if same_ty {"="} else {"≠"}, if same_iv {"="} else {"≠"},
                            if same_u32 {"="} else {"≠"}, if same_tn {"="} else {"≠"},
                            if same_sid {"="} else {"≠"},
                            pty, plo, phi, psid, cty, clo, chi, csid,
                        );
                    }
                    // Top-frame stack slot diffs
                    use crate::analysis::machine::frame_stack::FrameLevel;
                    let top = FrameLevel::from_index(prev.frames.depth().saturating_sub(1));
                    let pf = prev.frames.get(top);
                    let cf = state.frames.get(top);
                    // explicit: dump the fp-0x128 (-296) slot specifically
                    let pslot = pf.stack.get_slot(-296);
                    let cslot = cf.stack.get_slot(-296);
                    eprintln!("[TRAP] fp-296 (= fp-0x128): prev={:?}", pslot);
                    eprintln!("[TRAP] fp-296 (= fp-0x128): cur ={:?}", cslot);
                    let mut all_offs: std::collections::BTreeSet<i16> = pf.stack.slot_offsets().into_iter().collect();
                    all_offs.extend(cf.stack.slot_offsets());
                    for off in all_offs {
                        let ps = pf.stack.get_slot(off);
                        let cs = cf.stack.get_slot(off);
                        let same = match (ps, cs) {
                            (Some(a), Some(b)) => a == b,
                            (None, None) => true,
                            _ => false,
                        };
                        if !same {
                            eprintln!("[TRAP] fp{}: DIFF prev={:?} cur={:?}", off, ps, cs);
                        }
                    }
                    eprintln!("[TRAP] === end ===");
                }
                env.fail(crate::analysis::machine::error::VerificationError::InfiniteLoopDetected {
                    pc,
                });
                return true;
            }
        }
    }

    // Under BPF_F_TEST_STATE_FREQ, bypass all subsumption-hit pruning
    // (may_goto RANGE_WITHIN, loop pruning, standard pruning). The
    // inf-loop trap above already ran. Kernel verifier.c L18998 sets
    // `force_new_state=true` under this flag — every visit gets cached
    // as a fresh entry and explored to completion. This is the
    // load-bearing mechanism for iters.c::loop_state_deps1/2: their
    // unsafe paths are reached only when each iteration's r6/r7 state
    // is tracked distinctly rather than collapsed by subsumption.
    if env.ctx.has_flag(crate::common::constants::F_TEST_STATE_FREQ) {
        return false;
    }

    // may_goto-specific RANGE_WITHIN prune class.
    if pc < prog.instrs.len()
        && matches!(prog.instrs[pc], Instr::If { .. } | Instr::MayGoto { .. })
        && let Some(prev_states) = env.explored_states.get(&pc)
    {
        let is_may_goto = matches!(prog.instrs[pc], Instr::MayGoto { .. });
        if is_may_goto
            && may_goto_range_within_prune(state, prev_states, &live_regs, &frame_live_slots, config)
        {
            env.pruning_stats.may_goto_range_within_hits += 1;
            return true;
        }
    }

    let pruned = if in_loop {
        handle_loop_pruning(env, state, pc, prog, &live_regs, &frame_live_slots, config)
    } else {
        handle_standard_pruning(env, state, pc, &live_regs, &frame_live_slots, config)
    };
    pruned
}

/// bump miss_cnt for every `prev_idx` and evict whose
/// `miss_cnt > hit_cnt * n + n` (kernel verifier.c v6.15 L19222-L19233).
/// `n = 64` at force-checkpoint pcs (iter_next, may_goto, sync-cb-call
/// helpers); `n = 3` elsewhere. Caller passes the indices of every
/// cached state that was walked-past during a failed subsumption check;
/// hit cases use `record_pruning_hit` instead.
fn record_pruning_misses(env: &mut VerifierEnv, pc: usize, miss_idxs: &[usize]) {
    if miss_idxs.is_empty() {
        return;
    }
    let force = env
        .insn_aux_data
        .get(pc)
        .map(|a| a.force_checkpoint)
        .unwrap_or(false);

    // Read `branches` per cached state for the kernel-faithful `n`
    // formula (verifier.c v6.18-rc4 L20444):
    //   n = is_force_checkpoint && sl->state.branches > 0 ? 64 : 3
    // `branches > 0` means the cached state's downstream DFS is still in
    // progress (it's part of an active SCC iteration); the kernel
    // protects these from premature eviction at force-checkpoint pcs.
    let branches_by_idx: std::collections::HashMap<usize, u32> = if let Some(states) =
        env.explored_states.get(&pc)
    {
        miss_idxs
            .iter()
            .filter_map(|&i| states.get(i).map(|s| (i, s.branches)))
            .collect()
    } else {
        std::collections::HashMap::new()
    };

    let mut to_evict: Vec<usize> = Vec::new();
    if let Some(metrics) = env.state_metrics.get_mut(&pc) {
        for &i in miss_idxs {
            if let Some(m) = metrics.get_mut(i) {
                m.miss_cnt = m.miss_cnt.saturating_add(1);
                // Kernel L20444 exactly: n = force_checkpoint && branches>0 ? 64 : 3
                let branches = branches_by_idx.get(&i).copied().unwrap_or(0);
                let n: u32 = if force && branches > 0 { 64 } else { 3 };
                if m.miss_cnt > m.hit_cnt.saturating_mul(n).saturating_add(n) {
                    to_evict.push(i);
                }
            }
        }
    }
    if to_evict.is_empty() {
        return;
    }
    // Sort descending so removals don't shift later indices.
    to_evict.sort_unstable_by(|a, b| b.cmp(a));
    // Kernel is_state_visited L20455-64: eviction moves the state to
    // env->free_list (it stays resolvable through descendants'
    // st->parent until branches == 0), it is NOT destroyed. Retire the
    // evicted State objects so parent-chain walks (branches accounting,
    // bcf backtrack base, children_unsafe marking, replay base fetch)
    // keep working — destroying them here was the from_l3_fib_no_log
    // pc222 0x94363000 miss (base state evicted → bcf_suffix_base_pc
    // None → base-less goal).
    let mut evicted: Vec<State> = Vec::new();
    if let Some(states) = env.explored_states.get_mut(&pc) {
        for &i in &to_evict {
            if i < states.len() {
                evicted.push(states.remove(i));
            }
        }
    }
    if let Some(metrics) = env.state_metrics.get_mut(&pc) {
        for &i in &to_evict {
            if i < metrics.len() {
                metrics.remove(i);
            }
        }
    }
    // cache_loc_by_id cleanup: drop evicted ids (they resolve through
    // retired_states from now on), re-index survivors. Same invariant
    // as the FIFO drain in `merging::record_state`.
    for s in evicted {
        if let Some(id) = s.cache_id {
            env.cache_loc_by_id.remove(&id);
            env.retire_state(id, pc, s);
        }
    }
    if let Some(states) = env.explored_states.get(&pc) {
        for (new_idx, s) in states.iter().enumerate() {
            if let Some(id) = s.cache_id {
                env.cache_loc_by_id.insert(id, (pc, new_idx));
            }
        }
    }
}

/// bump hit_cnt for the cached state at `prev_idx`.
fn record_pruning_hit(env: &mut VerifierEnv, pc: usize, prev_idx: usize) {
    env.pruning_stats.lifetime_hits += 1;
    if let Some(metrics) = env.state_metrics.get_mut(&pc)
        && let Some(m) = metrics.get_mut(prev_idx)
    {
        m.hit_cnt = m.hit_cnt.saturating_add(1);
    }
}

/// RANGE_WITHIN prune class for may_goto pcs.
///
/// Tries to subsume `cur` against any prev state where the
/// `may_goto_depth` differs (mandatory: same depth would hit the EXACT
/// inf-loop trap instead). Subsumption is run with `cur`'s precision
/// marks cleared — the kernel's RANGE_WITHIN equivalent — so a
/// loop-counter that's been precision-marked at a body memory access
/// can still converge once its abstract value lies inside the cached
/// range.
fn may_goto_range_within_prune(
    cur: &State,
    prev_states: &[State],
    live_regs: &HashSet<Reg>,
    frame_live_slots: &[Option<HashSet<i16>>],
    config: &VerifierConfig,
) -> bool {
    // Build a precision-stripped clone of `cur` once. State carries
    // precision in two places: `precise_regs` (per-reg) and
    // `SpilledReg::precise` (per stack slot).
    let mut relaxed = cur.clone();
    relaxed.precise_regs.clear();
    use crate::analysis::machine::frame_stack::FrameLevel;
    for fi in 0..relaxed.frames.depth() {
        let level = FrameLevel::from_index(fi);
        let stack = &mut relaxed.frames.get_mut(level).stack;
        for off in stack.slot_offsets() {
            if let Some(slot) = stack.get_slot_mut(off) {
                slot.precise = false;
            }
        }
    }

    for prev in prev_states {
        if prev.may_goto_depth == cur.may_goto_depth {
            continue;
        }
        // Misses on this auxiliary RANGE_WITHIN prune class are
        // intentionally NOT recorded in the subsumption-miss histogram —
        // they would inflate the "stack" / "tnum" buckets with the
        // precision-stripped clone's behaviour, which isn't the same
        // as the standard subsumption pipeline we're trying to measure.
        // may_goto RANGE_WITHIN prune class explicitly relaxes precision;
        // pass force_exact=false so domain_subsumed_by keeps its NOT_EXACT
        // semantics for non-precise regs (the relaxed clone has cleared
        // precise_regs anyway).
        if state_subsumed_by(&relaxed, prev, live_regs, frame_live_slots, config, false).is_ok() {
            return true;
        }
    }
    false
}
