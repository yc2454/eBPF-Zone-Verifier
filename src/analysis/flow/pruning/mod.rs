// src/analysis/flow/pruning/mod.rs
//
// Pruning orchestration: should_prune, handle_loop_pruning,
// handle_standard_pruning, and supporting bookkeeping.
// Loop detection + widening math live in widening.rs.
// Subsumption predicates live in subsumption.rs.

mod subsumption;
mod widening;

use std::collections::HashSet;

use crate::analysis::machine::env::{SubsumptionMissReason, VerifierEnv};
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{Instr, Program};
use crate::common::config::VerifierConfig;
use subsumption::{iter_active_depths_differ, state_exact_equal, state_subsumed_by};
use widening::{
    arrived_via_back_edge, is_at_loop_point, is_prune_point, loop_body_has_force_checkpoint,
    loop_has_conditional_exit, loop_has_if_exit, this_loop_iter_pre_widening,
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

/// Handle pruning decision at a loop point.
/// Returns Some(true) to prune, Some(false) to continue, None if no previous states.
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
                continue;
            }
            // SCC force_exact: prev is on the current DFS path iff its
            // branches > 0 (cached but DFS through it not yet finished).
            // The kernel uses `get_loop_entry(sl)->branches > 0`; the
            // simpler "prev itself open" approximation captures the
            // load-bearing case for loop-state-deps and avoids the
            // multi-hop chain walk on the hot path.
            // Kernel `force_exact = loop_entry && loop_entry->branches > 0`
            // (verifier.c L19175): walk prev's loop_entry chain to its
            // outermost loop header, then check whether THAT header is
            // still on the DFS path. The simpler `prev.branches > 0`
            // misses cases where prev itself has finished but is part of
            // a still-open enclosing SCC (e.g. inner-loop body state in
            // loop_state_deps2). We also keep `prev.branches > 0` as a
            // direct trigger: prev itself open ⇒ enclosing loop open.
            let force_exact = prev.branches > 0
                || prev
                    .cache_id
                    .and_then(|cid| env.get_loop_entry(cid))
                    .and_then(|lcid| env.cache_loc_by_id.get(&lcid).copied())
                    .and_then(|(lpc, lidx)| {
                        env.explored_states
                            .get(&lpc)
                            .and_then(|v| v.get(lidx))
                            .map(|s| s.branches > 0)
                    })
                    .unwrap_or(false);
            match state_subsumed_by(state, prev, live_regs, frame_live_slots, config, force_exact) {
                Ok(()) => {
                    h = Some(i);
                    break;
                }
                Err(reason) => {
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
            env.propagate_precision(state, &prev);
            // SCC: at a force_exact hit, propagate prev's loop_entry to
            // cur (verifier.c L19178). cur is about to be pruned and
            // complete_dfs_branch will walk up; carrying the loop_entry
            // lets the propagation reach the parent chain. We also seed
            // from prev's cache_id when prev itself is the entry.
            if prev.branches > 0 {
                let le = prev
                    .cache_id
                    .and_then(|cid| env.get_loop_entry(cid))
                    .or(prev.cache_id);
                if let Some(lcid) = le {
                    env.update_loop_entry(state, lcid);
                }
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
    if let Some(prev_states) = env.explored_states.get(&pc) {
        for (i, prev) in prev_states.iter().enumerate() {
            // Kernel children_unsafe (bcf_refine, verifier.c:24580-81):
            // a path-unreachable refinement marked this cached ancestor
            // not-prune-safe. Don't let it subsume a later arrival.
            if prev.children_unsafe {
                continue;
            }
            // Kernel `force_exact = loop_entry && loop_entry->branches > 0`
            // (verifier.c L19175): walk prev's loop_entry chain to its
            // outermost loop header, then check whether THAT header is
            // still on the DFS path. The simpler `prev.branches > 0`
            // misses cases where prev itself has finished but is part of
            // a still-open enclosing SCC (e.g. inner-loop body state in
            // loop_state_deps2). We also keep `prev.branches > 0` as a
            // direct trigger: prev itself open ⇒ enclosing loop open.
            let force_exact = prev.branches > 0
                || prev
                    .cache_id
                    .and_then(|cid| env.get_loop_entry(cid))
                    .and_then(|lcid| env.cache_loc_by_id.get(&lcid).copied())
                    .and_then(|(lpc, lidx)| {
                        env.explored_states
                            .get(&lpc)
                            .and_then(|v| v.get(lidx))
                            .map(|s| s.branches > 0)
                    })
                    .unwrap_or(false);
            match state_subsumed_by(state, prev, live_regs, frame_live_slots, config, force_exact) {
                Ok(()) => {
                    hit_idx = Some(i);
                    break;
                }
                Err(reason) => {
                    miss_idxs.push(i);
                    miss_reasons.push(reason);
                }
            }
        }
    }
    if let Some(idx) = hit_idx {
        record_pruning_hit(env, pc, idx);
        // Kernel-aligned propagate_precision (per-path lineage walk).
        if let Some(prev) = env.explored_states.get(&pc).and_then(|v| v.get(idx)).cloned() {
            env.propagate_precision(state, &prev);
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

    if std::env::var("ZOVIA_NO_PRUNE").is_ok() {
        return false;
    }

    env.pruning_stats.should_prune_calls += 1;

    if !is_prune_point(env, pc) {
        env.pruning_stats.not_prune_point += 1;
        return false;
    }

    let is_on_path = state
        .history_idx
        .map(|idx| env.history.is_on_path(idx, pc))
        .unwrap_or(false);

    let in_loop = is_at_loop_point(env, state, pc, prog);

    // Re-entry to a PC from a different depth (e.g. repeated call in a loop).
    // Must continue to reach the actual loop back-edge.
    if is_on_path && !in_loop {
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
    let nframes = state.frames.depth();
    let frame_live_slots: Vec<Option<HashSet<i16>>> = (0..nframes)
        .map(|i| {
            let fpc = if i + 1 == nframes {
                pc
            } else {
                state
                    .frames
                    .get(crate::analysis::machine::frame_stack::FrameLevel::from_index(i + 1))
                    .return_pc
            };
            env.insn_aux_data.get(fpc).map(|a| a.live_slots.clone())
        })
        .collect();

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
            if prev.may_goto_depth != state.may_goto_depth {
                continue;
            }
            if iter_active_depths_differ(prev, state) {
                continue;
            }
            if state_exact_equal(prev, state) {
                env.fail(crate::analysis::machine::error::VerificationError::InfiniteLoopDetected {
                    pc,
                });
                return true;
            }
        }
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

    let mut to_evict: Vec<usize> = Vec::new();
    if let Some(metrics) = env.state_metrics.get_mut(&pc) {
        for &i in miss_idxs {
            if let Some(m) = metrics.get_mut(i) {
                m.miss_cnt = m.miss_cnt.saturating_add(1);
                // Kernel formula (verifier.c L19222):
                //   n = is_force_checkpoint && sl->state.branches > 0 ? 64 : 3
                // We don't track `branches`. Approximate via `hit_cnt`:
                // cached states that have been hit at least once are
                // "proven useful"; keep them longer (n=64 at force-
                // checkpoint pcs). Unhit states use the smaller n,
                // matching the kernel's `branches == 0` fast-evict.
                // Non-force-checkpoint pcs use a slightly raised n=8
                // (vs kernel's n=3) because we always increment miss_cnt
                // — kernel gates that on the `add_new_state` heuristic
                // (verifier.c L19141-L19144) which we don't model.
                let n: u32 = if force {
                    if m.hit_cnt > 0 { 64 } else { 3 }
                } else {
                    8
                };
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
    if let Some(states) = env.explored_states.get_mut(&pc) {
        for &i in &to_evict {
            if i < states.len() {
                states.remove(i);
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
            if let Some(slot) = stack.slots.get_mut(&off) {
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
