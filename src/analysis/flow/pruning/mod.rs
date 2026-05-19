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
use subsumption::state_subsumed_by;
use widening::{
    apply_loop_bound, apply_widening, check_loop_convergence, detect_loop_bound, is_at_loop_point,
    is_prune_point, loop_has_conditional_exit, loop_has_if_exit,
};

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

    let loop_bound = detect_loop_bound(env, state, pc, prog);

    // Apply bound before subsumption check
    apply_loop_bound(state, loop_bound);

    // Walk prev_states once, recording the first hit (if any) and all
    // walked-past indices. We hold the borrow only inside this scope so
    // the metrics-update at the end can take `&mut env` cleanly.
    let (hit_idx, miss_idxs, miss_reasons, prev_first_budget, prev_last_budget, prev_states_len): (
        Option<usize>,
        Vec<usize>,
        Vec<SubsumptionMissReason>,
        Option<u32>,
        Option<u32>,
        usize,
    ) = if let Some(prev_states) = env.explored_states.get(&pc) {
        let mut h = None;
        let mut m: Vec<usize> = Vec::new();
        let mut r: Vec<SubsumptionMissReason> = Vec::new();
        // Branchy loop tops can hold multiple cached states; match the
        // first that subsumes (kernel `is_state_visited` walks the
        // explored_state list, verifier.c v6.15 ~L19018).
        for (i, prev) in prev_states.iter().enumerate() {
            // Kernel children_unsafe (bcf_refine, verifier.c:24580-81).
            if prev.children_unsafe {
                continue;
            }
            match state_subsumed_by(state, prev, live_regs, frame_live_slots, config) {
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
        let f = prev_states.first().map(|s| s.goto_budget);
        let l = prev_states.last().map(|s| s.goto_budget);
        (h, m, r, f, l, prev_states.len())
    } else {
        env.pruning_stats.loop_walks_no_prev += 1;
        return false;
    };

    if let Some(idx) = hit_idx {
        env.pruning_stats.loop_walks_hit += 1;
        // Record hit BEFORE check_loop_convergence — eviction won't
        // touch the just-hit entry, but cleaner ordering.
        record_pruning_hit(env, pc, idx);
        // Kernel-aligned propagate_precision (verifier.c v6.15 L18828):
        // pull cached's precise-mark set into cur's parent-cache lineage
        // so the path's continuation tracks the same precision contract.
        if let Some(prev) = env.explored_states.get(&pc).and_then(|v| v.get(idx)).cloned() {
            env.propagate_precision(state, &prev);
        }
        // For convergence we still need the full prev_states list.
        let prev_states = env
            .explored_states
            .get(&pc)
            .cloned()
            .unwrap_or_default();
        if check_loop_convergence(
            env,
            state,
            pc,
            prog,
            &prev_states,
            live_regs,
            loop_bound,
            config,
        ) {
            env.pruning_stats.loop_walks_pruned_via_convergence += 1;
            return true;
        }
        // Subsumed but convergence not yet provable (widening not
        // effective on live regs OR exit path not yet explored). Apply
        // widening against the cached state we just hit so the next
        // iteration's cached entry covers a strictly wider scalar
        // range than this one — eventually widening_was_effective
        // fires and the loop converges. Without this, tight scalar
        // loops where every iteration subsumes via `!precise → accept`
        // (e.g. `verifier_bounds.c::crossing_64_bit_signed_boundary_2`)
        // never converge: subsumption succeeds but widening only fires
        // on misses, so the cached state never widens.
        if let Some(prev_states) = env.explored_states.get(&pc)
            && let Some(old) = prev_states.get(idx).cloned().as_ref()
        {
            apply_widening(state, old, live_regs, loop_bound);
        }
        return false;
    }

    env.pruning_stats.loop_walks_miss += 1;
    // Not subsumed: record misses + maybe evict, then apply widening.
    record_pruning_misses(env, pc, &miss_idxs);
    record_subsumption_miss_reasons(env, pc, &miss_reasons);

    let only_may_goto_exit = !loop_has_if_exit(env, state, pc, prog);
    let may_goto_progress = prev_first_budget
        .zip(prev_last_budget)
        .map(|(f, l)| f > l)
        .unwrap_or(false);
    let force_widen_for_may_goto =
        only_may_goto_exit && loop_bound.is_none() && may_goto_progress;
    // Tnum-only divergence at a back-edge: a counter scalar incrementing
    // each iteration produces tnum-precise values that never subsume,
    // even though the *interval* domain happily widens. Apply tnum
    // widening here so non-iter / non-may_goto goto-loops with scalar
    // counters can converge — without affecting tests that miss for
    // other reasons (stack/types/domain). Pattern observed in
    // verifier_bounds.c::crossing_64_bit_signed_boundary_2 (counter r0
    // incrementing in [S64_MIN, ...] until SLt branch exits).
    let only_tnum_misses = !miss_reasons.is_empty()
        && miss_reasons
            .iter()
            .all(|r| *r == SubsumptionMissReason::Tnum);
    if (config.use_widening || force_widen_for_may_goto || only_tnum_misses)
        && prev_states_len > 0
    {
        // Re-fetch the last cached state for widening (after eviction
        // it may have shifted; take the last surviving one).
        if let Some(prev_states) = env.explored_states.get(&pc)
            && let Some(old) = prev_states.last().cloned().as_ref()
        {
            apply_widening(state, old, live_regs, loop_bound);
        }
    }

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
            match state_subsumed_by(state, prev, live_regs, frame_live_slots, config) {
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
        if state_subsumed_by(&relaxed, prev, live_regs, frame_live_slots, config).is_ok() {
            return true;
        }
    }
    false
}
