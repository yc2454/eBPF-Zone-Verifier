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
use crate::domains::tnum::Tnum;
use subsumption::state_subsumed_by;
use widening::{
    apply_loop_bound, apply_slot_loop_bound, apply_widening, body_feeds_other_live_reg_from,
    body_uses_reg_only_in_branches, check_loop_convergence, CounterDirection, dbm_diverging_regs,
    demote_body_written_scalar_slots, detect_loop_bound, detect_slot_counter,
    find_counter_fed_regs, is_at_loop_point, is_prune_point, is_pure_accumulator,
    loop_body_implied_bound, loop_body_tests_reg, loop_has_conditional_exit, loop_has_if_exit,
    precise_domain_diverging_regs, singleton_strict_direction,
};

/// Handle pruning decision at a loop point.
/// Returns Some(true) to prune, Some(false) to continue, None if no previous states.
fn handle_loop_pruning(
    env: &mut VerifierEnv,
    state: &mut State,
    pc: usize,
    prog: &Program,
    live_regs: &HashSet<Reg>,
    live_slots: &HashSet<i16>,
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

    // Stack-spilled counter widening: covers `volatile __u64 i` patterns
    // (loop3::while_true) where the counter lives entirely on the stack
    // and never gets a persistent register at the loop top. The detector
    // requires a load-add-store triple targeting the same slot —
    // structurally distinct from the register-only oscillating /
    // constant counterexamples (`infinite_loop_three_jump_trick` etc).
    if let Some(slot_info) = detect_slot_counter(env, state, pc, prog) {
        apply_slot_loop_bound(state, slot_info);
        demote_body_written_scalar_slots(env, state, pc, prog, slot_info.slot_offset);
    }

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
            match state_subsumed_by(state, prev, live_regs, live_slots, config) {
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
    // Domain-only divergence at a back-edge whose diverging precise
    // scalars are loop counters with body-implied bounds. For each
    // diverging reg we check independently:
    //   - it has a body-resident `If reg cmp imm` branch (gives the
    //     widening cap),
    //   - the most-recent cached state vs arrival shows
    //     singleton-precise + strict positive progress
    //     (`old_min == old_max`, `cur_min == cur_max`, `cur_min > old_min`),
    //   - it is not linked via `scalar_ids` to another live reg
    //     (linkage signals the reg is an alias for a downstream-needed
    //     value; widening it drops the sibling's bound).
    //   - the SAME set of regs diverges across every cached state
    //     (different cache slots agreeing on which regs are the
    //     counters).
    //
    // This `for(i=0; i<N; i++ [, j+=K])` pattern matches:
    //   - test_bpf_ma macro expansion (single `i` counter),
    //   - bloom_filter_bench (`for(i=0; i<1024; i++, index += value_size)`,
    //     two precise diverging counters per iter).
    //
    // Filters out:
    //   - load-bearing precise regs that aren't counters (would FR
    //     `bpf_iter_task_stack::dump_task_stack`) — the singleton +
    //     scalar_id-link gates catch them,
    //   - oscillating counters in genuinely infinite loops with a
    //     bound-shaped exit branch (`infinite_loop_three_jump_trick`,
    //     where `r0 = (r0+1) & 1` joins to `r0 ∈ [0,1]` non-singleton).
    //
    // Critically this does NOT extend `detect_loop_bound`, which would
    // make `apply_loop_bound` set tnum=UNKNOWN unconditionally and
    // unsoundly subsume infinite-loop tests whose multi-branch body has
    // a per-branch comparison shaped like a bound.
    // (counter_widen_set, demote_set): counters to widen with their
    // bound, plus non-counter precise diverging regs whose precision
    // mark we can safely drop on the live state (kernel rule
    // `!precise → accept` will then cover them on subsumption against
    // the cached widened state). Both empty means we don't fire.
    let (counter_widen_set, demote_set): (Vec<(Reg, i64)>, Vec<Reg>) = if !miss_reasons
        .is_empty()
        && miss_reasons
            .iter()
            .all(|r| *r == SubsumptionMissReason::Domain)
    {
        env.explored_states.get(&pc).cloned().map(|prev_states| {
            if prev_states.len() < 4 {
                return (Vec::new(), Vec::new());
            }
            let first_set: Vec<Reg> = precise_domain_diverging_regs(
                &state.domain,
                &prev_states[0].domain,
                live_regs,
                &prev_states[0].precise_regs,
            );
            if first_set.is_empty() {
                return (Vec::new(), Vec::new());
            }
            // Every cached state must produce the SAME diverging set.
            let same_set_everywhere = prev_states.iter().all(|prev| {
                let s = precise_domain_diverging_regs(
                    &state.domain,
                    &prev.domain,
                    live_regs,
                    &prev.precise_regs,
                );
                s == first_set
            });
            if !same_set_everywhere {
                return (Vec::new(), Vec::new());
            }
            // Additionally collect non-precise live regs whose DBM
            // cells advance — they block `zone_subsumed_by` even when
            // their precision marks are absent. Same-set requirement
            // applies. Pattern from `test_parse_tcp_hdr_opt_dynptr`'s
            // R6 (byte_offset accumulator).
            let dbm_extra: Vec<Reg> = {
                let first_dbm = dbm_diverging_regs(
                    &state.domain, &prev_states[0].domain, live_regs);
                let same_dbm = prev_states.iter().all(|prev| {
                    dbm_diverging_regs(&state.domain, &prev.domain, live_regs) == first_dbm
                });
                if same_dbm {
                    first_dbm
                        .into_iter()
                        .filter(|r| !first_set.contains(r))
                        .collect()
                } else {
                    Vec::new()
                }
            };
            let last = prev_states.last().unwrap();
            let mut bounded: Vec<(Reg, i64)> = Vec::new();
            let mut demote: Vec<Reg> = Vec::new();
            // Process the non-precise DBM-diverging regs first: they
            // can ONLY be demoted (no counter widening since they're
            // not precise so wouldn't enter the singleton-direction
            // logic meaningfully, and we want to leave their value
            // tracking alone if branch-only). Demotion here clears
            // their DBM cells so `zone_subsumed_by` stops blocking.
            for &r in &dbm_extra {
                if state.scalar_id(r).is_none()
                    && body_uses_reg_only_in_branches(env, state, pc, prog, r, live_regs)
                {
                    demote.push(r);
                } else {
                    return (Vec::new(), Vec::new());
                }
            }
            for &r in &first_set {
                // Try to classify as counter first. Counter pattern:
                //   - no scalar_id link,
                //   - body has `If r cmp imm` test,
                //   - doesn't feed an accumulator (`dst := dst OP r`),
                //   - singleton-precise strict direction on last slot,
                //   - has a cap (asc: body bound; desc: max observed).
                // The counter widening branch unconditionally calls
                // `assume_ge_imm(r, 0)` and sets tnum to `[0, upper]`,
                // which is unsound when the reg's interval crosses
                // zero (e.g. the signed-boundary tests in
                // verifier_bounds.c::crossing_*_signed_boundary_*
                // operate in the negative half of i64). Gate counter
                // classification on `cur_lo >= 0` so the unsound apply
                // step never fires for these. Mirrors the same gate
                // in `detect_loop_bound` (`if lo >= 0`).
                let (cur_lo, _) = state.domain.get_interval(r);
                let basic_counter_shape = cur_lo >= 0
                    && state.scalar_id(r).is_none()
                    && loop_body_tests_reg(env, state, pc, prog, r);
                let feeds_others = body_feeds_other_live_reg_from(env, state, pc, prog, r, live_regs);
                // Extended counter shape: counter feeds one or more live
                // accumulators (`A := A OP counter` or `A := counter OP B`).
                // Allowed when every fed-target is a "pure accumulator"
                // (no memory base / branch use, only arithmetic
                // self-feedback or cross-feed within the accumulator
                // closure). Loop1 pattern: inner counter `i` (R3) feeds
                // `sum` (R0/R5) which is itself only used in further
                // accumulation and the function's exit value.
                //
                // Soundness sketch: widening counter to [0, K] sets the
                // cached counter range so subsequent iters subsume on it.
                // The fed accumulators get their precision marks dropped
                // (kernel `!precise → accept` rule); their values stay
                // imprecise across iters, but since they're not used as
                // memory bases or branch operands their imprecision is
                // dispensable for verifying memory safety / control flow.
                // Restrict the accumulator-aware extension to ASCENDING
                // counters. Descending shapes (`r -= 1; if r != 0`)
                // worked pre-extension by allowing the accumulator gate
                // to bail (no widening); allowing the extension here
                // regressed `verifier_loops1::back_jump_to_1st_insn_2`
                // because the descending widening drops r to `[0, max]`
                // including a value below the smallest singleton ever
                // observed at the loop top, and the post-`r -= 1` body
                // produces a negative r that branches under `if r != 0`
                // explosively. Ascending counters don't have this
                // issue: the widening floor `assume_ge_imm(0)` matches
                // the natural [0, k-1] range from `i++ < k` patterns.
                let dir_for_ext = singleton_strict_direction(&state.domain, &last.domain, r);
                let is_ascending = matches!(dir_for_ext, Some(CounterDirection::Ascending));
                let extended_counter_shape = if basic_counter_shape && feeds_others && is_ascending {
                    let fed = find_counter_fed_regs(env, state, pc, prog, r, live_regs);
                    // Transitively expand the candidate set: any live reg
                    // that an accumulator feeds becomes part of the
                    // closure (loop1's `R5 = R0; R0 = R0 + R5` cycle).
                    // Stop when the set stops growing or we observe a
                    // disqualifying use (memory base / branch / scalar_id
                    // link).
                    let mut closure: HashSet<Reg> = fed.iter().copied().collect();
                    closure.insert(r);
                    loop {
                        let mut grew = false;
                        let snapshot: Vec<Reg> = closure.iter().copied().collect();
                        for &a in &snapshot {
                            if a == r {
                                continue;
                            }
                            for tgt in find_counter_fed_regs(env, state, pc, prog, a, live_regs) {
                                if closure.insert(tgt) {
                                    grew = true;
                                }
                            }
                        }
                        if !grew {
                            break;
                        }
                    }
                    !fed.is_empty()
                        && closure.iter().filter(|&&a| a != r).all(|&a| {
                            state.scalar_id(a).is_none()
                                && is_pure_accumulator(env, state, pc, prog, a, &closure, live_regs)
                        })
                } else {
                    false
                };
                let is_counter_shape =
                    basic_counter_shape && (!feeds_others || extended_counter_shape);
                if extended_counter_shape {
                    // Queue the entire accumulator closure for demotion
                    // alongside counter widening below.
                    let fed = find_counter_fed_regs(env, state, pc, prog, r, live_regs);
                    let mut closure: HashSet<Reg> = fed.iter().copied().collect();
                    loop {
                        let mut grew = false;
                        let snapshot: Vec<Reg> = closure.iter().copied().collect();
                        for &a in &snapshot {
                            for tgt in find_counter_fed_regs(env, state, pc, prog, a, live_regs) {
                                if tgt != r && closure.insert(tgt) {
                                    grew = true;
                                }
                            }
                        }
                        if !grew {
                            break;
                        }
                    }
                    for a in closure {
                        if !demote.contains(&a) {
                            demote.push(a);
                        }
                    }
                }
                if is_counter_shape {
                    if let Some(dir) =
                        singleton_strict_direction(&state.domain, &last.domain, r)
                    {
                        let cap_opt: Option<i64> = match dir {
                            CounterDirection::Ascending => {
                                loop_body_implied_bound(env, state, pc, prog, r)
                            }
                            CounterDirection::Descending => {
                                let mut max_seen = state.domain.get_interval(r).1;
                                for ps in &prev_states {
                                    let (_, pm) = ps.domain.get_interval(r);
                                    if pm > max_seen {
                                        max_seen = pm;
                                    }
                                }
                                if max_seen > 0 { Some(max_seen) } else { None }
                            }
                        };
                        if let Some(cap) = cap_opt {
                            bounded.push((r, cap));
                            continue;
                        }
                    }
                }
                // Not a counter — try demotion. A precise scalar that
                // only ever drives a branch (no memory access, no
                // arithmetic feeding another reg, no helper-call
                // arg) can have its cached-side precise mark dropped:
                // the kernel `!precise → accept` rule then covers it,
                // so future arrivals subsume against the cached
                // widened state regardless of this reg's value.
                // Pattern observed in `test_parse_tcp_hdr_opt`'s R4
                // (`bytes_remaining` loaded from stack, only used in
                // `if !bytes_remaining break`).
                if state.scalar_id(r).is_none()
                    && body_uses_reg_only_in_branches(env, state, pc, prog, r, live_regs)
                {
                    demote.push(r);
                    continue;
                }
                // Neither counter nor demotable — bail.
                return (Vec::new(), Vec::new());
            }
            // At least one counter must be widening for the firing
            // to make sense. Pure demotion (no widening) was tried
            // and introduced an FA in
            // `verifier_search_pruning::short_loop1` and a regression
            // in `bpf_iter_task_stack` — without a forced-progress
            // signal, demoting precision marks alone allows
            // converging loops we shouldn't.
            if bounded.is_empty() {
                return (Vec::new(), Vec::new());
            }
            (bounded, demote)
        }).unwrap_or((Vec::new(), Vec::new()))
    } else {
        (Vec::new(), Vec::new())
    };
    let domain_widen_loop_counter_only = !counter_widen_set.is_empty();
    if (config.use_widening
        || force_widen_for_may_goto
        || only_tnum_misses
        || domain_widen_loop_counter_only)
        && prev_states_len > 0
    {
        // Re-fetch the last cached state for widening (after eviction
        // it may have shifted; take the last surviving one).
        if let Some(prev_states) = env.explored_states.get(&pc)
            && let Some(old) = prev_states.last().cloned().as_ref()
        {
            if !counter_widen_set.is_empty() {
                // Targeted per-counter widening + non-counter demotion.
                for (counter, upper) in &counter_widen_set {
                    state.domain.forget(*counter);
                    state.domain.assume_le_imm(*counter, *upper);
                    state.domain.assume_ge_imm(*counter, 0);
                    state.set_tnum(*counter, Tnum::from_range(0, *upper as u64));
                }
                // Demote precision marks AND forget DBM cells for
                // non-counter precise diverging regs classified as
                // branch-only. Two complementary effects:
                //
                //   1. `precise_regs.remove` drops the kernel-rule
                //      `precise → range_within` check on this reg
                //      (`!precise → accept` covers it). Mirrors lazy
                //      mark_chain_precision.
                //   2. `domain.forget` clears the reg's DBM cells.
                //      Without this, `zone_subsumed_by`'s live-reg
                //      pair check (`old_dbm.get(r, a) >= cur_dbm.get`)
                //      keeps blocking subsumption even with the
                //      precise mark gone, because DBM cells are
                //      checked unconditionally for live regs.
                //
                // Pattern from `test_parse_tcp_hdr_opt`'s R4
                // (byte_offset accumulator) — it's not a counter
                // (interval grows each iter, not singleton) but only
                // drives an `If R4 cmp imm` body branch, so the
                // precision is dispensable for verification.
                for r in &demote_set {
                    state.precise_regs.remove(r);
                    state.domain.forget(*r);
                }
            } else {
                apply_widening(state, old, live_regs, loop_bound);
            }
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
    live_slots: &HashSet<i16>,
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
            match state_subsumed_by(state, prev, live_regs, live_slots, config) {
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
    let live_slots = env.insn_aux_data[pc].live_slots.clone();

    // may_goto-specific RANGE_WITHIN prune class.
    if pc < prog.instrs.len()
        && matches!(prog.instrs[pc], Instr::If { .. } | Instr::MayGoto { .. })
        && let Some(prev_states) = env.explored_states.get(&pc)
    {
        let is_may_goto = matches!(prog.instrs[pc], Instr::MayGoto { .. });
        if is_may_goto
            && may_goto_range_within_prune(state, prev_states, &live_regs, &live_slots, config)
        {
            env.pruning_stats.may_goto_range_within_hits += 1;
            return true;
        }
    }

    let pruned = if in_loop {
        handle_loop_pruning(env, state, pc, prog, &live_regs, &live_slots, config)
    } else {
        handle_standard_pruning(env, state, pc, &live_regs, &live_slots, config)
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
    live_slots: &HashSet<i16>,
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
        if state_subsumed_by(&relaxed, prev, live_regs, live_slots, config).is_ok() {
            return true;
        }
    }
    false
}
