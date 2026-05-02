// src/analysis/pruning.rs

use std::collections::HashSet;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Instr, Operand, Program};
use crate::common::config::VerifierConfig;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;

/// Check if the loop body contains a conditional branch (If instruction),
/// which indicates the loop has a potential exit path.
/// Only considers instructions at the same call depth as the loop head.
/// Does this loop have at least one `Instr::If` exit? Used to distinguish
/// "natural" loops with comparison-based exits (where domain refinement on
/// the exit branch handles termination) from may_goto-only loops where the
/// runtime budget is the only termination guarantee.
fn loop_has_if_exit(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    if let Some(idx) = state.history_idx {
        let body_pcs = env.history.loop_body_pcs(idx, pc, Some(state.num_frames()));
        for body_pc in body_pcs {
            if body_pc < prog.instrs.len()
                && matches!(prog.instrs[body_pc], Instr::If { .. })
            {
                return true;
            }
        }
    }
    if pc < prog.instrs.len() && matches!(prog.instrs[pc], Instr::If { .. }) {
        return true;
    }
    false
}

fn loop_has_conditional_exit(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    if let Some(idx) = state.history_idx {
        // Only check PCs at the same frame depth (excludes callee instructions)
        let body_pcs = env.history.loop_body_pcs(idx, pc, Some(state.num_frames()));
        for body_pc in body_pcs {
            if body_pc < prog.instrs.len()
                && matches!(
                    prog.instrs[body_pc],
                    Instr::If { .. } | Instr::MayGoto { .. }
                )
            {
                return true;
            }
        }
    }
    // Also check the loop head itself. `MayGoto` is a budget-bounded
    // conditional exit (BPF_JCOND v6.8): the kernel inlines a hidden
    // counter check that eventually short-circuits the back-edge, so the
    // exit is guaranteed to be reachable.
    if pc < prog.instrs.len()
        && matches!(
            prog.instrs[pc],
            Instr::If { .. } | Instr::MayGoto { .. }
        )
    {
        return true;
    }
    false
}

/// Extract loop bound from a `!= K` condition.
///
/// This is called when we detect a back-edge to infer an upper bound for the loop.
/// For bounded loops (e.g. `for (i = 0; i < 40; i++)`), the compiler emits:
///   `if r != 40 goto loop_head`
///
/// Since the loop continues only when `r != K`, an incrementing counter yields `r < K`.
/// There are two back-edge detection cases handled here:
/// 1. We're at the branch instruction itself (`if r1 != 40 goto 20`).
/// 2. We're at the loop head and arrived via a backward jump (`goto 20` where PC=20).
/// Returns `(reg, upper_bound)` if a bounded loop pattern is detected.
fn detect_loop_bound(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
) -> Option<(Reg, i64)> {
    // Case 1: Check if the CURRENT instruction is a `!= K` branch (back-edge at branch site)
    if current_pc < prog.instrs.len()
        && let Instr::If {
            op: CmpOp::Ne,
            left,
            right: Operand::Imm(k),
            ..
        } = &prog.instrs[current_pc]
    {
        let (lo, _hi) = state.domain.get_interval(*left);
        if lo >= 0 && *k > 0 {
            return Some((*left, *k - 1));
        }
    }

    // Case 2: Check if we arrived via a `!= K` branch (back-edge at loop head)
    let history_idx = state.history_idx?;
    let branch_step = env.history.get(history_idx)?;
    let branch_pc = branch_step.pc;

    if branch_pc < prog.instrs.len()
        && let Instr::If {
            op: CmpOp::Ne,
            left,
            right: Operand::Imm(k),
            target,
            ..
        } = &prog.instrs[branch_pc]
        && *target == current_pc
    {
        let (lo, _hi) = state.domain.get_interval(*left);
        if lo >= 0 && *k > 0 {
            return Some((*left, *k - 1));
        }
    }

    None
}

/// Check if any conditional branch in the loop body has had its exit path
/// actually explored (i.e., the exit PC has explored states). This detects
/// cases where a conditional exit exists syntactically but is never feasible.
///
/// Only considers instructions at the same call depth as the loop head,
/// so BPF-to-BPF calls within the loop don't pollute the loop body set.
fn loop_exit_was_explored(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    // Collect loop body PCs at the same frame depth (excludes callee instructions)
    let frame_depth = state.num_frames();
    let mut body_pc_set: HashSet<usize> = HashSet::new();
    body_pc_set.insert(pc); // loop head
    if let Some(idx) = state.history_idx {
        for body_pc in env.history.loop_body_pcs(idx, pc, Some(frame_depth)) {
            body_pc_set.insert(body_pc);
        }
    }

    // For each conditional-exit instruction in the loop body (If or
    // MayGoto), check if its exit successor (the one that leaves the
    // loop) has been explored. MayGoto behaves the same way for this
    // analysis: budget exhaustion guarantees one of its successors is
    // an exit.
    for &body_pc in &body_pc_set {
        if body_pc >= prog.instrs.len() {
            continue;
        }
        let target_opt = match &prog.instrs[body_pc] {
            Instr::If { target, .. } => Some(*target),
            Instr::MayGoto { target } => Some(*target),
            _ => None,
        };
        if let Some(target) = target_opt {
            let fall_through = body_pc + 1;
            // Check if fall-through exits the loop
            if !body_pc_set.contains(&fall_through)
                && env.explored_states.contains_key(&fall_through)
            {
                return true;
            }
            // Check if target exits the loop
            if !body_pc_set.contains(&target) && env.explored_states.contains_key(&target) {
                return true;
            }
        }
    }
    false
}

/// Check if current PC is a designated prune point.
fn is_prune_point(env: &VerifierEnv, pc: usize) -> bool {
    env.insn_aux_data
        .get(pc)
        .map(|aux| aux.prune_point)
        .unwrap_or(false)
}

/// Check if the current instruction is a backward-jumping branch.
fn is_backward_branch(pc: usize, prog: &Program) -> bool {
    if pc >= prog.instrs.len() {
        return false;
    }
    match &prog.instrs[pc] {
        Instr::If { target, .. } | Instr::Jmp { target } => *target < pc,
        _ => false,
    }
}

/// Check if we arrived at current PC via a backward jump (loop head detection).
fn arrived_via_back_edge(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    state
        .history_idx
        .and_then(|idx| {
            let prev_step = env.history.get(idx)?;
            let prev_pc = prev_step.pc;
            if prev_pc >= prog.instrs.len() {
                return Some(false);
            }
            match &prog.instrs[prev_pc] {
                Instr::If { target, .. } | Instr::Jmp { target }
                    if *target == pc && prev_pc > pc =>
                {
                    Some(true)
                }
                _ => Some(false),
            }
        })
        .unwrap_or(false)
}

/// Determine if we're at an actual loop point (back-edge).
///
/// A loop point is either:
/// 1. A backward-jumping branch (source of back-edge): If/Jmp with target < pc
/// 2. The target of a backward jump (loop head): arrived here via a backward jump
///
/// We require that the history confirms this is a back-edge at the current call depth,
/// not just that we've visited this PC before on some other path.
fn is_at_loop_point(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    // History must confirm this is a back-edge at current call depth
    let is_back_edge_pc = state
        .history_idx
        .map(|idx| env.history.is_back_edge(idx, pc, state.num_frames()))
        .unwrap_or(false);

    is_back_edge_pc && (is_backward_branch(pc, prog) || arrived_via_back_edge(env, state, pc, prog))
}

/// Apply loop bound constraints to the state.
/// Returns true if bounds were applied.
fn apply_loop_bound(state: &mut State, loop_bound: Option<(Reg, i64)>) -> bool {
    if let Some((reg, upper_bound)) = loop_bound {
        let (cur_lo, _) = state.domain.get_interval(reg);
        if cur_lo <= upper_bound {
            state.domain.assume_le_imm(reg, upper_bound);
            state.domain.assume_ge_imm(reg, 0);
            state.set_tnum(reg, Tnum::UNKNOWN);
            return true;
        }
    }
    false
}

/// Check if widening was effective (bounds expanded compared to first visit).
fn widening_was_effective(first: &State, last: &State, live_regs: &HashSet<Reg>) -> bool {
    live_regs.iter().any(|&r| {
        let (first_min, first_max) = first.domain.get_interval(r);
        let (last_min, last_max) = last.domain.get_interval(r);
        last_min < first_min || last_max > first_max
    })
}

/// Check if loop has converged and can be pruned.
/// Precondition: state is already subsumed by prev_states.last().
fn check_loop_convergence(
    env: &VerifierEnv,
    state: &State,
    pc: usize,
    prog: &Program,
    prev_states: &[State],
    live_regs: &HashSet<Reg>,
    loop_bound: Option<(Reg, i64)>,
    config: &VerifierConfig,
) -> bool {
    // Only converge if:
    // 1. Widening was applied (prev_states >= 2)
    // 2. Either widening was effective (live regs' bounds expanded), or
    //    the loop is may_goto-bounded (the runtime counter on its own
    //    proves termination — no scalar needs to widen). Loop body
    //    effects on live regs are still subsumption-checked by the
    //    caller; this just controls when we *trust* the subsumption to
    //    let us prune.
    // 3. Exit path exists (bounded loop or exit was explored)
    if prev_states.len() < 2 {
        return false;
    }

    let first = &prev_states[0];
    let last = prev_states.last().unwrap();

    // may_goto loops decrement `goto_budget` on every iteration; once
    // we're observably making progress on the budget the runtime is
    // guaranteed to exit, so subsumption alone is sufficient. This is
    // what `verifier_iterating_callbacks::cond_break5` needs — the
    // body's `cnt1++` doesn't widen because cnt1 isn't live across
    // the loop head, but the budget counts iterations down regardless.
    let may_goto_bounded = first.goto_budget > last.goto_budget;

    if !may_goto_bounded
        && !live_regs.is_empty()
        && !widening_was_effective(first, last, live_regs)
    {
        return false;
    }

    // Bounded loops don't need exit exploration; bound proves exit exists
    // (only if detect_bounded_loops is enabled)
    let bounded_loop_detected = config.detect_bounded_loops && loop_bound.is_some();
    bounded_loop_detected || loop_exit_was_explored(env, state, pc, prog)
}

/// Apply widening to state based on previous exploration.
fn apply_widening(
    state: &mut State,
    old: &State,
    live_regs: &HashSet<Reg>,
    loop_bound: Option<(Reg, i64)>,
) {
    // Widen numeric domain
    state.domain = old.domain.widen(&state.domain);

    // Re-apply loop bound after widening
    apply_loop_bound(state, loop_bound);

    // Widen Tnums: if changed, set to UNKNOWN for fast convergence
    for &r in live_regs {
        if old.get_tnum(r) != state.get_tnum(r) {
            state.set_tnum(r, Tnum::UNKNOWN);
        }
    }
}

/// Handle pruning decision at a loop point.
/// Returns Some(true) to prune, Some(false) to continue, None if no previous states.
fn handle_loop_pruning(
    env: &VerifierEnv,
    state: &mut State,
    pc: usize,
    prog: &Program,
    live_regs: &HashSet<Reg>,
    config: &VerifierConfig,
) -> bool {
    // Loops without conditional exits are infinite - let complexity limit catch them
    if !loop_has_conditional_exit(env, state, pc, prog) {
        return false;
    }

    let loop_bound = detect_loop_bound(env, state, pc, prog);

    // Apply bound before subsumption check
    apply_loop_bound(state, loop_bound);

    let Some(prev_states) = env.explored_states.get(&pc) else {
        return false;
    };

    // Branchy loop tops can hold multiple cached states (e.g. an
    // `iter_*_next` fork leaves both the non-null and null R0 paths
    // cached at the same pc). Match against any of them — only checking
    // `last()` would miss subsumption when the branches alternate.
    // Mirrors kernel `is_state_visited` which iterates `list_for_each`
    // over the full explored_state list (verifier.c v6.15 ~L19018).
    let any_subsumes = prev_states
        .iter()
        .any(|old| state_subsumed_by(state, old, live_regs, config));

    if let Some(old) = prev_states.last() {
        if any_subsumes {
            // Check if we can converge (widening effective + exit explored)
            if check_loop_convergence(
                env,
                state,
                pc,
                prog,
                prev_states,
                live_regs,
                loop_bound,
                config,
            ) {
                return true;
            }
            // Subsumed but conditions not met (widening not effective or no exit path)
            // Let complexity limit catch infinite loops - don't widen when already subsumed
            return false;
        }

        // Not subsumed: apply widening to accelerate convergence.
        //
        // Force-widen when the loop's ONLY conditional exit is a may_goto
        // (no `Instr::If` in the body and no static loop bound detected),
        // and the goto_budget is strictly decreasing across `prev_states`.
        // Without that, the body's per-iteration scalar mutation prevents
        // subsumption forever and we hit the complexity limit. The budget
        // decrement guarantees termination, so we can afford to lose
        // precision on scalars the static bounds machinery can't pin down.
        //
        // Bounded loops with both an `If`-style exit AND a may_goto
        // (e.g. test2's `for (i=0; i<N && can_loop; i++)`) already
        // converge via `apply_loop_bound`, so we don't force-widen there
        // — preserves the index-bound precision the array store inside
        // needs.
        let only_may_goto_exit = !loop_has_if_exit(env, state, pc, prog);
        let may_goto_progress = prev_states
            .first()
            .zip(prev_states.last())
            .map(|(f, l)| f.goto_budget > l.goto_budget)
            .unwrap_or(false);
        let force_widen_for_may_goto =
            only_may_goto_exit && loop_bound.is_none() && may_goto_progress;
        if config.use_widening || force_widen_for_may_goto {
            apply_widening(state, old, live_regs, loop_bound);
        }
    }

    false
}

/// Handle standard (non-loop) subsumption check.
fn handle_standard_pruning(
    env: &VerifierEnv,
    state: &State,
    pc: usize,
    live_regs: &HashSet<Reg>,
    config: &VerifierConfig,
) -> bool {
    if let Some(prev_states) = env.explored_states.get(&pc) {
        for prev in prev_states {
            if state_subsumed_by(state, prev, live_regs, config) {
                return true;
            }
        }
    }
    false
}

/// Check if we should prune this state (already covered by a previous exploration).
/// For loop heads with conditional exits, applies widening to accelerate convergence.
pub fn should_prune(
    env: &VerifierEnv,
    state: &mut State,
    config: &VerifierConfig,
    prog: &Program,
) -> bool {
    let pc = state.pc;

    if !is_prune_point(env, pc) {
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
        return false;
    }

    let live_regs = &env.insn_aux_data[pc].live_regs;

    // Bucket F-D: may_goto-specific RANGE_WITHIN prune class.
    // Mirrors kernel `is_state_visited` (verifier.c v6.15 ~L19102):
    //   if (is_may_goto_insn_at(env, insn_idx)) {
    //       if (sl->state.may_goto_depth != cur->may_goto_depth &&
    //           states_equal(env, &sl->state, cur, RANGE_WITHIN)) {
    //           goto hit;
    //       }
    //   }
    // RANGE_WITHIN: scalar precision marks are dropped — bounds/tnum
    // containment is enough. Combined with the depth-bump in the
    // `Instr::MayGoto` transfer, this lets bounded-but-precision-tight
    // loops (cond_break1/2/3) converge: the body precision-marks `i`
    // at the `arr[i]` access, but successive may_goto visits share a
    // RANGE_WITHIN view of `i` modulo its widened range.
    if pc < prog.instrs.len()
        && matches!(prog.instrs[pc], Instr::If { .. } | Instr::MayGoto { .. })
        && let Some(prev_states) = env.explored_states.get(&pc)
    {
        let is_may_goto = matches!(prog.instrs[pc], Instr::MayGoto { .. });
        if is_may_goto && may_goto_range_within_prune(state, prev_states, live_regs, config) {
            return true;
        }
    }

    if in_loop {
        handle_loop_pruning(env, state, pc, prog, live_regs, config)
    } else {
        handle_standard_pruning(env, state, pc, live_regs, config)
    }
}

/// Bucket F-D: RANGE_WITHIN prune class for may_goto pcs.
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
        if state_subsumed_by(&relaxed, prev, live_regs, config) {
            return true;
        }
    }
    false
}

/// Callee-saved registers that persist across calls and affect
/// post-return control flow. Must be checked in caller frames.
fn callee_saved_regs() -> HashSet<Reg> {
    [Reg::R6, Reg::R7, Reg::R8, Reg::R9].into_iter().collect()
}

/// Check if `cur` is subsumed by `old` (old covers all behaviors of cur).
fn state_subsumed_by(
    cur: &State,
    old: &State,
    live_regs: &HashSet<Reg>,
    config: &VerifierConfig,
) -> bool {
    // Check current frame
    if config.skip_dbm_check {
        if !(types_subsumed_by(&cur.types, &old.types, live_regs)
            && stack_subsumed_by(cur, old)
            && tnum_subsumed_by(cur, old, live_regs))
        {
            return false;
        }
    } else if !(types_subsumed_by(&cur.types, &old.types, live_regs)
        && domain_subsumed_by(&cur.domain, &old.domain, live_regs, &old.precise_regs)
        && stack_subsumed_by(cur, old)
        && tnum_subsumed_by(cur, old, live_regs))
    {
        return false;
    }

    // Cluster: regsafe scalar-id check.
    // If two live registers share a scalar_id in `old` (so a future
    // refinement on one will propagate to the other along the cached
    // continuation), `cur` must also have them linked. Otherwise the
    // cur-state's continuation would refine them independently — pruning
    // it against `old` hides paths where the unlinked register stays
    // unbounded. Mirrors upstream `check_ids` in `regsafe`.
    if !scalar_id_links_subsumed_by(cur, old, live_regs) {
        return false;
    }

    // Active-lock identity. When `old.active_lock` names a specific
    // map_value (`ptr_id`), every live register that *currently* holds
    // that map_value in `old` must still hold the same map_value in
    // `cur` — otherwise a future `bpf_spin_unlock` along the cached
    // continuation through such a register would mismatch the lock in
    // `cur`. This caught the FALSE_ACCEPT in
    // `verifier_spin_lock::reg_id_for_map_value`, where one path
    // reassigns the lock-holding register to a different map_value.
    if !active_lock_subsumed_by(cur, old, live_regs) {
        return false;
    }

    // W3.1c: `old` must have at least as much may_goto budget remaining as
    // `cur`, otherwise pruning would let `cur` continue under behaviours
    // `old` never explored (old already exhausted the budget on a path cur
    // hasn't yet reached). Monotone: budget only ever decreases, so once
    // cur's future iterations are covered by an old state with a larger or
    // equal counter, pruning is sound.
    if old.goto_budget < cur.goto_budget {
        return false;
    }

    // Active refcount-tracked acquisitions (dynptr / sock / cpumask /
    // kptr / ...) must be a subset in `cur` of those held by `old`. If
    // `cur` carries an active ref that `old` doesn't, pruning would
    // hide a leak: the cached continuation from `old` already proved
    // there's no leaking exit, but along that continuation cur's extra
    // ref never gets released — exit leak-check would catch it on cur
    // but not on old. Caught `dynptr_fail::ringbuf_missing_release2`,
    // where one branch releases both ptr1+ptr2 and the other only ptr1.
    if !cur.active_refs.is_subset(&old.active_refs) {
        return false;
    }

    // Check caller frames: callee-saved registers (r6-r9) persist across
    // calls and determine post-return control flow. Without this check,
    // two states that differ only in caller-frame r6-r9 values get pruned
    // against each other, hiding bugs that manifest after return.
    let saved = callee_saved_regs();
    for (cur_frame, old_frame) in cur.frames.iter().zip(old.frames.iter()) {
        if !types_subsumed_by(&cur_frame.caller_types, &old_frame.caller_types, &saved) {
            return false;
        }
        if !config.skip_dbm_check
            && !domain_subsumed_by(
                &cur_frame.caller_domain,
                &old_frame.caller_domain,
                &saved,
                &HashSet::new(),
            )
        {
            return false;
        }
        if !caller_tnum_subsumed_by(cur_frame, old_frame, &saved) {
            return false;
        }
    }

    true
}

/// Linkage class for a register, used by `scalar_id_links_subsumed_by`.
///
/// Two registers belong to the same equivalence class when a future
/// refinement (e.g. null-check, range narrowing) on one will propagate
/// to the other along the kernel verifier's id-tracking. This covers:
///   - scalars sharing a `scalar_id`
///   - id-bearing nullable pointer types (`PtrToMapValueOrNull`,
///     `PtrToBtfIdOrNull`, `PtrToAllocMemOrNull`) sharing an id — null
///     refinement promotes all class members to the non-null form.
///   - the non-null forms `PtrToMapValue { id, .. }`, `PtrToAllocMem { id, .. }`
///     — the id persists post-refinement and still drives propagation.
///
/// The numeric tag in `LinkageKind` keeps classes from different RegType
/// variants disjoint even when their ids collide as `u32` values.
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
enum LinkageKind {
    Scalar,
    MapValue,
    MapValueOrNull,
    BtfIdOrNull,
    AllocMem,
    AllocMemOrNull,
    /// Interval-mode packet-pointer family (kernel `reg->id`).
    /// Two registers with the same `(PacketPtr, id)` share a variable
    /// offset chain; a bounds check on one refines `range` for all.
    /// Zone mode handles this via DBM cells, not ids — the
    /// corresponding subsumption check lives in `zone_subsumed_by`.
    PacketPtr,
}

fn linkage_key(state: &State, r: Reg) -> Option<(LinkageKind, u32)> {
    use crate::analysis::machine::reg_types::RegType;
    use crate::domains::numeric::NumericDomain;
    match state.types.get(r) {
        RegType::PtrToMapValueOrNull { id, .. } => Some((LinkageKind::MapValueOrNull, id)),
        RegType::PtrToMapValue { id, .. } => Some((LinkageKind::MapValue, id)),
        RegType::PtrToBtfIdOrNull { id, .. } => Some((LinkageKind::BtfIdOrNull, id)),
        RegType::PtrToAllocMemOrNull { id, .. } => Some((LinkageKind::AllocMemOrNull, id)),
        RegType::PtrToAllocMem { id, .. } => Some((LinkageKind::AllocMem, id)),
        RegType::ScalarValue => state.scalar_id(r).map(|id| (LinkageKind::Scalar, id)),
        RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta => {
            if let NumericDomain::Interval(ref ivl) = state.domain {
                ivl.get_ptr_offset(r)
                    .and_then(|po| po.id)
                    .map(|id| (LinkageKind::PacketPtr, id))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `old.active_lock` constraint check: for every live register that
/// holds the locked map_value in `old` (i.e. its `PtrToMapValue.id`
/// equals `old.active_lock.ptr_id`), the same register in `cur` must
/// still hold a map_value whose id equals `cur.active_lock.ptr_id`.
///
/// Encodes the rule that pruning must not collapse a state where the
/// lock's owning register has been reassigned to a different map_value
/// — `bpf_spin_unlock` later in the cached continuation would target
/// the wrong identity. See `verifier_spin_lock::reg_id_for_map_value`.
fn active_lock_subsumed_by(cur: &State, old: &State, live_regs: &HashSet<Reg>) -> bool {
    use crate::analysis::machine::reg_types::RegType;
    let Some(old_lock) = old.get_active_lock() else {
        return true;
    };
    let cur_lock_ptr = cur.get_active_lock().map(|l| l.ptr_id);
    for &r in live_regs {
        if let RegType::PtrToMapValue { id: old_id, .. } = old.types.get(r) {
            if old_id != old_lock.ptr_id {
                continue;
            }
            // r holds the lock's map_value in `old`. Require the same
            // in `cur`: cur.r must be a PtrToMapValue whose id matches
            // cur's active_lock.
            let RegType::PtrToMapValue { id: cur_id, .. } = cur.types.get(r) else {
                return false;
            };
            if Some(cur_id) != cur_lock_ptr {
                return false;
            }
        }
    }
    true
}

/// Conservative id-equivalence check used by `state_subsumed_by`.
///
/// Returns true iff every pair `(r1, r2)` of live regs in the same
/// linkage class in `old` is also in the same linkage class in `cur`.
/// This is the safe direction: `cur` may have MORE links than `old`
/// (refinement narrows), but `old` cannot have links that `cur` lacks —
/// those are exactly the cases where future refinement in old's
/// continuation would silently miss propagation in cur. Mirrors
/// upstream `check_ids` in `regsafe`.
fn scalar_id_links_subsumed_by(
    cur: &State,
    old: &State,
    live_regs: &HashSet<Reg>,
) -> bool {
    let live: Vec<Reg> = live_regs.iter().copied().collect();
    for i in 0..live.len() {
        for j in (i + 1)..live.len() {
            let r1 = live[i];
            let r2 = live[j];
            let old_link = match (linkage_key(old, r1), linkage_key(old, r2)) {
                (Some(a), Some(b)) if a == b => true,
                _ => false,
            };
            if !old_link {
                continue;
            }
            let cur_link = match (linkage_key(cur, r1), linkage_key(cur, r2)) {
                (Some(a), Some(b)) if a == b => true,
                _ => false,
            };
            if !cur_link {
                return false;
            }
        }
    }
    true
}

/// Check if cur types are subsumed by old types.
fn types_subsumed_by(cur: &TypeState, old: &TypeState, live_regs: &HashSet<Reg>) -> bool {
    for &r in live_regs {
        if !type_subsumed_by(&cur.get(r), &old.get(r)) {
            return false;
        }
    }
    true
}

/// Check if cur_ty is subsumed by old_ty.
fn type_subsumed_by(cur_ty: &RegType, old_ty: &RegType) -> bool {
    use RegType::*;

    match (old_ty, cur_ty) {
        // Identical types
        (ScalarValue, ScalarValue) => true,
        (NotInit, NotInit) => true,
        (PtrToCtx, PtrToCtx) => true,
        (PtrToPacketEnd, PtrToPacketEnd) => true,

        // Anything subsumes NotInit
        (NotInit, _) => true,

        // Packet pointers: old must have >= range
        (PtrToPacket, PtrToPacket) => true,

        // Map value pointers
        (
            PtrToMapValue {
                offset: o1,
                map_idx: m1,
                ..
            },
            PtrToMapValue {
                offset: o2,
                map_idx: m2,
                ..
            },
        ) => {
            m1 == m2
                && match (o1, o2) {
                    (None, _) => true,
                    (Some(a), Some(b)) => a == b,
                    (Some(_), None) => false,
                }
        }

        // Map value or null
        (
            PtrToMapValueOrNull {
                id: id1,
                map_idx: m1,
            },
            PtrToMapValueOrNull {
                id: id2,
                map_idx: m2,
            },
        ) => m1 == m2 && id1 == id2,

        // Socket pointers
        (PtrToSocket { ref_id: id1 }, PtrToSocket { ref_id: id2 }) => id1 == id2,
        (PtrToSocketOrNull { ref_id: id1 }, PtrToSocketOrNull { ref_id: id2 }) => id1 == id2,

        // Stack pointers - DBM subsumption covers the numeric relationship
        (PtrToStack { frame_level: fl1 }, PtrToStack { frame_level: fl2 }) => fl1 == fl2,

        // PtrToAllocMem from `bpf_iter_*_next` etc.: the dispatcher mints
        // a fresh `id` on every call, so two visits to the same loop top
        // hold non-equal-but-semantically-identical allocs in the loop
        // variable. Subsume when (mem_size, ref_id) match — `ref_id`
        // None means unref-tracked iter-elem alloc, Some(N) means the
        // alloc is owned by a tracked acquire (dynptr_data slice from
        // a specific dynptr; ringbuf reservation). For the latter, the
        // matching ref_id ensures we don't conflate two acquires;
        // mem_size pins the bounds-check budget. Without this rule,
        // unbounded `bpf_for_each` loops state-explode (each iter's
        // fresh id breaks loop-top subsumption on the loop variable).
        // The `id` field is intentionally ignored — it's a per-call
        // tag, not a structural property.
        (
            PtrToAllocMem { mem_size: ms1, ref_id: ri1, .. },
            PtrToAllocMem { mem_size: ms2, ref_id: ri2, .. },
        ) => ms1 == ms2 && ri1 == ri2,
        (
            PtrToAllocMemOrNull { mem_size: ms1, ref_id: ri1, .. },
            PtrToAllocMemOrNull { mem_size: ms2, ref_id: ri2, .. },
        ) => ms1 == ms2 && ri1 == ri2,

        // Default: structural equality. Covers variants without a
        // looser explicit rule (PtrToBtfId, PtrToCpumask, PtrToArena,
        // PtrToCgroup, PtrToTask, PtrToOwnedKptr, PtrToMapKptr,
        // PtrToCallback, PtrToSockCommon, PtrToTcpSock, PtrToPacketMeta,
        // and the *OrNull versions of the above). Without this fallback,
        // identical pointer types compare unequal at prune-points and
        // every state is treated as novel — that's the entire reason
        // `bpf_cubic_cong_avoid` (and any struct_ops program with a
        // long-lived `PtrToBtfId` arg in r6-r9) hits the complexity
        // limit. PartialEq is derived on RegType, so structural ==
        // is the right canonical check for these.
        (a, b) if a == b => true,
        _ => false,
    }
}

/// Check if cur numeric domain is subsumed by old domain.
///
/// For registers listed in `precise`, subsumption requires *exact* interval
/// equality rather than superset coverage: a bound-check refinement that
/// W2.2 flagged as precision-critical must not be generalised away by
/// pruning against a looser cached state.
fn domain_subsumed_by(
    cur: &NumericDomain,
    old: &NumericDomain,
    live_regs: &HashSet<Reg>,
    precise: &HashSet<Reg>,
) -> bool {
    for &r in live_regs {
        let (old_min, old_max) = old.get_interval(r);
        let (cur_min, cur_max) = cur.get_interval(r);
        if precise.contains(&r) {
            if old_min != cur_min || old_max != cur_max {
                return false;
            }
        } else if !(old_min <= cur_min && old_max >= cur_max) {
            return false;
        }
    }

    // Anchor-to-anchor constraints (packet bounds) must also be subsumed.
    // These represent relationships like data_end - data >= N that are
    // critical for packet access safety and persist across calls.
    match (old, cur) {
        (NumericDomain::Zone(old_dbm), NumericDomain::Zone(cur_dbm)) => {
            zone_subsumed_by(old_dbm, cur_dbm, live_regs)
        }
        (NumericDomain::Interval(old_ivl), NumericDomain::Interval(cur_ivl)) => {
            interval_subsumed_by(old_ivl, cur_ivl)
        }
        _ => {
            // Mismatched domain types - should not happen in normal operation
            true
        }
    }
}

fn zone_subsumed_by(
    old_dbm: &crate::analysis::Dbm,
    cur_dbm: &crate::analysis::Dbm,
    live_regs: &HashSet<Reg>,
) -> bool {
    let anchors = [Reg::AnchorData, Reg::AnchorDataEnd, Reg::AnchorDataMeta];

    // Anchor↔anchor: packet-region geometry (e.g. `data_end - data >= N`).
    for &a in &anchors {
        for &b in &anchors {
            if a == b {
                continue;
            }
            if old_dbm.get(a, b) < cur_dbm.get(a, b) {
                return false;
            }
        }
    }

    // Live-reg pairs (including reg ↔ anchor): zone-mode analogue of
    // the kernel's id-tracking for packet pointers. Without this,
    // pruning collapses two states whose live registers differ in
    // their *relation* to one another or to a packet anchor —
    // e.g. one path established `r2 - r3 == 0` (`r2 = r3` aliasing)
    // and the other did not, but their standalone intervals coincide.
    // That's the FALSE_ACCEPT in
    // `verifier_direct_packet_access::id_in_regsafe_bad_access`.
    //
    // For subsumption: `old` covers `cur` only if every directed cell
    // `old.get(a, b) >= cur.get(a, b)` for live-reg pairs. (`>=` is
    // the looser direction in difference-bound semantics — a larger
    // upper bound on `a - b` is more permissive.)
    let live: Vec<Reg> = live_regs
        .iter()
        .copied()
        .filter(|r| !r.is_anchor())
        .collect();
    for &r in &live {
        for &a in &anchors {
            if old_dbm.get(r, a) < cur_dbm.get(r, a) {
                return false;
            }
            if old_dbm.get(a, r) < cur_dbm.get(a, r) {
                return false;
            }
        }
    }
    for i in 0..live.len() {
        for j in 0..live.len() {
            if i == j {
                continue;
            }
            let a = live[i];
            let b = live[j];
            if old_dbm.get(a, b) < cur_dbm.get(a, b) {
                return false;
            }
        }
    }
    true
}

fn interval_subsumed_by(
    old_ivl: &crate::domains::interval::IntervalState,
    cur_ivl: &crate::domains::interval::IntervalState,
) -> bool {
    // Interval domain: check packet_size_lower_bound and meta_size_lower_bound
    // For subsumption, old must be MORE permissive (fewer constraints) than cur.
    // If old requires a minimum packet size but cur doesn't, old does NOT subsume cur.
    let old_pkt = old_ivl.get_packet_size_bound().unwrap_or(0);
    let cur_pkt = cur_ivl.get_packet_size_bound().unwrap_or(0);
    if old_pkt > cur_pkt {
        return false;
    }
    let old_meta = old_ivl.get_meta_size_bound().unwrap_or(0);
    let cur_meta = cur_ivl.get_meta_size_bound().unwrap_or(0);
    if old_meta > cur_meta {
        return false;
    }
    true
}

fn stack_subsumed_by(cur: &State, old: &State) -> bool {
    for (old_frame, new_frame) in old.frames.iter().zip(cur.frames.iter()) {
        let all_offsets: HashSet<i16> = old_frame
            .stack
            .slot_offsets()
            .into_iter()
            .chain(new_frame.stack.slot_offsets())
            .collect();

        for offset in all_offsets {
            let old_ty = old_frame.stack.get_slot_type(offset);
            let new_ty = new_frame.stack.get_slot_type(offset);
            if !type_subsumed_by(&new_ty, &old_ty) {
                return false;
            }

            // Precision: a precise *cached* slot requires the new slot
            // to fall inside its range/tnum (kernel `regsafe` SCALAR
            // verifier.c v6.15 L18357: precise old → range_within +
            // tnum_in; non-precise old → free pass when live). Earlier
            // we keyed on `new_s.precise` and demanded EXACT — that's
            // stricter than the kernel and blocks may_goto-bounded
            // loops where a body memory access precision-marks the
            // counter (cond_break1/2/3, bucket F-D).
            let old_slot = old_frame.stack.get_slot(offset);
            let new_slot = new_frame.stack.get_slot(offset);
            if let (Some(old_s), Some(new_s)) = (old_slot, new_slot) {
                if old_s.precise {
                    if !tnum_covers(&new_s.tnum, &old_s.tnum) {
                        return false;
                    }
                    if !(old_s.bounds.min <= new_s.bounds.min
                        && new_s.bounds.max <= old_s.bounds.max)
                    {
                        return false;
                    }
                }
            }

            // W3.2c: open-coded iterator identity.
            //
            // An Active/Drained iterator slot represents a specific
            // loop instance (id minted at `*_new`). A cached state
            // subsumes the current one at this slot only when both
            // carry the exact same annotation — matching kind, state,
            // and id. Mismatched iterator state, mismatched id, or one
            // side carrying an annotation and the other not are all
            // semantically distinct program points and must not
            // collapse into a single pruned state.
            //
            // Non-precise loop-varying scalars are allowed to converge
            // via the existing W2.3 non-precise superset rule above —
            // this check is about the iterator identity itself, not
            // the loop variable.
            // `depth` is intentionally ignored — it grows monotonically
            // per iter_next ACTIVE-fork (kernel `iter.depth`) and is
            // used by the inf-loop detector and `widen_imprecise_scalars`
            // to keep iterations distinguishable, NOT by subsumption.
            // Kernel `states_equal(RANGE_WITHIN)` for iter_next call
            // sites doesn't compare `iter.depth` either; convergence
            // here is exactly what allows e.g. `i++; while(iter_next)`
            // loops to terminate.
            let old_iter = old_slot.and_then(|s| s.iterator);
            let new_iter = new_slot.and_then(|s| s.iterator);
            let iter_eq_modulo_depth = match (old_iter, new_iter) {
                (None, None) => true,
                (Some(a), Some(b)) => a.kind == b.kind && a.state == b.state && a.id == b.id,
                _ => false,
            };
            if !iter_eq_modulo_depth {
                return false;
            }

            // For packet pointers, also check interval_range subsumption.
            // If old has a proven range but cur doesn't, old does NOT subsume cur,
            // because cur might fail a packet access that old would pass.
            // We need to explore cur to find potential unsafe paths.
            if matches!(new_ty, RegType::PtrToPacket | RegType::PtrToPacketMeta) {
                let old_slot = old_frame.stack.get_slot(offset);
                let new_slot = new_frame.stack.get_slot(offset);
                if let (Some(old_s), Some(new_s)) = (old_slot, new_slot) {
                    use crate::analysis::machine::stack_state::PointerBounds;
                    let old_range = match &old_s.ptr_bounds {
                        Some(PointerBounds::Interval { range, .. }) => *range,
                        _ => None,
                    };
                    let new_range = match &new_s.ptr_bounds {
                        Some(PointerBounds::Interval { range, .. }) => *range,
                        _ => None,
                    };

                    match (old_range, new_range) {
                        // old has range but cur doesn't: old does NOT subsume cur
                        (Some(_), None) => return false,
                        // old has larger range than cur: old does NOT subsume cur
                        (Some(old_r), Some(new_r)) if old_r > new_r => return false,
                        // cur has range >= old, or both None: OK
                        _ => {}
                    }
                }
            }
        }
    }
    true
}

fn tnum_subsumed_by(cur_state: &State, old_state: &State, live_regs: &HashSet<Reg>) -> bool {
    for &r in live_regs {
        let cur = cur_state.get_tnum(r);
        let old = old_state.get_tnum(r);
        if old_state.is_reg_precise(r) {
            if !tnum_covers(&cur, &old) {
                return false;
            }
        } else if !tnum_covers(&cur, &old) {
            return false;
        }
    }
    true
}

/// Check if old tnum covers cur tnum (old's possible values are a superset of cur's).
fn tnum_covers(cur: &crate::domains::tnum::Tnum, old: &crate::domains::tnum::Tnum) -> bool {
    // Every unknown bit in cur must also be unknown in old
    if cur.mask & !old.mask != 0 {
        return false;
    }
    // For bits that are known in both, the values must match
    let both_known = !cur.mask & !old.mask;
    (cur.value & both_known) == (old.value & both_known)
}

/// Like tnum_subsumed_by but operates on call stack frames instead of full states.
fn caller_tnum_subsumed_by(
    cur_frame: &crate::analysis::machine::frame_stack::CallFrame,
    old_frame: &crate::analysis::machine::frame_stack::CallFrame,
    regs: &HashSet<Reg>,
) -> bool {
    for &r in regs {
        let cur = cur_frame
            .caller_tnums
            .get(&r)
            .copied()
            .unwrap_or(Tnum::UNKNOWN);
        let old = old_frame
            .caller_tnums
            .get(&r)
            .copied()
            .unwrap_or(Tnum::UNKNOWN);
        if !tnum_covers(&cur, &old) {
            return false;
        }
    }
    true
}
