// src/analysis/flow/pruning/widening.rs
//
// Loop detection, widening machinery, and counter analysis helpers.
// All pub(super) items are called from mod.rs (the orchestration layer).

use std::collections::HashSet;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Instr, Operand, Program};
use crate::common::config::VerifierConfig;
use crate::domains::tnum::Tnum;

/// Does this loop have at least one `Instr::If` exit? Used to distinguish
/// "natural" loops with comparison-based exits (where domain refinement on
/// the exit branch handles termination) from may_goto-only loops where the
/// runtime budget is the only termination guarantee.
pub(super) fn loop_has_if_exit(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
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

pub(super) fn loop_has_conditional_exit(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
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
pub(super) fn detect_loop_bound(
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
pub(super) fn is_prune_point(env: &VerifierEnv, pc: usize) -> bool {
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
pub(super) fn is_at_loop_point(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    // History must confirm this is a back-edge at current call depth
    let is_back_edge_pc = state
        .history_idx
        .map(|idx| env.history.is_back_edge(idx, pc, state.num_frames()))
        .unwrap_or(false);

    is_back_edge_pc && (is_backward_branch(pc, prog) || arrived_via_back_edge(env, state, pc, prog))
}

pub(super) fn apply_loop_bound(state: &mut State, loop_bound: Option<(Reg, i64)>) -> bool {
    if let Some((reg, upper_bound)) = loop_bound {
        let (cur_lo, _) = state.domain.get_interval(reg);
        if cur_lo <= upper_bound {
            state.domain.assume_le_imm(reg, upper_bound);
            state.domain.assume_ge_imm(reg, 0);
            // Use a tnum tight to the [0, upper_bound] interval rather
            // than blanket UNKNOWN. UNKNOWN destroys stack-offset
            // resolution downstream — `locks[i]` style stack stores
            // need the tnum to keep the low bits known so the verifier
            // can prove `r10 + offset + i*8` is a valid stack slot.
            // Pattern observed in
            // `res_spin_lock::res_spin_lock_test_held_lock_max`.
            // `Tnum::from_range` mirrors the kernel's `tnum_range`
            // (see kernel/bpf/tnum.c).
            state.set_tnum(reg, Tnum::from_range(0, upper_bound as u64));
            return true;
        }
    }
    false
}

/// Check if widening was effective (bounds expanded compared to first visit).
fn widening_was_effective(first: &State, last: &State, live_regs: &HashSet<Reg>) -> bool {
    live_regs.iter().any(|&r| {
        // Interval widening: last covers strictly more values than first.
        let (first_min, first_max) = first.domain.get_interval(r);
        let (last_min, last_max) = last.domain.get_interval(r);
        if last_min < first_min || last_max > first_max {
            return true;
        }
        // Tnum widening: last has more unknown bits than first. Without
        // this, scalar-counter loops where the interval was already
        // maximally wide (e.g. [S64_MIN, S64_MAX] propagated from a
        // boundary-crossing add) but the tnum was per-iteration precise
        // can never converge — widening is happening on tnum each
        // iteration but `widening_was_effective` only sees intervals.
        // Pattern observed in
        // verifier_bounds.c::crossing_64_bit_signed_boundary_2.
        let first_tn = first.get_tnum(r);
        let last_tn = last.get_tnum(r);
        // last has *more* unknown bits than first iff (last.mask | first.mask) != first.mask.
        if (last_tn.mask | first_tn.mask) != first_tn.mask {
            return true;
        }
        false
    })
}

/// Check if loop has converged and can be pruned.
/// Precondition: state is already subsumed by prev_states.last().
pub(super) fn check_loop_convergence(
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
    // Force-checkpoint PCs (iter_next kfuncs, may_goto, sync-cb-call
    // helpers) carry their own convergence guarantee: the kernel's
    // `is_state_visited` at these PCs treats subsumption alone as
    // sufficient because the iter-id / budget / cb-state mechanics in
    // the verifier semantics force termination independent of any
    // scalar widening on body-live regs. Without this exception, our
    // gates below (widening-effective + may_goto-progress) reject
    // valid prunes for iter-based loops where the loop variable lives
    // on the stack as an iter handle (not in a live register), and
    // the body's effects on the iter handle aren't visible as
    // "widening" in the live-reg sense. Audit on v6.15 corpus showed
    // this single missing case accounted for ~6 timeouts (clean_live_
    // states, widen_spill, iter_bpf_for_each_macro,
    // iter_nested_deeply_iters, triple_continue, bad_words: all had
    // many subsumption hits but `check_loop_convergence` returned
    // false on every one, so the iter just kept iterating until cap).
    // Iter-based convergence (kernel `is_state_visited` at iter_next):
    // if the loop body contains a force-checkpoint PC (iter_next /
    // may_goto / sync-cb-call helper), the iter-id mechanics in the
    // kernel guarantee termination — subsumption at the loop head is
    // sufficient, no scalar widening needed. Without this, our gates
    // below (widening-effective + may_goto-progress) reject every
    // valid prune for iter-based loops where the iter handle lives on
    // the stack and the "loop variable" never appears as a live reg.
    let body_has_force_checkpoint = state
        .history_idx
        .map(|idx| {
            env.history
                .loop_body_pcs(idx, pc, Some(state.num_frames()))
                .into_iter()
                .any(|body_pc| {
                    env.insn_aux_data
                        .get(body_pc)
                        .map(|a| a.force_checkpoint)
                        .unwrap_or(false)
                })
        })
        .unwrap_or(false);
    if body_has_force_checkpoint {
        return true;
    }

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
pub(super) fn apply_widening(
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
