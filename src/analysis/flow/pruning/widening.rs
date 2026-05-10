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
use crate::domains::numeric::NumericDomain;
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

/// Scan the loop body for a `reg cmp imm` branch comparing `reg` against
/// a positive immediate. Returns the implied upper bound on `reg` under
/// monotone-from-zero increment semantics. **Used only by the widening
/// gate** — not by `apply_loop_bound`, because applying the bound
/// unconditionally (e.g. via `assume_le_imm` + tnum=UNKNOWN) is unsound
/// for multi-branch loops like `verifier_loops1::infinite_loop_three_jump_trick`,
/// where the per-branch test caps `r0` but the loop is genuinely infinite.
/// The widening gate consumes this bound only as a sanity check on the
/// diverging precise register; convergence soundness is then enforced by
/// the monotone-progress check on cur vs old intervals.
pub(super) fn loop_body_implied_bound(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
    target_reg: Reg,
) -> Option<i64> {
    let history_idx = state.history_idx?;
    let mut body_pcs = env.history.loop_body_pcs(history_idx, current_pc, Some(state.num_frames()));
    body_pcs.push(current_pc);
    for body_pc in body_pcs {
        if body_pc >= prog.instrs.len() {
            continue;
        }
        let Instr::If { op, left, right, .. } = &prog.instrs[body_pc] else {
            continue;
        };
        if *left != target_reg {
            continue;
        }
        let (k, right_is_reg) = match right {
            Operand::Imm(k) => (*k, false),
            Operand::Reg(r) => {
                let (lo, hi) = state.domain.get_interval(*r);
                if lo == hi { (lo, true) } else { continue }
            }
        };
        // Right-hand side `Reg(k_const)` is only safe for *unsigned*
        // comparison ops. For signed ops the counter may live in the
        // negative half (e.g.
        // `verifier_bounds::crossing_32_bit_signed_boundary_2` runs
        // `r0 += 1` from `0x80000000`); applying a `[0, k]` widening
        // would unsoundly drop the low half of its actual range.
        if right_is_reg
            && !matches!(op, CmpOp::Ne | CmpOp::Eq | CmpOp::UGe | CmpOp::UGt | CmpOp::ULt | CmpOp::ULe)
        {
            continue;
        }
        let upper = match op {
            CmpOp::Ne
            | CmpOp::Eq
            | CmpOp::UGe
            | CmpOp::SGe
            | CmpOp::ULt
            | CmpOp::SLt => k - 1,
            CmpOp::UGt | CmpOp::SGt | CmpOp::ULe | CmpOp::SLe => k,
            _ => continue,
        };
        if upper <= 0 {
            continue;
        }
        return Some(upper);
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

/// Apply loop bound constraints to the state.
/// Returns true if bounds were applied.
/// Spilled-counter shape: a stack slot at `slot_offset` (frame 0) is
/// updated each iter via a load-add-store triple
/// (`R := *(R10+slot); R += stride; *(R10+slot) := R`), AND the loop's
/// back-edge tests `*(R10+slot) < K` (or similar `<`/`<=` shape) against
/// a constant K. The slot is the iteration counter; widening it to
/// `[0, K - stride*slack]` lets singleton-precise arrivals subsume.
///
/// Excludes the oscillating / constant counterexamples
/// (`infinite_loop_three_jump_trick`, `infinite_loop_in_two_jumps`):
/// neither has a load-add-store stack-counter triple — the constant
/// case never writes to a slot, the oscillating case operates entirely
/// in registers with `r0 &= 1`.
#[derive(Clone, Copy, Debug)]
pub(super) struct SlotCounterInfo {
    pub slot_offset: i16,
    pub upper: i64,
}

pub(super) fn detect_slot_counter(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
) -> Option<SlotCounterInfo> {
    // Find the back-edge: either current_pc is a branch back to the
    // loop top, or we just arrived via one. Identify the back-edge's
    // `If left CMP right` shape and capture (left, k).
    let body_pcs_set: HashSet<usize> = state
        .history_idx
        .map(|idx| {
            env.history
                .loop_body_pcs(idx, current_pc, Some(state.num_frames()))
                .into_iter()
                .collect()
        })
        .unwrap_or_default();

    let (left_reg, k) = {
        // Walk body PCs (plus current) for the back-edge `If` whose
        // target lands at current_pc. Multiple body Ifs are possible;
        // we want the one whose taken branch is the back-edge.
        let mut found: Option<(Reg, i64)> = None;
        let mut scan_pcs: Vec<usize> = body_pcs_set.iter().copied().collect();
        scan_pcs.push(current_pc);
        for pc in scan_pcs {
            if pc >= prog.instrs.len() {
                continue;
            }
            let Instr::If {
                op,
                left,
                right,
                target,
                ..
            } = &prog.instrs[pc]
            else {
                continue;
            };
            // Back-edge: taken branch loops back to current_pc, OR the
            // fall-through is the back-edge (target leaves the loop).
            // Both directions count as a "loop test" — we just need the
            // continue-direction's upper bound on `left`.
            let target_in_body = body_pcs_set.contains(target) || *target == current_pc;
            let fall = pc + 1;
            let fall_in_body = body_pcs_set.contains(&fall) || fall == current_pc;
            if !target_in_body && !fall_in_body {
                continue;
            }
            let k_opt = match right {
                Operand::Imm(k) => Some(*k),
                Operand::Reg(r) => {
                    let (lo, hi) = state.domain.get_interval(*r);
                    if lo == hi { Some(lo) } else { None }
                }
            };
            let Some(k) = k_opt else { continue };
            if k <= 0 {
                continue;
            }
            // Determine the upper bound on `left` along the continue
            // direction. Continue direction = whichever branch stays in
            // the body.
            let (cont_dir_taken, _) = (target_in_body, fall_in_body);
            let upper = if cont_dir_taken {
                // Continue when branch is TAKEN: left CMP k holds.
                match op {
                    CmpOp::Ne | CmpOp::ULt | CmpOp::SLt => k - 1,
                    CmpOp::ULe | CmpOp::SLe => k,
                    _ => continue,
                }
            } else {
                // Continue when branch is NOT TAKEN: !(left CMP k) holds.
                match op {
                    CmpOp::UGe | CmpOp::SGe => k - 1,
                    CmpOp::UGt | CmpOp::SGt => k,
                    _ => continue,
                }
            };
            if upper <= 0 {
                continue;
            }
            found = Some((*left, upper));
            break;
        }
        found?
    };

    // Walk body PCs to find the load-add-store triple targeting a stack
    // slot, where the loaded register is `left_reg` (or feeds it).
    // Specifically:
    //   - `Load { dst: Rx, base: R10, off: slot_offset }`
    //   - `Alu { op: Add, dst: Rx, src: Imm(positive) }`
    //   - `Store { base: R10, off: slot_offset, src: Reg(Rx) }`
    // The sequence may have unrelated body insns interleaved; we just
    // need all three to be present and reference the same slot_offset
    // and same Rx, in that program order.
    let mut body_seq: Vec<usize> = body_pcs_set.iter().copied().collect();
    body_seq.sort_unstable();

    let mut load_info: Option<(usize, Reg, i16)> = None; // (pc, dst, off)
    let mut add_info: Option<(usize, Reg, i64)> = None;
    let mut store_match: Option<i16> = None;
    for &pc in &body_seq {
        if pc >= prog.instrs.len() {
            continue;
        }
        match &prog.instrs[pc] {
            Instr::Load { dst, base, off, .. } if *base == Reg::R10 => {
                load_info = Some((pc, *dst, *off));
                add_info = None;
            }
            Instr::Alu {
                op: crate::ast::AluOp::Add,
                dst,
                src: Operand::Imm(k),
                ..
            } => {
                if let Some((_lpc, ldst, _loff)) = load_info
                    && *dst == ldst
                    && *k > 0
                {
                    add_info = Some((pc, *dst, *k));
                }
            }
            Instr::Store {
                base,
                off,
                src: Operand::Reg(s),
                ..
            } if *base == Reg::R10 => {
                if let (Some((_lpc, ldst, loff)), Some((_apc, adst, _ak))) =
                    (load_info, add_info)
                    && loff == *off
                    && ldst == *s
                    && adst == ldst
                {
                    store_match = Some(*off);
                    break;
                }
            }
            _ => {}
        }
    }

    let slot_offset = store_match?;

    // Confirm that `left_reg` itself was loaded from this slot somewhere
    // in the body (typically just before the back-edge for the
    // post-store reload). If `left_reg` was loaded from the same slot
    // we identified, the back-edge is genuinely testing the counter.
    let mut left_loads_from_slot = false;
    for &pc in &body_seq {
        if pc >= prog.instrs.len() {
            continue;
        }
        if let Instr::Load { dst, base, off, .. } = &prog.instrs[pc]
            && *dst == left_reg
            && *base == Reg::R10
            && *off == slot_offset
        {
            left_loads_from_slot = true;
            break;
        }
    }
    if !left_loads_from_slot {
        return None;
    }

    Some(SlotCounterInfo {
        slot_offset,
        upper: k,
    })
}

/// Apply a detected slot counter's bound: widen the slot's bounds and
/// tnum to `[0, upper]`. Mirrors the register-side `apply_loop_bound`
/// but targets the spilled scalar at frame 0, slot offset.
pub(super) fn apply_slot_loop_bound(state: &mut State, info: SlotCounterInfo) -> bool {
    use crate::analysis::machine::frame_stack::FrameLevel;
    use crate::analysis::machine::stack_state::ScalarBounds;

    // First read+rewrite the slot, capturing its `scalar_id` so we can
    // clear linked register IDs in step 2. Linkage propagates from the
    // slot at fill time: any register loaded from this slot inherits
    // the slot's `scalar_id`. Counter-shape classification at the
    // existing reg-side widening rejects regs with non-None scalar_id,
    // so leaving the link in place blocks the reg-counter widening
    // from firing on the loaded R3 — convergence requires both the
    // slot widening AND the reg-counter widening on the loaded reg.
    let prior_scalar_id: Option<u32>;
    {
        let stack = &mut state.frames.get_mut(FrameLevel::from_index(0)).stack;
        let Some(slot) = stack.get_slot_mut(info.slot_offset) else {
            return false;
        };
        if slot.bounds.min < 0 || info.upper < 0 {
            return false;
        }
        let new_max = info.upper.max(slot.bounds.min);
        slot.bounds = ScalarBounds {
            min: 0,
            max: new_max,
        };
        slot.tnum = Tnum::from_range(0, new_max as u64);
        slot.precise = false;
        prior_scalar_id = slot.scalar_id;
        slot.scalar_id = None;
    }

    // Clear scalar_id on any register linked to this slot via the
    // captured id. The kernel's `sync_linked_regs` would refine all
    // linked siblings together — clearing the link is safe because
    // we've already widened the slot beyond the per-iter precise value
    // (any subsequent refinement that targeted this id would have been
    // overridden by the widening anyway).
    if let Some(sid) = prior_scalar_id {
        for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5,
                  Reg::R6, Reg::R7, Reg::R8, Reg::R9] {
            if state.scalar_id(r) == Some(sid) {
                state.clear_scalar_id(r);
            }
        }
    }
    true
}

/// Demote precision on scalar stack slots that are written in the loop
/// body via load-modify-store (any RHS, not just `Imm`), excluding the
/// detected counter slot. Used together with `apply_slot_loop_bound` to
/// let `sum += val`-style accumulators stop blocking loop-top
/// subsumption. Sound for slots NOT involved in the loop-test back-edge.
pub(super) fn demote_body_written_scalar_slots(
    env: &VerifierEnv,
    state: &mut State,
    current_pc: usize,
    prog: &Program,
    skip_offset: i16,
) {
    use crate::analysis::machine::frame_stack::FrameLevel;

    let body_pcs: HashSet<usize> = state
        .history_idx
        .map(|idx| {
            env.history
                .loop_body_pcs(idx, current_pc, Some(state.num_frames()))
                .into_iter()
                .collect()
        })
        .unwrap_or_default();

    // Find all `Store { base: R10, off: K, src: Reg(_) }` body offsets
    // that participate in a load → ALU → store triple.
    let mut load_dst: std::collections::HashMap<i16, Reg> = std::collections::HashMap::new();
    let mut alu_seen: std::collections::HashSet<Reg> = std::collections::HashSet::new();
    let mut written_offsets: std::collections::HashSet<i16> = std::collections::HashSet::new();
    let mut body_seq: Vec<usize> = body_pcs.iter().copied().collect();
    body_seq.sort_unstable();
    for pc_b in body_seq {
        if pc_b >= prog.instrs.len() {
            continue;
        }
        match &prog.instrs[pc_b] {
            Instr::Load { dst, base, off, .. } if *base == Reg::R10 => {
                load_dst.insert(*off, *dst);
                alu_seen.clear();
            }
            Instr::Alu { dst, .. } => {
                alu_seen.insert(*dst);
            }
            Instr::Store {
                base,
                off,
                src: Operand::Reg(s),
                ..
            } if *base == Reg::R10 => {
                if load_dst.get(off) == Some(s) || alu_seen.contains(s) {
                    written_offsets.insert(*off);
                }
            }
            _ => {}
        }
    }

    let stack = &mut state.frames.get_mut(FrameLevel::from_index(0)).stack;
    for offset in written_offsets {
        if offset == skip_offset {
            continue;
        }
        if let Some(slot) = stack.get_slot_mut(offset)
            && slot.precise
        {
            slot.precise = false;
            slot.tnum = Tnum::UNKNOWN;
        }
    }
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

/// Set of precise live registers whose intervals fail the kernel
/// `range_within` check between `cur` and `old`. Order-stable: returns
/// registers in the iteration order of `live_regs`.
pub(super) fn precise_domain_diverging_regs(
    cur: &NumericDomain,
    old: &NumericDomain,
    live_regs: &HashSet<Reg>,
    precise: &HashSet<Reg>,
) -> Vec<Reg> {
    let mut out = Vec::new();
    for &r in live_regs {
        if !precise.contains(&r) {
            continue;
        }
        let (old_min, old_max) = old.get_interval(r);
        let (cur_min, cur_max) = cur.get_interval(r);
        if !(old_min <= cur_min && old_max >= cur_max) {
            out.push(r);
        }
    }
    out
}

/// Set of live registers (precise or not) whose `(reg → anchor)` DBM
/// cell value strictly increased between `old` and `cur`, i.e.
/// `old.get(r, anchor) < cur.get(r, anchor)`. These are the regs that
/// block `zone_subsumed_by`'s reg↔anchor check independent of
/// precision marks. Used by the widening gate to identify scalars
/// that aren't tracked as precise but still cause domain misses
/// because their DBM-tracked intervals diverge across cached states.
/// Pattern from `test_parse_tcp_hdr_opt_dynptr` where R6 (byte_offset
/// accumulator) is non-precise yet its DBM cells advance per iter.
pub(super) fn dbm_diverging_regs(
    cur: &NumericDomain,
    old: &NumericDomain,
    live_regs: &HashSet<Reg>,
) -> Vec<Reg> {
    let mut out = Vec::new();
    for &r in live_regs {
        if r.is_anchor() {
            continue;
        }
        let (old_min, old_max) = old.get_interval(r);
        let (cur_min, cur_max) = cur.get_interval(r);
        if !(old_min <= cur_min && old_max >= cur_max) {
            out.push(r);
        }
    }
    out
}

/// Direction of counter progress between two singleton-precise states.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CounterDirection {
    Ascending,
    Descending,
}

/// If `r` is singleton-precise in both `cur` and `old` AND strictly
/// changing (`cur_min != old_min`), classify the direction. Otherwise
/// returns `None`. The singleton requirement filters oscillating
/// counters in `infinite_loop_three_jump_trick`-style tests where the
/// abstract domain has joined the counter to a non-singleton interval.
pub(super) fn singleton_strict_direction(
    cur: &NumericDomain,
    old: &NumericDomain,
    r: Reg,
) -> Option<CounterDirection> {
    let (old_min, old_max) = old.get_interval(r);
    let (cur_min, cur_max) = cur.get_interval(r);
    if old_min != old_max || cur_min != cur_max {
        return None;
    }
    if cur_min > old_min {
        Some(CounterDirection::Ascending)
    } else if cur_min < old_min {
        Some(CounterDirection::Descending)
    } else {
        None
    }
}

/// True iff the loop body contains an `If r cmp imm` branch on `r` —
/// any cmp, any imm. Distinguishes a register that genuinely drives a
/// loop test (the body uses it in a comparison) from a precise scalar
/// that merely accumulates per iter without bound-driving the loop.
/// Used as a "this is a real counter" heuristic for both ascending and
/// descending widening cases.
pub(super) fn loop_body_tests_reg(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
    target_reg: Reg,
) -> bool {
    let Some(history_idx) = state.history_idx else {
        return false;
    };
    let mut body_pcs = env.history.loop_body_pcs(history_idx, current_pc, Some(state.num_frames()));
    body_pcs.push(current_pc);
    for body_pc in body_pcs {
        if body_pc >= prog.instrs.len() {
            continue;
        }
        if let Instr::If { op, left, right, .. } = &prog.instrs[body_pc]
            && *left == target_reg
        {
            // Counter-shape branch: right-side is either an immediate or
            // a register holding a singleton constant. The latter is
            // restricted to unsigned comparison ops because signed ops
            // permit the counter to live in the negative half (see
            // `loop_body_implied_bound` for the matching gate; both
            // helpers must agree on what counts as a counter shape so
            // classification and bound extraction stay in sync).
            match right {
                Operand::Imm(_) => return true,
                Operand::Reg(r) => {
                    let (lo, hi) = state.domain.get_interval(*r);
                    if lo == hi
                        && matches!(
                            op,
                            CmpOp::Ne
                                | CmpOp::Eq
                                | CmpOp::UGe
                                | CmpOp::UGt
                                | CmpOp::ULt
                                | CmpOp::ULe
                        )
                    {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// True iff the loop body contains an Alu instruction `dst := dst OP counter`
/// where `dst != counter` and `dst` is in `live_regs`. Widening a
/// counter that feeds a live accumulator unbounds the accumulator
/// across iterations and breaks subsumption on it. Pattern observed
/// in `verifier_loops1::back_jump_to_1st_insn_2` (`r2 += r1; r1 -= 1;
/// if r1 != 0 goto`). We check the body's instruction stream rather
/// than precision marks because the live arrival state hasn't yet
/// accumulated marks for `dst` at the time the gate is evaluated —
/// precision propagates retroactively via mark_chain_precision after
/// the back-edge fires.
pub(super) fn body_feeds_other_live_reg_from(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
    counter: Reg,
    live_regs: &HashSet<Reg>,
) -> bool {
    let Some(history_idx) = state.history_idx else {
        return false;
    };
    // `loop_body_pcs` excludes target_pc itself, but the loop head's own
    // instruction is part of the body for our purposes (in
    // `back_jump_to_1st_insn_2` the loop head is the `r2 += r1` Alu).
    // Include it.
    let mut scan_pcs = env.history.loop_body_pcs(history_idx, current_pc, Some(state.num_frames()));
    scan_pcs.push(current_pc);
    for body_pc in scan_pcs {
        if body_pc >= prog.instrs.len() {
            continue;
        }
        if let Instr::Alu { dst, src: Operand::Reg(src), .. } = &prog.instrs[body_pc] {
            if *src == counter && *dst != counter && live_regs.contains(dst) {
                return true;
            }
        }
    }
    false
}

/// Find live registers that the loop body writes via Alu-from-counter
/// (`A := A OP counter` or `A := counter OP B` or `A := counter`).
/// These are the regs that block `body_feeds_other_live_reg_from`'s
/// "no-counter-feeds-accumulator" gate; the caller may demote them
/// alongside the counter widening if they are pure accumulators (no
/// memory base / branch use).
pub(super) fn find_counter_fed_regs(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
    counter: Reg,
    live_regs: &HashSet<Reg>,
) -> HashSet<Reg> {
    let mut out = HashSet::new();
    let Some(history_idx) = state.history_idx else {
        return out;
    };
    let mut scan_pcs = env.history.loop_body_pcs(history_idx, current_pc, Some(state.num_frames()));
    scan_pcs.push(current_pc);
    for body_pc in scan_pcs {
        if body_pc >= prog.instrs.len() {
            continue;
        }
        if let Instr::Alu { dst, src: Operand::Reg(src), .. } = &prog.instrs[body_pc]
            && *src == counter
            && *dst != counter
            && live_regs.contains(dst)
        {
            out.insert(*dst);
        }
    }
    out
}

/// True iff `r` is an "accumulator" — its body uses are confined to
/// (a) self-updates (`r := f(r, ...)` or `r := f(s, r)`),
/// (b) writes-into-other-regs that themselves are accumulators
///     (transitive — captured by `accumulator_set`),
/// and `r` is never used as a memory base or a branch operand. Caller
/// must pre-compute the candidate accumulator set so this function can
/// check "writes into another accumulator" without recursing.
pub(super) fn is_pure_accumulator(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
    r: Reg,
    accumulator_set: &HashSet<Reg>,
    live_regs: &HashSet<Reg>,
) -> bool {
    let Some(history_idx) = state.history_idx else {
        return false;
    };
    let mut scan_pcs = env.history.loop_body_pcs(history_idx, current_pc, Some(state.num_frames()));
    scan_pcs.push(current_pc);
    for body_pc in scan_pcs {
        if body_pc >= prog.instrs.len() {
            continue;
        }
        match &prog.instrs[body_pc] {
            // Branch on r: kernel's `!precise → accept` rule covers
            // imprecise scalars in If — both branches get explored
            // when r is non-precise, which is conservative-safe for
            // verification (cur arrivals at either branch target subsume
            // against the cached widened state regardless of r). No
            // soundness violation; mirrors the existing
            // `body_uses_reg_only_in_branches` demote path.
            Instr::If { .. } => {}
            Instr::Alu { dst, src, .. } => {
                if *dst == r {
                    continue; // self-update OK
                }
                if let Operand::Reg(s) = src
                    && *s == r
                    && live_regs.contains(dst)
                    && !accumulator_set.contains(dst)
                {
                    return false; // writes into a non-accumulator live reg
                }
            }
            Instr::MovSx { dst, src, .. } => {
                if *dst == r {
                    continue;
                }
                if let Operand::Reg(s) = src
                    && *s == r
                    && live_regs.contains(dst)
                    && !accumulator_set.contains(dst)
                {
                    return false;
                }
            }
            Instr::Load { base, dst, .. } => {
                // r as memory base: precision is load-bearing for the
                // address bound, demoting unsound.
                if *base == r {
                    return false;
                }
                // Load INTO r is fine — it reassigns r entirely, so
                // r's prior precision doesn't matter for any use after
                // this point. The post-load value is a fresh scalar
                // tracked independently. (Loop1's `m = PT_REGS_RC(ctx)`
                // pattern at pc=13 reassigns R0 from ctx memory.)
                let _ = dst;
            }
            Instr::Store { base, src, .. } => {
                if *base == r {
                    return false;
                }
                // Store r into memory: spilled value lives in the slot;
                // the slot tracks its own precision and we don't model
                // demotion-vs-slot-precision interplay yet. Conservative.
                if let Operand::Reg(s) = src
                    && *s == r
                {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

pub(super) fn body_uses_reg_only_in_branches(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
    r: Reg,
    live_regs: &HashSet<Reg>,
) -> bool {
    let Some(history_idx) = state.history_idx else {
        return false;
    };
    let mut scan_pcs = env.history.loop_body_pcs(history_idx, current_pc, Some(state.num_frames()));
    scan_pcs.push(current_pc);
    for body_pc in scan_pcs {
        if body_pc >= prog.instrs.len() {
            continue;
        }
        match &prog.instrs[body_pc] {
            Instr::If { .. } => {}
            Instr::Alu { dst, src, .. } => {
                // Self-update (r := r OP _): always fine (the reg
                // mutates itself within the loop).
                if *dst == r {
                    continue;
                }
                // r as src into a non-r dst: only a "use of r's
                // precision" if dst is live across the loop head.
                if let Operand::Reg(s) = src {
                    if *s == r && live_regs.contains(dst) {
                        return false;
                    }
                }
            }
            Instr::MovSx { dst, src, .. } => {
                if *dst == r {
                    continue;
                }
                if let Operand::Reg(s) = src {
                    if *s == r && live_regs.contains(dst) {
                        return false;
                    }
                }
            }
            Instr::Load { base, .. } => {
                if *base == r {
                    return false;
                }
            }
            Instr::Store { base, .. } => {
                // r-as-base is a hard memory-access use. r-as-src
                // just spills the value to memory; the stack slot
                // tracks its own precision independently.
                if *base == r {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}
