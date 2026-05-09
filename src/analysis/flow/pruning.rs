// src/analysis/pruning.rs

use std::collections::HashSet;

use crate::analysis::machine::env::{SubsumptionMissReason, VerifierEnv};
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
fn loop_body_implied_bound(
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
struct SlotCounterInfo {
    slot_offset: i16,
    upper: i64,
}

fn detect_slot_counter(
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
fn apply_slot_loop_bound(state: &mut State, info: SlotCounterInfo) -> bool {
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
fn demote_body_written_scalar_slots(
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

fn apply_loop_bound(state: &mut State, loop_bound: Option<(Reg, i64)>) -> bool {
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
    env: &mut VerifierEnv,
    state: &mut State,
    pc: usize,
    prog: &Program,
    live_regs: &HashSet<Reg>,
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
            match state_subsumed_by(state, prev, live_regs, config) {
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
    // a per-branch comparison shaped like a bound. See
    // `project_push3_domain_widen_audit_2026-05-08`.
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
                let is_counter_shape = cur_lo >= 0
                    && state.scalar_id(r).is_none()
                    && loop_body_tests_reg(env, state, pc, prog, r)
                    && !body_feeds_other_live_reg_from(env, state, pc, prog, r, live_regs);
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
    config: &VerifierConfig,
) -> bool {
    let mut hit_idx: Option<usize> = None;
    let mut miss_idxs: Vec<usize> = Vec::new();
    let mut miss_reasons: Vec<SubsumptionMissReason> = Vec::new();
    if let Some(prev_states) = env.explored_states.get(&pc) {
        for (i, prev) in prev_states.iter().enumerate() {
            match state_subsumed_by(state, prev, live_regs, config) {
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

    // Bucket F-D: may_goto-specific RANGE_WITHIN prune class.
    if pc < prog.instrs.len()
        && matches!(prog.instrs[pc], Instr::If { .. } | Instr::MayGoto { .. })
        && let Some(prev_states) = env.explored_states.get(&pc)
    {
        let is_may_goto = matches!(prog.instrs[pc], Instr::MayGoto { .. });
        if is_may_goto && may_goto_range_within_prune(state, prev_states, &live_regs, config) {
            env.pruning_stats.may_goto_range_within_hits += 1;
            return true;
        }
    }

    let pruned = if in_loop {
        handle_loop_pruning(env, state, pc, prog, &live_regs, config)
    } else {
        handle_standard_pruning(env, state, pc, &live_regs, config)
    };
    pruned
}

/// Bucket F-A: bump miss_cnt for every `prev_idx` and evict whose
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

/// Bucket F-A: bump hit_cnt for the cached state at `prev_idx`.
fn record_pruning_hit(env: &mut VerifierEnv, pc: usize, prev_idx: usize) {
    env.pruning_stats.lifetime_hits += 1;
    if let Some(metrics) = env.state_metrics.get_mut(&pc)
        && let Some(m) = metrics.get_mut(prev_idx)
    {
        m.hit_cnt = m.hit_cnt.saturating_add(1);
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
        // Misses on this auxiliary RANGE_WITHIN prune class are
        // intentionally NOT recorded in the subsumption-miss histogram —
        // they would inflate the "stack" / "tnum" buckets with the
        // precision-stripped clone's behaviour, which isn't the same
        // as the standard subsumption pipeline we're trying to measure.
        if state_subsumed_by(&relaxed, prev, live_regs, config).is_ok() {
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
/// Returns `Ok(())` on success or `Err(reason)` identifying the *first*
/// sub-check that rejected. The reason is what the
/// `subsumption_misses` instrumentation aggregates per-PC.
fn state_subsumed_by(
    cur: &State,
    old: &State,
    live_regs: &HashSet<Reg>,
    config: &VerifierConfig,
) -> Result<(), SubsumptionMissReason> {
    // Order matters for instrumentation: the *first* rejecting check
    // is what we record, so cheaper / more-fundamental checks come
    // first to keep the histogram readable.
    if !types_subsumed_by(&cur.types, &old.types, live_regs) {
        return Err(SubsumptionMissReason::Types);
    }
    if !config.skip_dbm_check
        && !domain_subsumed_by(&cur.domain, &old.domain, live_regs, &old.precise_regs)
    {
        return Err(SubsumptionMissReason::Domain);
    }
    if !stack_subsumed_by(cur, old) {
        return Err(SubsumptionMissReason::Stack);
    }
    if !tnum_subsumed_by(cur, old, live_regs) {
        return Err(SubsumptionMissReason::Tnum);
    }

    // Cluster: regsafe scalar-id check.
    // If two live registers share a scalar_id in `old` (so a future
    // refinement on one will propagate to the other along the cached
    // continuation), `cur` must also have them linked. Otherwise the
    // cur-state's continuation would refine them independently — pruning
    // it against `old` hides paths where the unlinked register stays
    // unbounded. Mirrors upstream `check_ids` in `regsafe`.
    if !scalar_id_links_subsumed_by(cur, old, live_regs) {
        return Err(SubsumptionMissReason::ScalarIdLinks);
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
        return Err(SubsumptionMissReason::ActiveLock);
    }

    // W3.1c: `old` must have at least as much may_goto budget remaining as
    // `cur`, otherwise pruning would let `cur` continue under behaviours
    // `old` never explored (old already exhausted the budget on a path cur
    // hasn't yet reached). Monotone: budget only ever decreases, so once
    // cur's future iterations are covered by an old state with a larger or
    // equal counter, pruning is sound.
    if old.goto_budget < cur.goto_budget {
        return Err(SubsumptionMissReason::GotoBudget);
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
        return Err(SubsumptionMissReason::ActiveRefs);
    }

    // Check caller frames: callee-saved registers (r6-r9) persist across
    // calls and determine post-return control flow. Without this check,
    // two states that differ only in caller-frame r6-r9 values get pruned
    // against each other, hiding bugs that manifest after return.
    let saved = callee_saved_regs();
    for (cur_frame, old_frame) in cur.frames.iter().zip(old.frames.iter()) {
        if !types_subsumed_by(&cur_frame.caller_types, &old_frame.caller_types, &saved) {
            return Err(SubsumptionMissReason::CallerFrame);
        }
        if !config.skip_dbm_check
            && !domain_subsumed_by(
                &cur_frame.caller_domain,
                &old_frame.caller_domain,
                &saved,
                &HashSet::new(),
            )
        {
            return Err(SubsumptionMissReason::CallerFrame);
        }
        if !caller_tnum_subsumed_by(cur_frame, old_frame, &saved) {
            return Err(SubsumptionMissReason::CallerFrame);
        }
    }

    Ok(())
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

        // Map value or null. Like `PtrToAllocMem` below, the kernel
        // mints a fresh `id` on every `bpf_map_lookup_elem` call —
        // looping `map_val = bpf_map_lookup_elem(...); if (map_val) ...`
        // produces non-equal-but-semantically-identical pointers across
        // iterations and id-equality blocks loop-top subsumption.
        // Structural identity is `map_idx` (which map); `id` is a per-
        // call tag used for null-check narrowing on the *current*
        // state's continuation, not for cross-state subsumption.
        // Pattern observed in iters.c::iter_tricky_but_fine.
        (
            PtrToMapValueOrNull { map_idx: m1, .. },
            PtrToMapValueOrNull { map_idx: m2, .. },
        ) => m1 == m2,

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

/// Set of precise live registers whose intervals fail the kernel
/// `range_within` check between `cur` and `old`. Order-stable: returns
/// registers in the iteration order of `live_regs`.
fn precise_domain_diverging_regs(
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
fn dbm_diverging_regs(
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
enum CounterDirection {
    Ascending,
    Descending,
}

/// If `r` is singleton-precise in both `cur` and `old` AND strictly
/// changing (`cur_min != old_min`), classify the direction. Otherwise
/// returns `None`. The singleton requirement filters oscillating
/// counters in `infinite_loop_three_jump_trick`-style tests where the
/// abstract domain has joined the counter to a non-singleton interval.
fn singleton_strict_direction(
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
fn loop_body_tests_reg(
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
fn body_feeds_other_live_reg_from(
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

/// True iff `r`'s precise value is "safely demotable": no body use
/// transfers `r`'s value into another LIVE register or memory address.
/// Reading `r` into a non-live transient register is fine (the
/// transient is reset each iter). Reading `r` as a memory base or
/// into a live destination is not.
///
/// Used to identify precise diverging registers that only drive
/// branches (or transient computations) and can have their cached-
/// side precision marks dropped, letting the kernel `!precise →
/// accept` rule cover them on subsumption against the widened state.
fn body_uses_reg_only_in_branches(
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

fn domain_subsumed_by(
    cur: &NumericDomain,
    old: &NumericDomain,
    live_regs: &HashSet<Reg>,
    precise: &HashSet<Reg>,
) -> bool {
    // Kernel `regsafe` rule (verifier.c v6.15 L18357 / L18387):
    //   - precise → range_within (old ⊇ cur)
    //   - !precise → accept (kernel doesn't compare imprecise scalars
    //     across cur/old at all).
    for &r in live_regs {
        if !precise.contains(&r) {
            continue;
        }
        let (old_min, old_max) = old.get_interval(r);
        let (cur_min, cur_max) = cur.get_interval(r);
        if !(old_min <= cur_min && old_max >= cur_max) {
            if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                eprintln!(
                    "[domain_miss] reg={:?} precise old=[{},{}] cur=[{},{}]",
                    r, old_min, old_max, cur_min, cur_max
                );
            }
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
                if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                    eprintln!("[domain_miss] anchor-anchor a={:?} b={:?}", a, b);
                }
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
                if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                    eprintln!("[domain_miss] reg-anchor r={:?} a={:?}", r, a);
                }
                return false;
            }
            if old_dbm.get(a, r) < cur_dbm.get(a, r) {
                if std::env::var("ZOVIA_DUMP_DOMAIN_MISS").ok().as_deref() == Some("1") {
                    eprintln!("[domain_miss] anchor-reg a={:?} r={:?}", a, r);
                }
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

/// Stack-slot type subsumption: stricter than `type_subsumed_by`.
/// NotInit only subsumes NotInit (no "covers anything" rule), and
/// otherwise we use the same family rules as registers.
fn stack_slot_type_subsumed_by(new_ty: &RegType, old_ty: &RegType) -> bool {
    use RegType::*;
    match (old_ty, new_ty) {
        (NotInit, NotInit) => true,
        // For non-NotInit pairs, defer to register-style rules.
        // The default rule `(a, b) if a == b => true` covers most
        // pointer types; ScalarValue→ScalarValue covers the common
        // "spilled scalar" case; PtrToMapValue offsets etc. have
        // their own match arms in `type_subsumed_by`.
        _ => type_subsumed_by(new_ty, old_ty),
    }
}

fn stack_subsumed_by(cur: &State, old: &State) -> bool {
    // Kernel-aligned idmap (verifier.c v6.15 `check_ids` in regsafe at
    // STACK_ITER L18583): iter ids are minted fresh by every
    // `bpf_iter_*_new` call, so literal `old.id == cur.id` always fails
    // when an iter slot is re-initialized (e.g. nested iters: each outer
    // iteration recreates the inner iter at the same stack slot with a
    // fresh id). Build a per-comparison map `old_id → cur_id` and check
    // for consistency: a given old id may map to exactly one cur id
    // across the comparison.
    let mut iter_idmap: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
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
            // Stack-specific subsumption is STRICTER than register
            // `type_subsumed_by`. For registers, `(NotInit, _) => true`
            // is correct: an uninit reg "covers" anything because
            // future reads error anyway. For STACK slots, NotInit
            // means "never written" — semantically a specific state
            // distinct from "written with type X". Pruning cur (with
            // a written slot) against cached (with the slot
            // unwritten) skips exploring cur's continuation, which
            // observes the written slot; cached's continuation never
            // does, so the two are not equivalent.
            //
            // Pattern from `rbtree::rbtree_add_and_remove_array` and
            // `test_cls_redirect::cls_redirect`: slot reused across
            // paths with different types; cached state with NotInit
            // (or earlier-spilled scalar) wrongly subsumes a path
            // that has spilled `PtrToOwnedKptr` / `PtrToPacket` to
            // the same offset.
            if !stack_slot_type_subsumed_by(&new_ty, &old_ty) {
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
                (Some(a), Some(b)) => {
                    if a.kind != b.kind || a.state != b.state {
                        false
                    } else {
                        // check_ids: id may be remapped, but consistently.
                        match iter_idmap.get(&a.id) {
                            Some(&mapped) => mapped == b.id,
                            None => {
                                iter_idmap.insert(a.id, b.id);
                                true
                            }
                        }
                    }
                }
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
    // Kernel rule: precise → tnum-cover; !precise → accept.
    for &r in live_regs {
        if !old_state.is_reg_precise(r) {
            continue;
        }
        let cur = cur_state.get_tnum(r);
        let old = old_state.get_tnum(r);
        if !tnum_covers(&cur, &old) {
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
