// src/analysis/pruning.rs

use std::collections::HashSet;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Instr, Operand, Program};
use crate::common::config::VerifierConfig;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{assume_le_imm, assume_ge_imm, get_interval_i64};
use crate::zone::tnum::Tnum;

/// Check if the loop body contains a conditional branch (If instruction),
/// which indicates the loop has a potential exit path.
fn loop_has_conditional_exit(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    if let Some(idx) = state.history_idx {
        let body_pcs = env.history.loop_body_pcs(idx, pc);
        for body_pc in body_pcs {
            if body_pc < prog.instrs.len() {
                if matches!(prog.instrs[body_pc], Instr::If { .. }) {
                    return true;
                }
            }
        }
    }
    // Also check the loop head itself
    if pc < prog.instrs.len() {
        if matches!(prog.instrs[pc], Instr::If { .. }) {
            return true;
        }
    }
    false
}

/// Extract loop bound from a `!= K` condition on the back-edge.
///
/// For bounded loops like `for (i = 0; i < 40; i++)`, the compiler often generates:
///   `if r != 40 goto loop_head`
///
/// On the back-edge (taken path), we know `r != K`. For an incrementing loop counter
/// starting from 0 or a small value, this means `r < K` (we haven't reached K yet).
///
/// Returns (reg, upper_bound) if a bounded loop pattern is detected.
/// Extract loop bound from a `!= K` condition.
///
/// This is called when we detect a back-edge. There are two cases:
/// 1. Back-edge at the branch instruction itself (e.g., PC 26: `if r1 != 40 goto 20`)
///    - We're re-visiting the branch, so look at the CURRENT instruction
/// 2. Back-edge at the loop head (e.g., PC 20)
///    - We jumped back, so look at the PARENT instruction (what branched here)
///
/// For bounded loops like `for (i = 0; i < 40; i++)`, the compiler generates:
///   `if r != 40 goto loop_head`
///
/// On the back-edge, we know `r != K`. For an incrementing loop counter,
/// this means `r < K`.
fn detect_loop_bound(
    env: &VerifierEnv,
    state: &State,
    current_pc: usize,
    prog: &Program,
) -> Option<(Reg, i64)> {
    // Case 1: Check if the CURRENT instruction is a `!= K` branch (back-edge at branch site)
    if current_pc < prog.instrs.len() {
        if let Instr::If { op: CmpOp::Ne, left, right: Operand::Imm(k), .. } = &prog.instrs[current_pc] {
            let (lo, _hi) = get_interval_i64(&state.dbm, *left);
            if lo >= 0 && *k > 0 {
                return Some((*left, *k - 1));
            }
        }
    }

    // Case 2: Check if we arrived via a `!= K` branch (back-edge at loop head)
    let history_idx = state.history_idx?;
    let branch_step = env.history.get(history_idx)?;
    let branch_pc = branch_step.pc;

    if branch_pc < prog.instrs.len() {
        if let Instr::If { op: CmpOp::Ne, left, right: Operand::Imm(k), target, .. } = &prog.instrs[branch_pc] {
            if *target == current_pc {
                let (lo, _hi) = get_interval_i64(&state.dbm, *left);
                if lo >= 0 && *k > 0 {
                    return Some((*left, *k - 1));
                }
            }
        }
    }

    None
}

/// Check if any conditional branch in the loop body has had its exit path
/// actually explored (i.e., the exit PC has explored states). This detects
/// cases where a conditional exit exists syntactically but is never feasible.
fn loop_exit_was_explored(env: &VerifierEnv, state: &State, pc: usize, prog: &Program) -> bool {
    // Collect loop body PCs
    let mut body_pc_set: HashSet<usize> = HashSet::new();
    body_pc_set.insert(pc); // loop head
    if let Some(idx) = state.history_idx {
        for body_pc in env.history.loop_body_pcs(idx, pc) {
            body_pc_set.insert(body_pc);
        }
    }

    // For each If instruction in the loop body, check if its exit successor
    // (the one that leaves the loop) has been explored
    for &body_pc in &body_pc_set {
        if body_pc < prog.instrs.len() {
            if let Instr::If { target, .. } = &prog.instrs[body_pc] {
                let fall_through = body_pc + 1;
                // Check if fall-through exits the loop
                if !body_pc_set.contains(&fall_through) {
                    if env.explored_states.contains_key(&fall_through) {
                        return true;
                    }
                }
                // Check if target exits the loop
                if !body_pc_set.contains(target) {
                    if env.explored_states.contains_key(target) {
                        return true;
                    }
                }
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

    // Only prune at designated prune points
    if let Some(aux) = env.insn_aux_data.get(pc) {
        if !aux.prune_point {
                    return false;
        }
    } else {
        return false;
    }

    // Check if on path (safety)
    let is_on_path = state
        .history_idx
        .map(|idx| env.history.is_on_path(idx, pc))
        .unwrap_or(false);

    // Check if in a real loop back-edge (widening)
    // Only apply widening at actual loop points, not at every instruction
    // that happens to be revisited inside a loop body.
    //
    // A loop point is either:
    // 1. A backward-jumping branch (source of back-edge): If/Jmp with target < pc
    // 2. The target of a backward jump (loop head): we arrived here via a backward jump
    //
    // We detect case 2 by checking if the previous step in history was a backward
    // jump that landed at this PC.
    let is_back_edge_pc = state
        .history_idx
        .map(|idx| env.history.is_back_edge(idx, pc, state.num_frames()))
        .unwrap_or(false);

    let is_backward_branch = if pc < prog.instrs.len() {
        match &prog.instrs[pc] {
            Instr::If { target, .. } => *target < pc,
            Instr::Jmp { target } => *target < pc,
            _ => false,
        }
    } else {
        false
    };

    // Check if we arrived at this PC via a backward jump (loop head detection)
    let arrived_via_back_edge = state.history_idx.and_then(|idx| {
        let prev_step = env.history.get(idx)?;
        let prev_pc = prev_step.pc;
        if prev_pc < prog.instrs.len() {
            match &prog.instrs[prev_pc] {
                Instr::If { target, .. } if *target == pc && prev_pc > pc => Some(true),
                Instr::Jmp { target } if *target == pc && prev_pc > pc => Some(true),
                _ => Some(false),
            }
        } else {
            Some(false)
        }
    }).unwrap_or(false);

    let in_loop = is_back_edge_pc && (is_backward_branch || arrived_via_back_edge);


    if is_on_path && !in_loop {
        // Re-entry to a PC from a different depth (e.g. repeated call in a loop).
        // Must continue analysis to reach the actual loop back-edge.
        // Do NOT prune via subsumption here as it might close a caller's loop unsoundly.
        return false;
    }

    let live_regs = &env.insn_aux_data[pc].live_regs;

    if in_loop {
        // Only apply widening if the loop has a conditional exit (If instruction).
        // Loops without conditional exits are infinite and should be rejected
        // by the complexity limit.
        if !loop_has_conditional_exit(env, state, pc, prog) {
            return false;
        }

        // Bounded loop detection: extract upper bound from `!= K` condition
        let loop_bound = detect_loop_bound(env, state, pc, prog);

        // Apply the loop bound to the CURRENT state BEFORE subsumption check.
        // This is crucial because the state arriving at the branch point may have
        // bounds that exceed the loop limit (e.g., after increment: [2, 40]).
        // Applying the bound first constrains it to [2, 39] so subsumption can succeed.
        //
        // IMPORTANT: Only apply if it doesn't make the DBM inconsistent.
        // If the current state already has r > upper_bound, applying the bound
        // would create a contradiction. In that case, skip the bound application.
        if let Some((reg, upper_bound)) = loop_bound {
            let (cur_lo, _) = get_interval_i64(&state.dbm, reg);
            if cur_lo <= upper_bound {
                assume_le_imm(&mut state.dbm, reg, upper_bound);
                assume_ge_imm(&mut state.dbm, reg, 0);
                // Also set tnum to unknown for convergence check
                state.set_tnum(reg, Tnum::UNKNOWN);
            }
        }

        // Loop convergence via widening:
        // 1. Apply widening to over-approximate the state (ensures termination).
        // 2. On subsequent visits, check if the current state is subsumed
        //    by the last explored (widened) state → convergence.
        // 3. Only allow convergence if widening actually expanded the state
        //    (indicating the loop makes progress and the exit path was explored
        //    with the widened state). Stagnant loops (no change) are infinite.
        if let Some(prev_states) = env.explored_states.get(&pc) {
            if let Some(old) = prev_states.last() {
                // Check convergence: is current state subsumed by last explored?
                let types_ok = types_subsumed_by(&state.types, &old.types, live_regs);
                let dbm_ok = config.skip_dbm_check || dbm_subsumed_by(&state.dbm, &old.dbm, live_regs);
                let stack_ok = stack_subsumed_by(state, old);
                let tnum_ok = tnum_subsumed_by(state, old, live_regs);
                if state_subsumed_by(state, old, live_regs, config) {
                    // Only converge if:
                    // 1. Widening was applied (prev_states >= 2)
                    // 2. Widening was effective (bounds actually expanded
                    //    compared to the first visit)
                    // 3. An exit path from the loop was actually explored
                    if prev_states.len() >= 2 {
                        let first = &prev_states[0];
                        let widening_effective = live_regs.iter().any(|&r| {
                            let (first_min, first_max) = get_interval_i64(&first.dbm, r);
                            let (last_min, last_max) = get_interval_i64(&old.dbm, r);
                            last_min < first_min || last_max > first_max
                        });

                        // For bounded loops, we don't need to wait for exit exploration.
                        // The bound detection itself proves the exit exists and will be reached.
                        // For unbounded loops, we require the exit to be explored.
                        let exit_ok = loop_bound.is_some() || loop_exit_was_explored(env, state, pc, prog);

                        if widening_effective && exit_ok {
                            return true; // Converged with verified exit path
                        }
                    }
                    // Widening not effective or no exit path →
                    // loop may be infinite, let complexity limit catch it
                    return false;
                }

                // Not converged: apply widening
                let widened_dbm = old.dbm.widen(&state.dbm);
                state.dbm = widened_dbm;

                // Re-apply the loop bound after widening (widening may have expanded it)
                if let Some((reg, upper_bound)) = loop_bound {
                    assume_le_imm(&mut state.dbm, reg, upper_bound);
                    assume_ge_imm(&mut state.dbm, reg, 0);
                    // For bounded loop counters, set tnum to fully unknown within the bound.
                    // This ensures tnum convergence by not tracking exact bit patterns.
                    state.set_tnum(reg, Tnum::UNKNOWN);
                }

                // Widen Tnums for all live registers to guarantee convergence
                // Use aggressive widening: if the tnum changed, set to UNKNOWN.
                // This ensures fast convergence for loops.
                for &r in live_regs {
                    let old_t = old.get_tnum(r);
                    let cur_t = state.get_tnum(r);
                    if old_t != cur_t {
                        // Tnum changed - widen to unknown for fast convergence
                        state.set_tnum(r, Tnum::UNKNOWN);
                    }
                }
            }
        }
        return false;
    }

    // Non-loop: standard subsumption check
    if let Some(prev_states) = env.explored_states.get(&pc) {
        for prev in prev_states {
            if state_subsumed_by(state, prev, live_regs, config) {
                return true;
            }
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
    } else {
        if !(types_subsumed_by(&cur.types, &old.types, live_regs)
            && dbm_subsumed_by(&cur.dbm, &old.dbm, live_regs)
            && stack_subsumed_by(cur, old)
            && tnum_subsumed_by(cur, old, live_regs))
        {
            return false;
        }
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
        if !config.skip_dbm_check {
            if !dbm_subsumed_by(&cur_frame.caller_dbm, &old_frame.caller_dbm, &saved) {
                return false;
            }
        }
        if !caller_tnum_subsumed_by(cur_frame, old_frame, &saved) {
            return false;
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

        // Different types - no subsumption
        _ => false,
    }
}

/// Check if cur DBM is subsumed by old DBM.
fn dbm_subsumed_by(cur: &Dbm, old: &Dbm, live_regs: &HashSet<Reg>) -> bool {
    for &r in live_regs {
        let (old_min, old_max) = get_interval_i64(old, r);
        let (cur_min, cur_max) = get_interval_i64(cur, r);
        if !(old_min <= cur_min && old_max >= cur_max) {
            return false;
        }
    }

    // Anchor-to-anchor constraints (packet bounds) must also be subsumed.
    // These represent relationships like data_end - data >= N that are
    // critical for packet access safety and persist across calls.
    let anchors = [Reg::AnchorData, Reg::AnchorDataEnd, Reg::AnchorDataMeta];
    for &a in &anchors {
        for &b in &anchors {
            if a == b {
                continue;
            }
            // old must be at least as permissive: old.get(a,b) >= cur.get(a,b)
            if old.get(a, b) < cur.get(a, b) {
                return false;
            }
        }
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
        }
    }
    true
}

fn tnum_subsumed_by(cur_state: &State, old_state: &State, live_regs: &HashSet<Reg>) -> bool {
    for &r in live_regs {
        let cur = cur_state.get_tnum(r);
        let old = old_state.get_tnum(r);
        if !tnum_covers(&cur, &old) {
            return false;
        }
    }
    true
}

/// Check if old tnum covers cur tnum (old's possible values are a superset of cur's).
fn tnum_covers(cur: &crate::zone::tnum::Tnum, old: &crate::zone::tnum::Tnum) -> bool {
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
