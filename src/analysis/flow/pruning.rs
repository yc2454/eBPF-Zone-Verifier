// src/analysis/flow/pruning.rs
//
// State pruning: determines whether a new state is already covered by a
// previously explored state, so the verifier can skip redundant paths.
//
// Changes from previous version:
//   - stack_subsumed_by now takes `live_slots` and only compares slots that are
//     actually live (read downstream).
//   - For live slots, it checks BOTH type subsumption AND scalar bounds subsumption.
//     This prevents pruning when two paths spill different scalar values to the same
//     stack slot (e.g., Test 2: value 0 vs value 1 at [R10-16]).
//   - dbm_subsumed_by loop fix: was using `return` instead of `continue`.

use std::collections::HashSet;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::stack_state::SpilledReg;
use crate::analysis::machine::state::State;
use crate::common::config::VerifierConfig;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{Reg, get_simple_bounds};

/// Check if we should prune this state (already covered by a previous exploration).
pub fn should_prune(
    env: &VerifierEnv,
    state: &State,
    config: &VerifierConfig,
) -> bool {
    let pc = state.pc;

    // Only prune at designated prune points
    let aux = match env.insn_aux_data.get(pc) {
        Some(aux) if aux.prune_point => aux,
        _ => return false,
    };

    // Check if in a loop (don't prune loop iterations)
    let in_loop = state.history_idx
        .map(|idx| env.history.path_contains_pc(idx, pc))
        .unwrap_or(false);

    if in_loop {
        return false;
    }

    // Check subsumption against all explored states at this PC
    let live_regs = &aux.live_regs;
    let live_slots = &aux.live_slots;

    if let Some(prev_states) = env.explored_states.get(&pc) {
        for prev in prev_states {
            if state_subsumed_by(state, prev, live_regs, live_slots, config) {
                return true;
            }
        }
    }

    false
}

/// Check if `cur` is subsumed by `old` (old covers all behaviors of cur).
fn state_subsumed_by(
    cur: &State,
    old: &State,
    live_regs: &HashSet<Reg>,
    live_slots: &HashSet<i16>,
    config: &VerifierConfig,
) -> bool {
    // 1. Register types (only live registers)
    if !types_subsumed_by(&cur.types, &old.types, live_regs) {
        return false;
    }

    // 2. Stack (only live slots — type + value)
    if !stack_subsumed_by(cur, old, live_slots) {
        return false;
    }

    // 3. DBM (numerical bounds for live registers)
    if !config.skip_dbm_check {
        if !dbm_subsumed_by(&cur.dbm, &old.dbm, live_regs) {
            return false;
        }
    }

    true
}

// ---------- Register Type Subsumption ----------

/// Check if cur types are subsumed by old types (only for live registers).
fn types_subsumed_by(
    cur: &TypeState,
    old: &TypeState,
    live_regs: &HashSet<Reg>,
) -> bool {
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
        (_, NotInit) => true,

        // Packet pointers: old must have >= range
        (
            PtrToPacket { is_base: b1, range: old_range, .. },
            PtrToPacket { is_base: b2, range: cur_range, .. },
        ) => b1 == b2 && old_range >= cur_range,

        // Map value pointers
        (
            PtrToMapValue { offset: o1, map_idx: m1, .. },
            PtrToMapValue { offset: o2, map_idx: m2, .. },
        ) => {
            m1 == m2 && match (o1, o2) {
                (None, _) => true,
                (Some(a), Some(b)) => a == b,
                (Some(_), None) => false,
            }
        }

        // Map value or null
        (
            PtrToMapValueOrNull { id: id1, map_idx: m1 },
            PtrToMapValueOrNull { id: id2, map_idx: m2 },
        ) => m1 == m2 && id1 == id2,

        // Socket pointers
        (PtrToSocket { ref_id: id1 }, PtrToSocket { ref_id: id2 }) => id1 == id2,
        (PtrToSocketOrNull { ref_id: id1 }, PtrToSocketOrNull { ref_id: id2 }) => id1 == id2,

        // Stack pointers
        (
            PtrToStack { offset: o1, frame_level: fl1 },
            PtrToStack { offset: o2, frame_level: fl2 },
        ) => match (o1, o2) {
            (None, _) => fl1 == fl2,
            (Some(a), Some(b)) => a == b && fl1 == fl2,
            (Some(_), None) => false,
        },

        // Different types - no subsumption
        _ => false,
    }
}

// ---------- DBM (Numerical Bounds) Subsumption ----------

/// Check if cur DBM is subsumed by old DBM (only for live registers).
fn dbm_subsumed_by(cur: &Dbm, old: &Dbm, live_regs: &HashSet<Reg>) -> bool {
    for &r in live_regs {
        let (old_min, old_max) = get_simple_bounds(old, r);
        let (cur_min, cur_max) = get_simple_bounds(cur, r);
        // FIX: was `return` — must check ALL live regs, not just the first.
        if !(old_min <= cur_min && old_max >= cur_max) {
            return false;
        }
    }
    true
}

// ---------- Stack Subsumption ----------

/// Check if cur's stack is subsumed by old's stack.
///
/// Only compares stack slots that are LIVE at this program point.
/// For each live slot, checks both:
///   1. Type subsumption (e.g., PtrToMapValue vs ScalarValue)
///   2. Scalar bounds subsumption (old's range must cover cur's range)
///
/// This prevents pruning when two paths spill different scalar values
/// to the same live slot (the key fix for the "search pruning" test).
fn stack_subsumed_by(
    cur: &State,
    old: &State,
    live_slots: &HashSet<i16>,
) -> bool {
    // Must have the same call depth
    if cur.call_stack.len() != old.call_stack.len() {
        return false;
    }

    for (frame_idx, (old_frame, cur_frame)) in old.call_stack.iter()
        .zip(cur.call_stack.iter())
        .enumerate()
    {
        // For the current (top) frame, use liveness-guided comparison.
        // For caller frames saved on the call stack, we need to compare all
        // occupied slots since we don't have per-frame liveness for saved frames.
        let is_current_frame = frame_idx == cur.call_stack.len() - 1;

        if is_current_frame {
            // Only compare live slots
            for &offset in live_slots {
                if !spilled_slot_subsumed(
                    cur_frame.stack.get_slot(offset),
                    old_frame.stack.get_slot(offset),
                ) {
                    return false;
                }
            }
        } else {
            // Caller frame: compare all occupied slots from both frames
            let all_offsets: HashSet<i16> = old_frame.stack.slot_offsets().into_iter()
                .chain(cur_frame.stack.slot_offsets())
                .collect();

            for offset in all_offsets {
                if !spilled_slot_subsumed(
                    cur_frame.stack.get_slot(offset),
                    old_frame.stack.get_slot(offset),
                ) {
                    return false;
                }
            }
        }
    }
    true
}

/// Check if a single spilled slot in cur is subsumed by the corresponding slot in old.
///
/// For subsumption to hold:
///   - Types must be compatible (via type_subsumed_by)
///   - For scalar slots, old's bounds must cover cur's bounds (wider range = more general)
///   - For pointer slots, the types already encode the relevant info
fn spilled_slot_subsumed(
    cur_slot: Option<&SpilledReg>,
    old_slot: Option<&SpilledReg>,
) -> bool {
    match (old_slot, cur_slot) {
        // Both uninitialized — trivially subsumed
        (None, None) => true,

        // Old has data, cur is uninitialized — cur is "less defined", subsumed
        (Some(_), None) => true,

        // Old is uninitialized but cur has data — NOT subsumed.
        // The old state would treat this as uninitialized, but cur's path
        // depends on the spilled value. Cannot prune.
        (None, Some(_)) => false,

        // Both initialized — compare type and value
        (Some(old_spill), Some(cur_spill)) => {
            // 1. Type must be subsumed
            if !type_subsumed_by(&cur_spill.reg_type, &old_spill.reg_type) {
                return false;
            }

            // 2. For scalar values, bounds must be subsumed (old covers cur)
            if matches!(old_spill.reg_type, RegType::ScalarValue)
                && matches!(cur_spill.reg_type, RegType::ScalarValue)
            {
                if !(old_spill.bounds.min <= cur_spill.bounds.min
                    && old_spill.bounds.max >= cur_spill.bounds.max)
                {
                    return false;
                }
            }

            true
        }
    }
}
