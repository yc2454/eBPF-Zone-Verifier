// src/analysis/pruning.rs

use std::collections::HashSet;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::common::config::VerifierConfig;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{Reg, get_simple_bounds};
use crate::zone::tnum::Tnum;

/// Check if we should prune this state (already covered by a previous exploration).
pub fn should_prune(
    env: &VerifierEnv,
    state: &State,
    config: &VerifierConfig,
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

    // Check if in a loop (don't prune loop iterations)
    let in_loop = state.history_idx
        .map(|idx| env.history.path_contains_pc(idx, pc))
        .unwrap_or(false);
    
    if in_loop {
        return false;
    }

    // Check subsumption against all explored states at this PC
    let live_regs = &env.insn_aux_data[pc].live_regs;
    
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
        println!("Pruning check (skip DBM): type: {}, Stack: {}", 
            types_subsumed_by(&cur.types, &old.types, live_regs),
            stack_subsumed_by(cur, old));
        if !(types_subsumed_by(&cur.types, &old.types, live_regs)
            && stack_subsumed_by(cur, old)
            && tnum_subsumed_by(cur, old, live_regs))
        {
            return false;
        }
    } else {
        println!("Pruning check: type: {}, Stack: {}", 
            types_subsumed_by(&cur.types, &old.types, live_regs),
            stack_subsumed_by(cur, old));
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
    for (cur_frame, old_frame) in cur.frames.iter()
        .zip(old.frames.iter())
    {
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
        (NotInit, _) => true,

        // Packet pointers: old must have >= range
        (
            PtrToPacket,
            PtrToPacket,
        ) => true,

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

/// Check if cur DBM is subsumed by old DBM.
fn dbm_subsumed_by(cur: &Dbm, old: &Dbm, live_regs: &HashSet<Reg>) -> bool {

    for &r in live_regs {
        let (old_min, old_max) = get_simple_bounds(old, r);
        let (cur_min, cur_max) = get_simple_bounds(cur, r);
        if !(old_min <= cur_min && old_max >= cur_max) {
            return false;
        }
    }

    true
}

fn stack_subsumed_by(cur: &State, old: &State) -> bool {
    for (old_frame, new_frame) in old.frames.iter()
        .zip(cur.frames.iter())
    {
        let all_offsets: HashSet<i16> = old_frame.stack.slot_offsets().into_iter()
            .chain(new_frame.stack.slot_offsets())
            .collect();

        for offset in all_offsets {
            let old_ty = old_frame.stack.get_slot_type(offset);
            let new_ty = new_frame.stack.get_slot_type(offset);
            println!("[State subsumption check] Checking offset {}: {:?} vs {:?}", offset, old_ty, new_ty);
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
        let cur = cur_frame.caller_tnums.get(&r).copied().unwrap_or(Tnum::UNKNOWN);
        let old = old_frame.caller_tnums.get(&r).copied().unwrap_or(Tnum::UNKNOWN);
        if !tnum_covers(&cur, &old) {
            return false;
        }
    }
    true
}
