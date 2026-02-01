// src/analysis/pruning.rs

use std::collections::HashSet;

use crate::analysis::env::VerifierEnv;
use crate::analysis::reg_types::{RegType, TypeState};
use crate::analysis::state::State;
use crate::common::config::VerifierConfig;
use crate::zone::dbm::Dbm;
use crate::zone::domain::Reg;

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

/// Check if `cur` is subsumed by `old` (old covers all behaviors of cur).
fn state_subsumed_by(
    cur: &State,
    old: &State,
    live_regs: &HashSet<Reg>,
    config: &VerifierConfig,
) -> bool {
    if config.skip_dbm_check {
        types_subsumed_by(&cur.types, &old.types, live_regs)
    } else {
        types_subsumed_by(&cur.types, &old.types, live_regs)
            && dbm_subsumed_by(&cur.dbm, &old.dbm, live_regs)
    }
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
        (_, NotInit) => true,

        // Packet pointers: old must have >= range
        (
            PtrToPacket { is_base: b1, .. },
            PtrToPacket { is_base: b2, .. },
        ) => b1 == b2,

        // Mem pointers: old must have >= range
        (
            PtrToMem { region: reg1, range: r1 },
            PtrToMem { region: reg2, range: r2 },
        ) => reg1 == reg2 && r1 >= r2,

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
        (PtrToSocket { id: id1 }, PtrToSocket { id: id2 }) => id1 == id2,
        (PtrToSocketOrNull { id: id1 }, PtrToSocketOrNull { id: id2 }) => id1 == id2,

        // Stack pointers
        (
            PtrToStack { offset: o1 },
            PtrToStack { offset: o2 },
        ) => match (o1, o2) {
            (None, _) => true,
            (Some(a), Some(b)) => a == b,
            (Some(_), None) => false,
        },

        // Different types - no subsumption
        _ => false,
    }
}

/// Check if cur DBM is subsumed by old DBM.
fn dbm_subsumed_by(cur: &Dbm, old: &Dbm, live_regs: &HashSet<Reg>) -> bool {
    let zero_idx = 0;

    for &r in live_regs {
        let r_idx = r.idx();

        // old subsumes cur if old has >= bounds (less constrained)
        if old.get_idx(r_idx, zero_idx) < cur.get_idx(r_idx, zero_idx) {
            return false;
        }
        if old.get_idx(zero_idx, r_idx) < cur.get_idx(zero_idx, r_idx) {
            return false;
        }
    }

    true
}
