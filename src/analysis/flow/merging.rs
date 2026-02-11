// src/analysis/merging.rs

use std::collections::HashSet;

use crate::analysis::machine::env::{VerificationError, VerifierEnv};
use crate::analysis::machine::reg_types::{RegType, TypeState, type_family};
use crate::analysis::machine::state::State;
use crate::zone::domain::Reg;

/// Check if `state` is type-compatible with all previously explored states at the same PC.
/// Returns Err if types conflict (different pointer kinds at join point).
pub fn check_compatibility(
    env: &VerifierEnv,
    state: &State,
) -> Result<(), VerificationError> {
    let pc = state.pc;
    
    let live_regs = env.insn_aux_data
        .get(pc)
        .map(|aux| &aux.live_regs)
        .cloned()
        .unwrap_or_default();

    if let Some(prev_states) = env.explored_states.get(&pc) {
        for prev in prev_states {
            if let Some((reg, old_ty, new_ty)) = 
                find_type_conflict(&prev.types, &state.types, prev, state, &live_regs) {
                return Err(VerificationError::RegisterTypeConflict { pc, reg, old: old_ty, new: new_ty });
            }
        }
    }

    Ok(())
}

/// Record a state as explored at its PC.
pub fn record_state(env: &mut VerifierEnv, state: State) {
    env.explored_states
        .entry(state.pc)
        .or_default()
        .push(state);
}

/// Find the first type conflict between two type states.
/// Returns Some((reg, old_type, new_type)) if conflict found.
fn find_type_conflict(
    old: &TypeState,
    new: &TypeState,
    old_state: &State,
    new_state: &State,
    live_regs: &HashSet<Reg>,
) -> Option<(Reg, RegType, RegType)> {
    // Existing register check
    for &r in live_regs {
        let old_ty = old.get(r);
        let new_ty = new.get(r);
        if !types_compatible(&old_ty, &new_ty) {
            return Some((r, old_ty, new_ty));
        }
    }

    // Check stack slots across all frames
    for (_frame_idx, (old_frame, new_frame)) in old_state.call_stack.iter()
        .zip(new_state.call_stack.iter())
        .enumerate()
    {
        // println!("Live regs: {:?}", live_regs);
        let live_offsets: HashSet<i16> = old_frame.stack.live_slot_offsets(live_regs).into_iter()
            .chain(new_frame.stack.live_slot_offsets(live_regs))
            .collect();

        for offset in live_offsets {
            let old_ty = old_frame.stack.get_slot_type(offset);
            let new_ty = new_frame.stack.get_slot_type(offset);
            if !types_compatible(&old_ty, &new_ty) {
                // Can recover the actual reg from either side
                let reg = old_frame.stack.get_slot(offset)
                    .or_else(|| new_frame.stack.get_slot(offset))
                    .and_then(|s| s.source_reg)
                    .unwrap_or(Reg::R0);
                return Some((reg, old_ty, new_ty));
            }
        }
    }

    None
}

/// Check if two types are compatible at a join point.
/// This isn't subsumption — it just asks whether two different paths
/// reaching the same PC could legitimately produce these types.
fn types_compatible(a: &RegType, b: &RegType) -> bool {
    use RegType::*;

    // NotInit is compatible with anything (dead register, never read)
    matches!(a, NotInit) || matches!(b, NotInit)
    // ScalarValue is compatible with any type: null checks turn
    // pointer-or-null into scalar 0, arithmetic can yield scalars
    // from pointers, etc. This is the normal result of branching.
    || matches!(a, ScalarValue) || matches!(b, ScalarValue)
    // Same family is always compatible (e.g. PtrToMapValue with
    // PtrToMapValueOrNull, PtrToSocket with PtrToSocketOrNull)
    || type_family(a) == type_family(b)
}
