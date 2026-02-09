// src/analysis/merging.rs

use std::collections::HashSet;

use crate::analysis::machine::env::{VerificationError, VerifierEnv};
use crate::analysis::machine::reg_types::{RegType, TypeState};
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
        let all_offsets: HashSet<i16> = old_frame.stack.slot_offsets().into_iter()
            .chain(new_frame.stack.slot_offsets())
            .collect();

        for offset in all_offsets {
            let old_ty = old_frame.stack.get_slot_type(offset);
            let new_ty = new_frame.stack.get_slot_type(offset);
            if !types_compatible(&old_ty, &new_ty) {
                // You may want a different error variant for stack conflicts
                return Some((Reg::R0, old_ty, new_ty));
            }
        }
    }

    None
}

/// Check if two types are compatible (same kind, could coexist at join point).
/// This is different from subsumption - we just check if they're the same "family".
fn types_compatible(a: &RegType, b: &RegType) -> bool {
    use RegType::*;
    
    match (a, b) {
        // NotInit is compatible with anything (dead register)
        (NotInit, _) | (_, NotInit) => true,
        
        // Same type families are compatible
        (ScalarValue, ScalarValue) => true,
        (PtrToCtx, PtrToCtx) => true,
        (PtrToStack { .. }, PtrToStack { .. }) => true,
        (PtrToMapValue { .. }, PtrToMapValue { .. }) => true,
        (PtrToMapValueOrNull { .. }, PtrToMapValueOrNull { .. }) => true,
        (PtrToMapValue { id: id1, .. }, PtrToMapValueOrNull { id: id2, .. }) 
        | (PtrToMapValueOrNull { id: id1, .. }, PtrToMapValue { id: id2, .. }) => id1 == id2,
        (PtrToMapValueOrNull { .. }, ScalarValue) => true,
        (PtrToMapObject { map_idx: _id1 }, PtrToMapObject { map_idx: _id2 }) => true,
        (ScalarValue, PtrToMapValueOrNull { .. }) => true,
        (PtrToPacket { .. }, PtrToPacket { .. }) => true,
        (PtrToPacketEnd, PtrToPacketEnd) => true,
        (PtrToSocket { .. }, PtrToSocket { .. }) => true,
        (PtrToSocketOrNull { .. }, PtrToSocketOrNull { .. }) => true,
        (PtrToSockCommon { .. }, PtrToSockCommon { .. }) => true,
        (PtrToSockCommonOrNull { .. }, PtrToSockCommonOrNull { .. }) => true,
        (PtrToTcpSock { .. }, PtrToTcpSock { .. }) => true,
        (PtrToTcpSockOrNull { .. }, PtrToTcpSockOrNull { .. }) => true,
        (PtrToSocketOrNull { ref_id: id1 }, PtrToSocket { ref_id: id2 }) 
        | (PtrToSocket { ref_id: id1 }, PtrToSocketOrNull { ref_id: id2 }) => id1 == id2,
        (PtrToSocket { .. }, ScalarValue) => true,
        (ScalarValue, PtrToSocket { .. }) => true,
        (PtrToMapValue { .. }, ScalarValue) => true,
        (ScalarValue, PtrToMapValue { .. }) => true,
        (PtrToPacket { .. }, ScalarValue) => true,
        (ScalarValue, PtrToPacket { .. }) => true,
        // Different type families = incompatible
        _ => false,
    }
}