// src/analysis/merging.rs

use std::collections::HashSet;

use crate::analysis::env::{VerificationError, VerifierEnv};
use crate::analysis::reg_types::RegType;
use crate::analysis::state::State;
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
            if let Some((reg, old_ty, new_ty)) = find_type_conflict(&prev.types, &state.types, &live_regs) {
                return Err(VerificationError::RegisterTypeConflict { pc });
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
    old: &crate::analysis::reg_types::TypeState,
    new: &crate::analysis::reg_types::TypeState,
    live_regs: &HashSet<Reg>,
) -> Option<(Reg, RegType, RegType)> {
    for &r in live_regs {
        let old_ty = old.get(r);
        let new_ty = new.get(r);
        
        if !types_compatible(&old_ty, &new_ty) {
            return Some((r, old_ty, new_ty));
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
        (PtrToPacket { .. }, PtrToPacket { .. }) => true,
        (PtrToPacketEnd, PtrToPacketEnd) => true,
        (PtrToMem { .. }, PtrToMem { .. }) => true,
        (PtrToSocket { .. }, PtrToSocket { .. }) => true,
        (PtrToSocketOrNull { .. }, PtrToSocketOrNull { .. }) => true,
        
        // Different type families = incompatible
        _ => false,
    }
}