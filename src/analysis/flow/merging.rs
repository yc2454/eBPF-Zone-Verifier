// src/analysis/merging.rs
//
// Handles type conflict resolution at control flow merge points.
//
// When different paths reach the same PC with different pointer types for
// the same register, we use "deferred checking":
//   1. Instead of failing immediately, demote conflicting registers to ScalarValue
//   2. Continue exploration
//   3. If the register is later used as a pointer (load/store base), validation fails
//   4. If it's just returned or used arithmetically, it's fine
//
// This matches kernel verifier behavior more closely and handles cases like
// function return values that have different types on different paths but
// are never used as pointers after the merge.

use std::collections::HashSet;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg_types::{RegType, type_family};
use crate::analysis::machine::state::State;

/// Resolve type conflicts at a merge point by demoting conflicting registers to ScalarValue.
/// This implements "deferred checking" - we don't fail here, but the demoted register
/// will cause failures if later used as a pointer.
pub fn resolve_type_conflicts(env: &VerifierEnv, state: &mut State) {
    let pc = state.pc;

    let live_regs = env
        .insn_aux_data
        .get(pc)
        .map(|aux| &aux.live_regs)
        .cloned()
        .unwrap_or_default();

    if let Some(prev_states) = env.explored_states.get(&pc) {
        for prev in prev_states {
            // Find conflicting registers and demote them
            for &r in &live_regs {
                let old_ty = prev.types.get(r);
                let new_ty = state.types.get(r);
                if !types_compatible(&old_ty, &new_ty) {
                    // Demote to ScalarValue - this will cause failure if used as pointer
                    state.types.set(r, RegType::ScalarValue);
                }
            }

            // Also check stack slots and demote conflicting ones
            for (prev_frame, cur_frame) in prev.frames.iter().zip(state.frames.iter_mut()) {
                let live_offsets: HashSet<i16> = prev_frame
                    .stack
                    .live_slot_offsets(&live_regs)
                    .into_iter()
                    .chain(cur_frame.stack.live_slot_offsets(&live_regs))
                    .collect();

                for offset in live_offsets {
                    let old_ty = prev_frame.stack.get_slot_type(offset);
                    let new_ty = cur_frame.stack.get_slot_type(offset);
                    if !types_compatible(&old_ty, &new_ty) {
                        // Demote stack slot to ScalarValue
                        cur_frame.stack.demote_slot_to_scalar(offset);
                    }
                }
            }
        }
    }
}

/// Record a state as explored at its PC.
/// Enforces max_states_per_pc limit by removing oldest states when exceeded.
pub fn record_state(env: &mut VerifierEnv, state: State, max_states_per_pc: usize) {
    let states = env.explored_states.entry(state.pc).or_default();
    states.push(state);

    // Enforce limit: keep only the most recent states
    if max_states_per_pc > 0 && states.len() > max_states_per_pc {
        let excess = states.len() - max_states_per_pc;
        states.drain(0..excess);
    }
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
    // Different readable pointer types are compatible - each path will be
    // validated independently. This handles cases like `twotypes` where a
    // register can be either PtrToStack or PtrToMapValue depending on the path.
    // We don't demote to ScalarValue because both are valid for memory access.
    || (is_readable_ptr(a) && is_readable_ptr(b))
    // Map objects and inner map pointers (represented as PtrToMapValue) are both
    // valid map pointer arguments, so they shouldn't demote each other to Scalar.
    || (is_map_ptr(a) && is_map_ptr(b))
}

/// Check if a type is a general-purpose readable pointer that can safely merge
/// with other readable pointers at join points.
///
/// NOTE: PtrToCtx is intentionally EXCLUDED because ctx pointers have special
/// field-based access rules that differ from regular memory pointers. Merging
/// a ctx pointer with a map value pointer could allow unsafe ctx field access.
fn is_readable_ptr(ty: &RegType) -> bool {
    use RegType::*;
    matches!(
        ty,
        PtrToStack { .. }
            | PtrToMapValue { .. }
            | PtrToPacket
            | PtrToPacketMeta
            | PtrToAllocMem { .. }
            | PtrToArena { .. }
    )
}

/// Check if a type can be used as a map pointer. PtrToMapValue is included because
/// it can represent a pointer to an inner map in an array-of-maps or hash-of-maps.
fn is_map_ptr(ty: &RegType) -> bool {
    use RegType::*;
    matches!(ty, PtrToMapObject { .. } | PtrToMapValue { .. })
}
