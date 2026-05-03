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
///
/// Enforces max_states_per_pc limit by removing oldest states when
/// exceeded. Returns the freshly-minted `cache_id` for the cached
/// clone — callers should store this as the continuing state's
/// `parent_cache_id` so the per-path precision walker can find this
/// cached state as the path's most recent predecessor.
///
/// Kernel-aligned: under the kernel-precision regime, also clears
/// inherited precision marks on the cached clone (mirrors
/// `mark_all_scalars_imprecise` at checkpoint, verifier.c v6.15
/// L4543). Precision is then re-established on demand via
/// `propagate_precision` walking the per-path parent-cache-id chain.
pub fn record_state(
    env: &mut VerifierEnv,
    mut state: State,
    max_states_per_pc: usize,
) -> u32 {
    let pc = state.pc;

    let cache_id = env.next_cache_id;
    env.next_cache_id = env.next_cache_id.wrapping_add(1);
    state.cache_id = Some(cache_id);

    if crate::analysis::machine::env::kernel_precision_enabled() {
        state.mark_all_scalars_imprecise();
    }

    let states = env.explored_states.entry(pc).or_default();
    let idx = states.len();
    states.push(state);
    env.cache_loc_by_id.insert(cache_id, (pc, idx));

    // Bucket F-A: parallel metrics vector. Same indices as states.
    let metrics = env
        .state_metrics
        .entry(pc)
        .or_default();
    metrics.push(crate::analysis::machine::env::StateMetrics::default());

    // Enforce limit: keep only the most recent states. Apply the same
    // drain to `state_metrics` so the two vectors stay aligned. Keep
    // `cache_loc_by_id` consistent: the drained entries' cache_ids no
    // longer have a valid (pc, idx) location, so remove them; the
    // surviving entries shift left by `excess`, so update their idx.
    if max_states_per_pc > 0 && states.len() > max_states_per_pc {
        let excess = states.len() - max_states_per_pc;
        // Collect cache_ids of evicted (front) and surviving entries.
        let evicted_ids: Vec<u32> = states
            .iter()
            .take(excess)
            .filter_map(|s| s.cache_id)
            .collect();
        let surviving_ids: Vec<u32> = states
            .iter()
            .skip(excess)
            .filter_map(|s| s.cache_id)
            .collect();
        states.drain(0..excess);
        metrics.drain(0..excess);
        for id in evicted_ids {
            env.cache_loc_by_id.remove(&id);
        }
        for (new_idx, id) in surviving_ids.iter().enumerate() {
            env.cache_loc_by_id.insert(*id, (pc, new_idx));
        }
    }

    cache_id
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
            // PtrToBtfId is a kernel BTF-typed pointer; field loads are
            // bounds-validated against the type's BTF. When two paths
            // reach the same PC with one producing PtrToStack and another
            // producing PtrToBtfId (typical of `__noinline static`
            // subprogs called from both main and a timer/wq async cb,
            // see verifier_private_stack.c::private_stack_async_callback_2),
            // each path's body verifies independently against its own
            // type — no need to demote to Scalar. The kernel achieves the
            // same by re-verifying the subprog separately for each
            // distinct caller-state shape (`push_async_cb` makes the cb
            // a separate verifier root).
            | PtrToBtfId { .. }
    )
}

/// Check if a type can be used as a map pointer. PtrToMapValue is included because
/// it can represent a pointer to an inner map in an array-of-maps or hash-of-maps.
fn is_map_ptr(ty: &RegType) -> bool {
    use RegType::*;
    matches!(ty, PtrToMapObject { .. } | PtrToMapValue { .. })
}
