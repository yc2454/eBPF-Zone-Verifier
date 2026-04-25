// src/analysis/transfer/call/side_effects.rs
//
// Shared post-call applier (Phase 4 W4.1b).
//
// Reads `CallProto.ret`, `CallProto.flags`, and `CallProto.side_effects`
// to drive R0 typing and ref-tracking. Replaces the per-helper-id arms
// in `update_call_types` for migrated helpers; once Phase 4 W4.1c is
// done, kfuncs will plug into the same applier through a parallel
// proto producer in `signatures::kfuncs`.

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;

use super::signatures::{CallFlags, CallProto, RetKind, SideEffect};

/// Drive R0 typing + ref-tracking + side effects from `proto`.
///
/// Returns `true` if the proto carried enough information to set R0
/// (i.e. `RetKind != Unknown`). When it returns `false` the caller
/// should fall back to the legacy per-helper-id logic in
/// `update_call_types`.
pub(crate) fn apply_call_proto_r0(
    in_types: &TypeState,
    state: &mut State,
    proto: &CallProto,
) -> bool {
    // ReleaseRefFromArg fires before R0 typing because the released
    // ref-id might be the one we'd otherwise read (defensive ordering;
    // socket-release helpers don't return the released ref).
    for eff in proto.side_effects {
        match *eff {
            SideEffect::ReleaseRefFromArg { arg } => {
                let reg = arg_reg(arg);
                // Read from in_types: by the time the applier runs,
                // caller-saved registers may already have been clobbered
                // upstream. The kernel verifier likewise consults the
                // pre-call type for the release target.
                if let Some(ref_id) = in_types.get(reg).get_ref_id() {
                    state.release_ref(ref_id);
                    state.invalidate_ref(ref_id);
                }
            }
        }
    }

    match proto.ret {
        RetKind::Unknown => false,
        RetKind::Void | RetKind::Scalar => {
            state.types.set(Reg::R0, RegType::ScalarValue);
            true
        }
        RetKind::PtrToSocket => {
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToSocketOrNull { ref_id }
            } else {
                // No nullable wrapping: panic-safe fallback to ref-bearing socket.
                // None of the migrated helpers today take this branch.
                RegType::PtrToSocket { ref_id }
            };
            state.types.set(Reg::R0, ty);
            true
        }
        RetKind::PtrToSockCommon => {
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToSockCommonOrNull { ref_id }
            } else {
                RegType::PtrToSockCommon { ref_id }
            };
            state.types.set(Reg::R0, ty);
            true
        }
    }
}

/// Map a 0-indexed arg slot (0..=4) to its register (R1..R5).
fn arg_reg(arg: u8) -> Reg {
    match arg {
        0 => Reg::R1,
        1 => Reg::R2,
        2 => Reg::R3,
        3 => Reg::R4,
        4 => Reg::R5,
        _ => panic!("CallProto side-effect arg index {arg} out of range"),
    }
}
