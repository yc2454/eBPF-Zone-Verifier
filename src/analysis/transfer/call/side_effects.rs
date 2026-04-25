// src/analysis/transfer/call/side_effects.rs
//
// Shared post-call applier (Phase 4 W4.1b).
//
// Reads `CallProto.ret`, `CallProto.flags`, and `CallProto.side_effects`
// to drive R0 typing and ref-tracking. Replaces the per-helper-id arms
// in `update_call_types` for migrated helpers; once Phase 4 W4.1c is
// done, kfuncs will plug into the same applier through a parallel
// proto producer in `signatures::kfuncs`.

use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::analysis::machine::stack_state::{DynptrKind, DynptrSlot};
use crate::analysis::transfer::types::update_store_types;
use crate::ast::MemSize;
use crate::common::stack_objects::BPF_DYNPTR_SIZE;

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
            SideEffect::SetExceptionCallbackFromArg { arg } => {
                let reg = arg_reg(arg);
                // Caller already validated R1 as PtrToCallback via
                // ArgKind::PtrToCallback; pull the subprog target out.
                if let RegType::PtrToCallback { subprog_pc } = in_types.get(reg) {
                    state.set_program_exception_cb(subprog_pc as usize);
                }
            }
            SideEffect::DynptrInitOnArg { arg, kind, rdonly } => {
                let reg = arg_reg(arg);
                let Some((frame, base_off)) = resolve_stack_arg(state, reg) else {
                    // Validator already accepted the arg, so we expect a
                    // resolvable PtrToStack here. If the offset went
                    // symbolic between validator and applier we'd skip
                    // the init silently, which is conservatively safe
                    // (the slot stays uninitialized → next consumer
                    // rejects it).
                    continue;
                };
                let ref_id = if dynptr_kind_acquires(kind) {
                    state.acquire_ref()
                } else {
                    0
                };

                // Initialize 16 stack bytes as scalar (the kernel's
                // STACK_DYNPTR mark; programs may not read the body).
                let stack = state.stack_at_mut(frame);
                for i in 0..BPF_DYNPTR_SIZE {
                    let byte_off = base_off as i64 + i as i64;
                    update_store_types(stack, RegType::ScalarValue, MemSize::U8, Some(byte_off));
                }

                // Stamp annotation on both 8-byte slots of the pair.
                stack.stack_set_dynptr(
                    base_off,
                    DynptrSlot { kind, ref_id, rdonly, first_slot: true },
                );
                stack.stack_set_dynptr(
                    base_off + 8,
                    DynptrSlot { kind, ref_id, rdonly, first_slot: false },
                );
            }
            SideEffect::DynptrReleaseFromArg { arg } => {
                let reg = arg_reg(arg);
                let Some((frame, base_off)) = resolve_stack_arg(state, reg) else {
                    continue;
                };
                // Validator already verified an initialized first-slot
                // dynptr lives here.
                let slot = state.stack_at(frame).stack_get_dynptr(base_off);
                if let Some(slot) = slot
                    && slot.ref_id != 0
                {
                    state.release_ref(slot.ref_id);
                    state.invalidate_ref(slot.ref_id);
                }
                let stack = state.stack_at_mut(frame);
                stack.stack_clear_dynptr(base_off);
                stack.stack_clear_dynptr(base_off + 8);
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

/// True if a dynptr of this kind carries an acquire/release ref
/// (currently `Ringbuf` only — `Local`/`Skb`/`Xdp` have no release
/// kfunc).
fn dynptr_kind_acquires(kind: DynptrKind) -> bool {
    matches!(kind, DynptrKind::Ringbuf)
}

/// Resolve a stack-pointer register to `(frame_level, base_offset)`.
/// Returns `None` if the register isn't a `PtrToStack` or its offset
/// to `R10` isn't a fixed integer that fits in `i16`. Used by both the
/// dynptr applier (here) and the dynptr arg validator (in `checks.rs`).
pub(super) fn resolve_stack_arg(state: &State, reg: Reg) -> Option<(FrameLevel, i16)> {
    let RegType::PtrToStack { frame_level } = state.types.get(reg) else {
        return None;
    };
    let off = state.domain.get_distance_fixed(reg, Reg::R10)?;
    let off16 = i16::try_from(off).ok()?;
    Some((frame_level, off16))
}

/// Map a 0-indexed arg slot (0..=4) to its register (R1..R5).
pub(super) fn arg_reg(arg: u8) -> Reg {
    match arg {
        0 => Reg::R1,
        1 => Reg::R2,
        2 => Reg::R3,
        3 => Reg::R4,
        4 => Reg::R5,
        _ => panic!("CallProto side-effect arg index {arg} out of range"),
    }
}
