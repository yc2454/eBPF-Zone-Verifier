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
use crate::analysis::machine::reg_types::{RegType, TypeState, new_iter_id, new_ptr_id};
use crate::analysis::machine::stack_state::{
    DynptrKind, DynptrSlot, IrqFlagSlot, IterState, IteratorSlot,
};
use crate::common::stack_objects::bpf_iter_size;
use crate::analysis::machine::state::State;
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
                    if proto.flags.contains(CallFlags::RELEASE_NON_OWN) {
                        // Graph-add (rbtree_add / list_push_*): the
                        // owning ref is consumed by the container, but
                        // the original alloc-pointer aliases stay
                        // valid as non-owning refs under the lock
                        // (verifier.c v6.15 L12471
                        // `ref_convert_owning_non_owning`). Drop the
                        // ref-tracking entry but retype aliases rather
                        // than wiping them.
                        state.release_ref(ref_id);
                        state.convert_ref_to_non_owning(ref_id);
                    } else {
                        state.release_ref(ref_id);
                        state.invalidate_ref(ref_id);
                    }
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
                let dynptr_id = crate::analysis::machine::reg_types::new_dynptr_id();

                // Pre-stamp destroy-and-sweep (kernel
                // `destroy_if_dynptr_stack_slot`, verifier.c v6.15 L880):
                // if the slot already holds an *unrefcounted* dynptr
                // (refcounted is rejected by `validate_dynptr_arg`),
                // invalidate slices that carry the old `dynptr_id` so
                // their `PtrToAllocMem*` regs/slots demote to Scalar
                // (mirrors `bpf_for_each_reg_in_vstate` at L913-919).
                let mut victim_ids: Vec<u32> = Vec::new();
                if let Some(slot) = state.stack_at(frame).stack_get_dynptr(base_off) {
                    victim_ids.push(slot.dynptr_id);
                }
                if let Some(slot) = state.stack_at(frame).stack_get_dynptr(base_off + 8)
                    && !victim_ids.contains(&slot.dynptr_id)
                {
                    victim_ids.push(slot.dynptr_id);
                }
                for vid in &victim_ids {
                    state.invalidate_dynptr_slices(*vid);
                }

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
                    DynptrSlot { kind, ref_id, rdonly, first_slot: true, dynptr_id },
                );
                stack.stack_set_dynptr(
                    base_off + 8,
                    DynptrSlot { kind, ref_id, rdonly, first_slot: false, dynptr_id },
                );
            }
            SideEffect::IterInitOnArg { arg, kind } => {
                let reg = arg_reg(arg);
                let Some((frame, base_off)) = resolve_stack_arg(state, reg) else {
                    continue;
                };
                let size_bytes = bpf_iter_size(kind);
                // Kernel `mark_stack_slots_iter` (verifier.c v6.15
                // ~L1041): for KF_RCU_PROTECTED iter `_new` kfuncs (task,
                // css), the slot is MEM_RCU (trusted) iff we're in an
                // RCU CS at init time, otherwise PTR_UNTRUSTED. The
                // subsequent `_next` call then rejects the UNTRUSTED
                // slot with "expected an RCU CS when using …".
                let untrusted = kind.is_rcu_protected() && !state.in_rcu_read_section();
                let stack = state.stack_at_mut(frame);
                for i in 0..size_bytes {
                    let byte_off = base_off as i64 + i as i64;
                    update_store_types(stack, RegType::ScalarValue, MemSize::U8, Some(byte_off));
                }
                stack.stack_set_iterator(
                    base_off,
                    IteratorSlot {
                        kind,
                        state: IterState::Active,
                        id: new_iter_id(),
                        depth: 0,
                        untrusted,
                    },
                );
            }
            SideEffect::IterDestroyOnArg { arg } => {
                let reg = arg_reg(arg);
                let Some((frame, base_off)) = resolve_stack_arg(state, reg) else {
                    continue;
                };
                state.stack_at_mut(frame).stack_clear_iterator(base_off);
            }
            SideEffect::IrqSaveOnArg { arg, kfunc_class } => {
                let reg = arg_reg(arg);
                let Some((frame, base_off)) = resolve_stack_arg(state, reg) else {
                    continue;
                };
                // Initialize 8 stack bytes as scalar (kernel
                // `mark_stack_slots_irq_flag` ~L1184 stamps STACK_IRQ_FLAG;
                // we mirror with scalar bytes + the irq_flag annotation).
                let stack = state.stack_at_mut(frame);
                for i in 0..8 {
                    let byte_off = base_off as i64 + i as i64;
                    update_store_types(stack, RegType::ScalarValue, MemSize::U8, Some(byte_off));
                }
                let id = state.irq_save();
                state.stack_at_mut(frame).stack_set_irq_flag(
                    base_off,
                    IrqFlagSlot { id, kfunc_class },
                );
            }
            SideEffect::IrqRestoreFromArg { arg, kfunc_class: _ } => {
                let reg = arg_reg(arg);
                let Some((frame, base_off)) = resolve_stack_arg(state, reg) else {
                    continue;
                };
                // Validator already enforced: slot has IRQ_FLAG, class
                // matches, id == active_irq_id. Pop + clear annotation.
                if let Some(slot) = state.stack_at(frame).stack_get_irq_flag(base_off) {
                    let _ = state.irq_restore(slot.id);
                }
                state.stack_at_mut(frame).stack_clear_irq_flag(base_off);
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
        RetKind::PtrToCpumask => {
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToCpumaskOrNull { ref_id }
            } else {
                RegType::PtrToCpumask { ref_id }
            };
            state.types.set(Reg::R0, ty);
            true
        }
        RetKind::PtrToCgroup => {
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToCgroupOrNull { ref_id }
            } else {
                RegType::PtrToCgroup { ref_id }
            };
            state.types.set(Reg::R0, ty);
            true
        }
        RetKind::PtrToTask => {
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToTaskOrNull { ref_id }
            } else {
                RegType::PtrToTask { ref_id }
            };
            state.types.set(Reg::R0, ty);
            true
        }
        RetKind::PtrToBtfIdNamed { type_name } => {
            use crate::analysis::machine::reg_types::PtrFlags;
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToBtfIdOrNull {
                    id: new_ptr_id(),
                    type_name,
                    flags: PtrFlags::TRUSTED,
                    ref_id,
                }
            } else {
                RegType::PtrToBtfId {
                    type_name,
                    flags: PtrFlags::TRUSTED,
                    ref_id,
                }
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
        RetKind::PtrToAllocMem { mem_size } => {
            let id = new_ptr_id();
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToAllocMemOrNull {
                    id,
                    mem_size,
                    ref_id: None,
                    dynptr_id: None,
                }
            } else {
                RegType::PtrToAllocMem {
                    id,
                    mem_size,
                    ref_id: None,
                    dynptr_id: None,
                }
            };
            state.types.set(Reg::R0, ty);
            true
        }
        RetKind::IterNextBtfId { .. } => {
            // Same dispatch shape as `IterNextElem` — both forking
            // returns are split into successors before the flat-state
            // applier runs.
            unreachable!(
                "RetKind::IterNextBtfId must be handled by the kfunc dispatcher fork"
            );
        }
        RetKind::IterNextElem { .. } => {
            // The kfunc dispatcher forks IterNextElem into two
            // successors before the flat-state applier runs; reaching
            // here means a caller invoked the wrong path.
            unreachable!("RetKind::IterNextElem must be handled by the kfunc dispatcher fork");
        }
        RetKind::PtrToOwnedKptr => {
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            // pointee_btf_id is left None here; the kfunc dispatcher
            // (kfunc.rs) special-cases bpf_obj_new_impl /
            // bpf_refcount_acquire_impl / list+rbtree pop kfuncs to
            // overwrite R0 with the resolved pointee type id. Other
            // RetKind::PtrToOwnedKptr producers (currently none) get an
            // unknown pointee, which makes the __contains validator
            // fall through to the offset-only check.
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToOwnedKptrOrNull { ref_id, pointee_btf_id: None, offset: 0 }
            } else {
                RegType::PtrToOwnedKptr {
                    ref_id,
                    offset: 0,
                    non_owning: false,
                    pointee_btf_id: None,
                }
            };
            state.types.set(Reg::R0, ty);
            true
        }
        RetKind::PtrToArenaFromArg { page_cnt_arg } => {
            // mem_size = page_cnt * PAGE_SIZE (4096). Read upper bound
            // from the page_cnt arg (R(page_cnt_arg+1)); same convention
            // as PtrToAllocMemFromArg.
            const PAGE_SIZE: u64 = 4096;
            let size_reg = arg_reg(page_cnt_arg);
            let (_, max_pages) = state.domain.get_interval(size_reg);
            let mem_size = (max_pages.max(0) as u64).saturating_mul(PAGE_SIZE);
            let ref_id = if proto.flags.contains(CallFlags::ACQUIRE) {
                Some(state.acquire_ref())
            } else {
                None
            };
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToArenaOrNull { ref_id, mem_size }
            } else {
                RegType::PtrToArena { ref_id, mem_size }
            };
            state.types.set(Reg::R0, ty);
            true
        }
        RetKind::PtrToAllocMemFromArg { size_arg } => {
            // Read the size arg's upper bound from the pre-call domain
            // (apply_call_proto_r0 runs before caller-saved clobber, so
            // R1..R5 still hold their pre-call values here).
            let size_reg = arg_reg(size_arg);
            let (_, max_size) = state.domain.get_interval(size_reg);
            let mem_size = max_size.max(0) as u64;
            let id = new_ptr_id();
            // Inherit the source dynptr's ref_id from R1 so that releasing
            // the dynptr (`bpf_ringbuf_submit_dynptr` etc.) invalidates the
            // returned slice pointer too — catches use-after-release.
            // Also inherit `dynptr_id` (the per-instance identity) so
            // overwriting the source dynptr with `bpf_dynptr_from_mem`
            // (etc.) demotes the slice — mirrors kernel verifier.c v6.15
            // L11701 `regs[BPF_REG_0].dynptr_id = meta.dynptr_id`. All
            // current `PtrToAllocMemFromArg` users (`bpf_dynptr_data`,
            // `bpf_dynptr_slice`, `bpf_dynptr_slice_rdwr`) have R1 as
            // the source dynptr.
            let src_slot = resolve_stack_arg(state, arg_reg(0))
                .and_then(|(frame, off)| state.stack_at(frame).stack_get_dynptr(off));
            let ref_id = src_slot.map(|s| s.ref_id).filter(|id| *id != 0);
            let dynptr_id = src_slot.map(|s| s.dynptr_id);
            let ty = if proto.flags.contains(CallFlags::RET_NULL) {
                RegType::PtrToAllocMemOrNull {
                    id,
                    mem_size,
                    ref_id,
                    dynptr_id,
                }
            } else {
                RegType::PtrToAllocMem {
                    id,
                    mem_size,
                    ref_id,
                    dynptr_id,
                }
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
