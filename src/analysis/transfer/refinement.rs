// src/analysis/transfer/refinement.rs
//
// Pointer range refinement logic for packet, memory, and null checks

use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType};
use crate::ast::{Instr, CmpOp, Operand};
use crate::zone::domain::Reg;

/// Promote a pointer type across all stack frames by ref/ptr id.
/// `should_promote` checks if a slot's type matches, `promote` returns the new type.
fn promote_stack_slots_all_frames(
    state: &mut State,
    should_promote: impl Fn(&RegType) -> bool,
    promote: impl Fn(&RegType) -> RegType,
) {
    for frame in state.frames.iter_mut() {
        let offsets: Vec<i16> = frame.stack.slot_offsets();
        for k in offsets {
            let ty = frame.stack.get_slot_type(k);
            if should_promote(&ty) {
                frame.stack.set_slot_type(k, promote(&ty), None);
            }
        }
    }
}

/// Refines register types based on the outcome of a conditional branch.
///
/// This function analyzes the branch condition to promote types from "Unsafe" or "Nullable"
/// to "Safe". Specifically, it handles NULL checks for map values.
///
/// For example, given `if r0 != 0 goto Label`:
/// * In the **Taken** path (`branch_taken = true`), `r0` is known to be non-zero, so it is promoted to a safe pointer.
/// * In the **Fallthrough** path, `r0` is zero (NULL).
///
/// Conversely, given `if r0 == 0 goto Label`:
/// * In the **Fallthrough** path (`branch_taken = false`), `r0` is known to be non-zero.
///
/// # Arguments
///
/// * `state` - The mutable state to update.
/// * `instr` - The `If` instruction causing the branch.
/// * `branch_taken` - `true` if analyzing the path where the jump occurs; `false` if analyzing the fallthrough.
pub(crate) fn refine_branch(
    state: &mut State,
    instr: &Instr,
    branch_taken: bool,
) {
    match instr {
        Instr::If { op, left, right: Operand::Imm(0), .. } => {
            // Determine if this path implies reg is non-null
            let is_non_null = match op {
                CmpOp::Ne      => branch_taken,   // if (reg != 0) goto => taken means non-null
                CmpOp::Eq      => !branch_taken,  // if (reg == 0) goto => fallthrough means non-null
                CmpOp::SGe | CmpOp::UGe | CmpOp::SGt | CmpOp::UGt => branch_taken,
                CmpOp::SLe | CmpOp::ULe | CmpOp::SLt | CmpOp::ULt => !branch_taken,
                CmpOp::Test    => branch_taken,
            };

            // Existing map value promotion
            if is_non_null {
                maybe_promote_map_val(state, *left);
                maybe_promote_btf_id(state, *left);
                maybe_promote_mem(state, *left);
            }

            // refine acquired references (handles both paths)
            maybe_refine_acquired_ref(state, *left, is_non_null);
        },
        _ => {}
    }
}

/// Promotes a Nullable Map Pointer to a Safe Map Pointer.
fn maybe_promote_map_val(state: &mut State, reg: Reg) {
    let (target_id, _target_map_idx) = match state.types.get(reg) {
        RegType::PtrToMapValueOrNull { id, map_idx } => (id, map_idx),
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = state.types.get(r) {
            if id == target_id {
                state.types.set(r, RegType::PtrToMapValue { id, offset: Some(0), map_idx });
            }
        }
    }
    promote_stack_slots_all_frames(state,
        |ty| matches!(ty, RegType::PtrToMapValueOrNull { id, .. } if *id == target_id),
        |ty| match ty {
            RegType::PtrToMapValueOrNull { id, map_idx } => 
                RegType::PtrToMapValue { id: *id, offset: Some(0), map_idx: *map_idx },
            _ => unreachable!(),
        },
    );
}

fn maybe_promote_btf_id(state: &mut State, reg: Reg) {
    let target_id = match state.types.get(reg) {
        RegType::PtrToBtfIdOrNull { id, .. } => id,
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToBtfIdOrNull { id, type_name, trusted } = state.types.get(r) {
            if id == target_id {
                state.types.set(r, RegType::PtrToBtfId { type_name, trusted });
            }
        }
    }
    promote_stack_slots_all_frames(state,
        |ty| matches!(ty, RegType::PtrToBtfIdOrNull { id, .. } if *id == target_id),
        |ty| match ty {
            RegType::PtrToBtfIdOrNull { id: _, type_name, trusted } => 
                RegType::PtrToBtfId { type_name, trusted: *trusted },
            _ => unreachable!(),
        },
    );
}

fn maybe_promote_mem(state: &mut State, reg: Reg) {
    let (target_id, _) = match state.types.get(reg) {
        RegType::PtrToAllocMemOrNull { id, mem_size } => (id, mem_size),
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToAllocMemOrNull { id, mem_size } = state.types.get(r) {
            if id == target_id {
                state.types.set(r, RegType::PtrToAllocMem { id, mem_size });
            }
        }
    }
    promote_stack_slots_all_frames(state,
        |ty| matches!(ty, RegType::PtrToAllocMemOrNull { id, .. } if *id == target_id),
        |ty| match ty {
            RegType::PtrToAllocMemOrNull { id, mem_size } => 
                RegType::PtrToAllocMem { id: *id, mem_size: *mem_size },
            _ => unreachable!(),
        },
    );
}

fn same_socket_nullable_pointer(t1: &RegType, t2: &RegType) -> bool {
    match (t1, t2) {
        (RegType::PtrToSocketOrNull { ref_id: id1 }, RegType::PtrToSocketOrNull { ref_id: id2 }) => id1 == id2,
        (RegType::PtrToSockCommonOrNull { ref_id: id1 }, RegType::PtrToSockCommonOrNull { ref_id: id2 }) => id1 == id2,
        (RegType::PtrToTcpSockOrNull { id: id1 }, RegType::PtrToTcpSockOrNull { id: id2 }) => id1 == id2,
        _ =>false 
    }
}

/// On the non-NULL path: promotes PtrToSocketOrNull → PtrToSocket (ref stays active).
/// On the NULL path: releases the reference from tracking.
fn maybe_refine_acquired_ref(state: &mut State, reg: Reg, is_non_null: bool) {
    let reg_type = state.types.get(reg);
    let target_ref_id = match reg_type {
        RegType::PtrToSocketOrNull { ref_id } 
        | RegType::PtrToSockCommonOrNull { ref_id } 
        | RegType::PtrToTcpSockOrNull { id: ref_id } => ref_id,
        _ => return,
    };

    if is_non_null {
        for r in Reg::ALL {
            let ty = state.types.get(r);
            if same_socket_nullable_pointer(&reg_type, &ty) {
                state.types.set(r, ty.to_non_null().unwrap());
            }
        }
        promote_stack_slots_all_frames(
            state,
            |ty| same_socket_nullable_pointer(&reg_type, ty),
            |ty| ty.to_non_null().unwrap_or(RegType::ScalarValue),
        );
    } else {
        if target_ref_id.is_some() {
            state.release_ref(target_ref_id.unwrap());
        }
        for r in Reg::ALL {
            let ty = state.types.get(r);
            if same_socket_nullable_pointer(&reg_type, &ty) {
                state.types.set(r, RegType::ScalarValue);
            }
        }
        promote_stack_slots_all_frames(state,
            |ty| same_socket_nullable_pointer(&reg_type, ty),
            |_ty| RegType::ScalarValue,
        );
    }
}
