// src/analysis/transfer/refinement.rs
//
// Pointer range refinement logic for packet, memory, and null checks

use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::stack_state::StackState;
use crate::ast::{Instr, CmpOp, Operand};
use crate::zone::domain::Reg;
use crate::zone::dbm::{Dbm, INF};
use crate::common::ctx_model::MemRegionId;

/// Refines the safe access range of memory region pointers based on DBM constraints.
/// Similar to refine_packet_ranges but for PtrToMem.
pub(crate) fn refine_mem_ranges(dbm: &Dbm, types: &mut TypeState, stack: &mut StackState, mem_reg: Reg, end_reg: Reg) {
    let target_region = match types.get(mem_reg) {
        RegType::PtrToMem { region, .. } => region,
        _ => return,
    };
    
    // Validate end_reg is the correct end marker for this region
    let is_valid_end = match target_region {
        MemRegionId::CalicoMetaRegion => {
            matches!(types.get(end_reg), RegType::PtrToPacket { is_base: true, .. })
        }
    };
    if !is_valid_end {
        return;
    }
    
    // Update all PtrToMem registers with matching region
    for r in Reg::ALL {
        if let RegType::PtrToMem { region, range } = types.get(r) {
            if region == target_region {
                let dist = dbm.get(r, end_reg);
                if dist < INF && dist <= 0 {
                    let safe_bytes = dist.unsigned_abs();
                    if safe_bytes > range {
                        types.set(r, RegType::PtrToMem { region, range: safe_bytes });
                    }
                }
            }
        }
    }
    
    // Also update stack slots with matching region
    for k in stack.slot_offsets() {
        if let RegType::PtrToMem { region, range } = stack.get_slot_type(k) {
            if region == target_region {
                let max_range = Reg::ALL.iter()
                    .filter_map(|&r| match types.get(r) {
                        RegType::PtrToMem { region: rg, range } if rg == target_region => Some(range),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0);
                if max_range > range {
                    stack.set_slot_type(k, RegType::PtrToMem { region, range: max_range });
                }
            }
        }
    }
}

pub(crate) fn refine_packet_ranges(dbm: &Dbm, types: &mut TypeState, stack: &mut StackState, pkt_reg: Reg, end_reg: Reg) {
    println!("Refining packet ranges");
    // Determine which register is PtrToPacket and which is PtrToPacketEnd
    let target_id = match (types.get(pkt_reg), types.get(end_reg)) {
        (RegType::PtrToPacket { id, .. }, RegType::PtrToPacketEnd) => id,
        (RegType::PtrToPacketEnd, RegType::PtrToPacket { .. }) => {
            // Swap: recurse with correct argument order
            return refine_packet_ranges(dbm, types, stack, end_reg, pkt_reg);
        }
        _ => return,
    };

    println!("Target ID: {}", target_id);

    // Update all PtrToPacket registers with matching id
    for r in Reg::ALL {
        if let RegType::PtrToPacket { id, is_base, range } = types.get(r) {
            if id == target_id {
                let dist = dbm.get(r, end_reg);
                println!("{:?} -> {:?}: dist = {}", r, end_reg, dist);
                if dist < INF && dist <= 0 {
                    let safe_bytes = dist.unsigned_abs() as i64;
                    if safe_bytes > range {
                        types.set(r, RegType::PtrToPacket { id, is_base, range: safe_bytes });
                    }
                }
            }
        }
    }

    // Also update stack slots with matching id
    for k in stack.slot_offsets() {
        if let RegType::PtrToPacket { id, is_base, range } = stack.get_slot_type(k) {
            if id == target_id {
                let max_range = Reg::ALL.iter()
                    .filter_map(|&r| match types.get(r) {
                        RegType::PtrToPacket { id: rid, range, .. } if rid == target_id => Some(range),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0);
                if max_range > range {
                    stack.set_slot_type(k, RegType::PtrToPacket { id, is_base, range: max_range });
                }
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
    for k in state.stack.slot_offsets() {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = state.stack.get_slot_type(k) {
            if id == target_id {
                state.stack.set_slot_type(k, RegType::PtrToMapValue { id, offset: Some(0), map_idx });
            }
        }
    }
}

/// On the non-NULL path: promotes PtrToSocketOrNull → PtrToSocket (ref stays active).
/// On the NULL path: releases the reference from tracking.
fn maybe_refine_acquired_ref(state: &mut State, reg: Reg, is_non_null: bool) {
    let target_ref_id = match state.types.get(reg) {
        RegType::PtrToSocketOrNull { ref_id } 
        | RegType::PtrToSockCommonOrNull { ref_id } 
        | RegType::PtrToTcpSockOrNull { id: ref_id } => ref_id,
        _ => return,
    };

    if is_non_null {
        for r in Reg::ALL {
            let ty = state.types.get(r);
            match ty {
                RegType::PtrToSocketOrNull { ref_id } 
                | RegType::PtrToSockCommonOrNull { ref_id } 
                | RegType::PtrToTcpSockOrNull { id: ref_id } => {
                    if ref_id == target_ref_id {
                        state.types.set(r, ty.to_non_null().unwrap());
                    }
                }
                _ => {}
            }
        }
        for k in state.stack.slot_offsets() {
            let ty = state.stack.get_slot_type(k);
            match ty {
                RegType::PtrToSocketOrNull { ref_id } 
                | RegType::PtrToSockCommonOrNull { ref_id } 
                | RegType::PtrToTcpSockOrNull { id: ref_id } => {
                    if ref_id == target_ref_id {
                        state.stack.set_slot_type(k, ty.to_non_null().unwrap());
                    }
                }
                _ => {}
            }
        }
    } else {
        if target_ref_id.is_some() {
            state.release_ref(target_ref_id.unwrap());
        }
        for r in Reg::ALL {
            match state.types.get(r) {
                RegType::PtrToSocketOrNull { ref_id } 
                | RegType::PtrToSockCommonOrNull { ref_id } 
                | RegType::PtrToTcpSockOrNull { id: ref_id } => {
                    if ref_id == target_ref_id {
                        state.types.set(r, RegType::ScalarValue);
                    }
                }
                _ => {}
            }
        }
        for k in state.stack.slot_offsets() {
            match state.stack.get_slot_type(k) {
                RegType::PtrToSocketOrNull { ref_id } 
                | RegType::PtrToSockCommonOrNull { ref_id } 
                | RegType::PtrToTcpSockOrNull { id: ref_id } => {
                    if ref_id == target_ref_id {
                        state.stack.set_slot_type(k, RegType::ScalarValue);
                    }
                }
                _ => {}
            }
        }
    }
}
