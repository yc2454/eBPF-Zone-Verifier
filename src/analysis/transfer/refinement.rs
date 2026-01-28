// src/analysis/transfer/refinement.rs
//
// Pointer range refinement logic for packet, memory, and null checks

use crate::analysis::state::State;
use crate::analysis::reg_types::{RegType, TypeState};
use crate::ast::{Instr, CmpOp, Operand};
use crate::zone::domain::Reg;
use crate::zone::dbm::{Dbm, INF};
use crate::zone::domain::assign_zero;
use crate::parsing::ctx_model::MemRegionId;

/// Refines the safe access range of packet pointers based on numerical constraints.
///
/// This function bridges the Numerical Domain (DBM) and the Type System. It queries
/// the DBM to determine the distance between a packet pointer and the packet end register.
/// If the DBM proves that `pointer <= end - K`, then `K` bytes are safe to access.
///
/// This function handles aliasing: if multiple registers or stack slots point to the
/// same packet ID, they are all updated with the newly discovered safe range.
///
/// # Arguments
///
/// * `dbm` - The Difference Bound Matrix containing numerical constraints (e.g., `r1 < r2`).
/// * `types` - The mutable type state to update with new ranges.
/// * `packet_reg` - The register holding the packet pointer being compared.
/// * `end_reg` - The register holding the pointer to the end of the packet (`PtrToPacketEnd`).
pub(crate) fn refine_packet_ranges(dbm: &Dbm, types: &mut TypeState, packet_reg: Reg, end_reg: Reg) {
    let target_id = match types.get(packet_reg) {
        RegType::PtrToPacket { id, .. } => id,
        _ => return,
    };
    
    if !matches!(types.get(end_reg), RegType::PtrToPacketEnd) {
        return;
    }
    
    let mut max_base_range: u64 = 0;
    
    for r in Reg::ALL {
        if let RegType::PtrToPacket { id, range, off, is_base: _ } = types.get(r) {
            if id == target_id {
                let dist = dbm.get(r, end_reg);
                if dist < INF && dist <= 0 {
                    let safe_from_r = dist.unsigned_abs();
                    
                    // Only compute base range for non-negative offsets
                    if off >= 0 {
                        let base_range = (off as u64).saturating_add(safe_from_r);
                        if base_range > max_base_range {
                            max_base_range = base_range;
                        }
                    }
                }
                // Keep existing valid range if larger
                if range > max_base_range {
                    max_base_range = range;
                }
            }
        }
    }
    
    // Propagate to all pointers with this ID
    if max_base_range > 0 {
        for r in Reg::ALL {
            if let RegType::PtrToPacket { id, off, is_base, .. } = types.get(r) {
                if id == target_id {
                    types.set(r, RegType::PtrToPacket { id, range: max_base_range, off, is_base });
                }
            }
        }
        
        let stack_keys: Vec<i16> = types.stack.keys().cloned().collect();
        for k in stack_keys {
            if let RegType::PtrToPacket { id, off, is_base, .. } = types.get_stack(k) {
                if id == target_id {
                    types.set_stack(k, RegType::PtrToPacket { id, range: max_base_range, off, is_base });
                }
            }
        }
    }
}

/// Refines the safe access range of memory region pointers based on DBM constraints.
/// Similar to refine_packet_ranges but for PtrToMem.
pub(crate) fn refine_mem_ranges(dbm: &Dbm, types: &mut TypeState, mem_reg: Reg, end_reg: Reg) {
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
    let stack_keys: Vec<i16> = types.stack.keys().cloned().collect();
    for k in stack_keys {
        if let RegType::PtrToMem { region, range } = types.get_stack(k) {
            if region == target_region {
                let max_range = Reg::ALL.iter()
                    .filter_map(|&r| match types.get(r) {
                        RegType::PtrToMem { region: rg, range } if rg == target_region => Some(range),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0);
                if max_range > range {
                    types.set_stack(k, RegType::PtrToMem { region, range: max_range });
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
    branch_taken: bool // True if we are analyzing the branch-taken path, False if fallthrough
) {
    match instr {
        Instr::If { op, left, right: Operand::Imm(0), .. } => {
            match op {
                CmpOp::Ne => {
                    // if (reg != 0) goto Target;
                    // Taken (True) -> reg != 0 -> SAFE
                    if branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::Eq => {
                    // if (reg == 0) goto Target;
                    // Fallthrough (False) -> reg != 0 -> SAFE
                    if !branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::SGe | CmpOp::UGe | CmpOp::SGt | CmpOp::UGt => {
                    // if (reg >= 0) goto Target;  or  if (reg > 0) goto Target;
                    // Taken (True) -> reg >= 1 -> SAFE
                    if branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::SLe | CmpOp::ULe | CmpOp::SLt | CmpOp::ULt => {
                    // if (reg <= 0) goto Target;  or  if (reg < 0) goto Target;
                    // Fallthrough (False) -> reg >= 1 -> SAFE
                    if !branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::Test => {
                    // if (reg & 0xFF != 0) goto Target;
                    // Taken (True) -> reg != 0 -> SAFE
                    if branch_taken { maybe_promote_map_val(state, *left); }
                }
            }
        },
        _ => {}
    }
}

/// Promotes a Nullable Map Pointer to a Safe Map Pointer.
///
/// This helper function is called when a register is proven to be non-zero (non-NULL).
/// It transitions a register from `RegType::PtrToMapValueOrNull` to `RegType::PtrToMapValue`.
///
/// # Aliasing
/// This function scans **all** registers and **all** stack slots. Any location holding
/// a pointer with the same unique ID as `reg` is also promoted. This ensures that verifying
/// one alias (e.g., `if r1 != 0`) validates all copies of that pointer (e.g., `r2 = r1`).
///
/// # Arguments
///
/// * `state` - The mutable state to update.
/// * `reg` - The register that was validated as non-null.
fn maybe_promote_map_val(state: &mut State, reg: Reg) {
    let (target_id, _target_map_idx) = match state.types.get(reg) {
        RegType::PtrToMapValueOrNull { id, map_idx } => (id, map_idx),
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = state.types.get(r) {
            if id == target_id {
                state.types.set(r, RegType::PtrToMapValue { offset: Some(0), map_idx });
                assign_zero(&mut state.dbm, r);
            }
        }
    }
    let stack_keys: Vec<i16> = state.types.stack.keys().cloned().collect();
    for k in stack_keys {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = state.types.get_stack(k) {
            if id == target_id {
                state.types.set_stack(k, RegType::PtrToMapValue { offset: Some(0), map_idx });
            }
        }
    }
}
