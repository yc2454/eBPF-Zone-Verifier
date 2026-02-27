// src/analysis/transfer/branch/interval_packet.rs
//
// Interval-specific packet bounds refinement.
//
// This module handles updating the interval domain's packet_size_lower_bound
// when branch conditions reveal information about packet geometry.
//
// Example: After `if (pkt_data + 8 <= pkt_end) goto safe`, on the taken path
// we know the packet has at least 8 bytes, so we set packet_size_lower_bound = 8.
//
// This logic is interval-specific because the zone domain tracks these
// relationships directly via difference constraints (pkt_end - pkt_data >= N).

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::CmpOp;
use crate::domains::numeric::NumericDomain;

/// Information extracted from a packet pointer comparison
struct PacketComparison {
    /// Offset from pkt_data (e.g., 8 for pkt_data + 8)
    data_offset: i64,
    /// Whether data_offset includes any variable range
    has_variable_range: bool,
}

/// Try to extract packet comparison info from a register.
/// Returns Some if the register is pkt_data + constant offset.
fn get_packet_data_offset(state: &State, reg: Reg) -> Option<PacketComparison> {
    // Check if register type is PtrToPacket
    if !matches!(state.types.get(reg), RegType::PtrToPacket) {
        return None;
    }

    // Get the pointer offset info from interval state
    if let NumericDomain::Interval(ref ivl) = state.domain {
        if let Some(ptr_off) = ivl.get_ptr_offset(reg) {
            // Must be relative to AnchorData (pkt_data)
            if ptr_off.anchor == Reg::AnchorData {
                return Some(PacketComparison {
                    data_offset: ptr_off.offset,
                    has_variable_range: ptr_off.range > 0,
                });
            }
        }
    }

    None
}

/// Check if a register represents pkt_end
fn is_packet_end(state: &State, reg: Reg) -> bool {
    matches!(state.types.get(reg), RegType::PtrToPacketEnd)
}

/// Refine packet bounds based on a comparison between two registers.
///
/// Called when we have a branch condition comparing packet pointers.
/// Updates packet_size_lower_bound in the interval state when we can
/// prove a minimum packet size from the comparison.
///
/// # Arguments
/// * `state` - The state to update (should be the branch path state)
/// * `left` - Left operand of comparison
/// * `right` - Right operand of comparison
/// * `op` - The comparison operator
/// * `branch_taken` - Whether this is the taken (true) or fallthrough (false) path
pub fn refine_packet_bounds(
    state: &mut State,
    left: Reg,
    right: Reg,
    op: CmpOp,
    branch_taken: bool,
) {
    // Only applies to interval domain
    if !matches!(state.domain, NumericDomain::Interval(_)) {
        return;
    }

    // First, gather all information we need (immutable borrows)
    let (data_info, is_data_on_left) = if let Some(info) = get_packet_data_offset(state, left) {
        if is_packet_end(state, right) {
            (info, true)
        } else {
            return;
        }
    } else if let Some(info) = get_packet_data_offset(state, right) {
        if is_packet_end(state, left) {
            (info, false)
        } else {
            return;
        }
    } else {
        return;
    };

    // Skip if there's variable range - we can only use fixed offsets
    if data_info.has_variable_range {
        return;
    }

    let offset = data_info.data_offset;

    // Determine if this path proves packet has at least `offset` bytes
    //
    // Pattern: if (pkt_data + N OP pkt_end) goto taken
    //
    // For data_on_left (pkt_data + N OP pkt_end):
    //   ULe/SLe (<=): taken means N <= packet_size, so packet_size >= N
    //   ULt/SLt (<):  taken means N < packet_size, so packet_size >= N (actually > N-1)
    //   UGt/SGt (>):  fallthrough means N <= packet_size
    //   UGe/SGe (>=): fallthrough means N < packet_size
    //
    // For data_on_right (pkt_end OP pkt_data + N):
    //   UGe/SGe (>=): taken means packet_size >= N
    //   UGt/SGt (>):  taken means packet_size > N
    //   ULe/SLe (<=): fallthrough means packet_size >= N
    //   ULt/SLt (<):  fallthrough means packet_size > N

    let proves_size_ge_offset = if is_data_on_left {
        match (op, branch_taken) {
            // pkt_data + N <= pkt_end, taken => packet_size >= N
            (CmpOp::ULe | CmpOp::SLe, true) => true,
            // pkt_data + N < pkt_end, taken => packet_size > N (we use >= N)
            (CmpOp::ULt | CmpOp::SLt, true) => true,
            // pkt_data + N > pkt_end, fallthrough => packet_size >= N
            (CmpOp::UGt | CmpOp::SGt, false) => true,
            // pkt_data + N >= pkt_end, fallthrough => packet_size > N (we use >= N)
            (CmpOp::UGe | CmpOp::SGe, false) => true,
            _ => false,
        }
    } else {
        // pkt_end on left
        match (op, branch_taken) {
            // pkt_end >= pkt_data + N, taken => packet_size >= N
            (CmpOp::UGe | CmpOp::SGe, true) => true,
            // pkt_end > pkt_data + N, taken => packet_size > N
            (CmpOp::UGt | CmpOp::SGt, true) => true,
            // pkt_end <= pkt_data + N, fallthrough => packet_size >= N
            (CmpOp::ULe | CmpOp::SLe, false) => true,
            // pkt_end < pkt_data + N, fallthrough => packet_size > N
            (CmpOp::ULt | CmpOp::SLt, false) => true,
            _ => false,
        }
    };

    if proves_size_ge_offset && offset > 0 {
        // Now do the mutable borrow to update
        if let NumericDomain::Interval(ref mut ivl) = state.domain {
            let current = ivl.get_packet_size_bound().unwrap_or(0);
            if offset as u64 > current {
                ivl.set_packet_size_bound(offset as u64);
            }
        }
    }
}

/// Wrapper to call refine_packet_bounds for both then and else states
pub fn refine_packet_bounds_on_branch(
    then_state: &mut State,
    else_state: &mut State,
    left: Reg,
    right: Reg,
    op: CmpOp,
) {
    refine_packet_bounds(then_state, left, right, op, true);
    refine_packet_bounds(else_state, left, right, op, false);
}
