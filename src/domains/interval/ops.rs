// Interval domain operations
//
// Implements the abstract operations for the interval domain.
// These mirror the zone/ops.rs interface but without relational constraints.

use crate::analysis::machine::reg::Reg;
use super::state::{IntervalState, ScalarBounds, RegInterval, PtrOffset};

// ══════════════════════════════════════════════════════════════════════════════
//  Query & Interval Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Extracts the interval [lower_bound, upper_bound] for a register
pub fn get_interval(state: &IntervalState, x: Reg) -> (i64, i64) {
    state.get_interval(x)
}

/// Returns the interval of the distance between two registers
/// For interval domain, this is conservative unless both are pointers to same anchor
pub fn get_distance_interval(state: &IntervalState, x: Reg, y: Reg) -> (i64, i64) {
    // Trivial case: distance from a register to itself is always 0
    if x == y {
        return (0, 0);
    }

    // Check if both registers have pointer offset info to the same anchor
    let x_off = state.get_ptr_offset(x);
    let y_off = state.get_ptr_offset(y);

    match (x_off, y_off) {
        (Some(xo), Some(yo)) if xo.anchor == yo.anchor => {
            // Both point to same anchor - can compute distance
            let min_diff = xo.offset.saturating_sub(yo.max_offset());
            let max_diff = xo.max_offset().saturating_sub(yo.offset);
            (min_diff, max_diff)
        }
        _ => {
            // Cannot determine relationship - return conservative bounds
            // Try to use scalar bounds
            let (x_min, x_max) = state.get_interval(x);
            let (y_min, y_max) = state.get_interval(y);

            if x_min != i64::MIN && x_max != i64::MAX && y_min != i64::MIN && y_max != i64::MAX {
                (x_min.saturating_sub(y_max), x_max.saturating_sub(y_min))
            } else {
                (i64::MIN, i64::MAX)
            }
        }
    }
}

/// Returns the exact distance between two registers if constant
pub fn get_distance_fixed(state: &IntervalState, x: Reg, y: Reg) -> Option<i64> {
    let (lo, hi) = get_distance_interval(state, x, y);
    if lo == hi && lo != i64::MIN && lo != i64::MAX {
        Some(lo)
    } else {
        None
    }
}

/// Returns the fixed concrete value of a register if constant
pub fn get_fixed_value(state: &IntervalState, x: Reg) -> Option<i64> {
    state.get_fixed_value(x)
}

// ══════════════════════════════════════════════════════════════════════════════
//  Predicates & Proofs
// ══════════════════════════════════════════════════════════════════════════════

/// Returns true if the register is proven to be exactly zero
pub fn proven_zero(state: &IntervalState, x: Reg) -> bool {
    state.get_bounds(x).is_zero()
}

/// Returns true if the register is proven to be >= 0
pub fn proven_nonnegative(state: &IntervalState, x: Reg) -> bool {
    state.get_bounds(x).is_nonnegative()
}

/// Returns true if the register is proven to be > 0
pub fn proven_positive(state: &IntervalState, x: Reg) -> bool {
    state.get_bounds(x).is_positive()
}

/// Returns true if a register is proven to be in the u32 range [0, 2^32-1]
pub fn proven_u32_range(state: &IntervalState, v: Reg) -> bool {
    state.get_bounds(v).is_u32()
}

// ══════════════════════════════════════════════════════════════════════════════
//  Value Assignments
// ══════════════════════════════════════════════════════════════════════════════

/// Removes all constraints related to the specified register
pub fn forget(state: &mut IntervalState, x: Reg) {
    state.forget(x);
}

/// Overwrites a register with a specific constant value
pub fn assign_imm(state: &mut IntervalState, x: Reg, imm: i64) {
    if x != Reg::Zero && !x.is_anchor() {
        state.set(x, RegInterval::constant(imm));
    }
}

/// Overwrites a register with zero
pub fn assign_zero(state: &mut IntervalState, x: Reg) {
    assign_imm(state, x, 0);
}

/// Overwrites a register with the value of another register
pub fn assign_reg(state: &mut IntervalState, x: Reg, y: Reg) {
    if x != Reg::Zero && !x.is_anchor() {
        state.set(x, state.get(y).clone());
    }
}

/// Establishes the relationship dst = src + imm
pub fn assign_reg_offset(state: &mut IntervalState, dst: Reg, src: Reg, imm: i64) {
    if dst == Reg::Zero || dst.is_anchor() {
        return;
    }

    let src_interval = state.get(src).clone();
    let new_bounds = ScalarBounds {
        smin: src_interval.bounds.smin.saturating_add(imm),
        smax: src_interval.bounds.smax.saturating_add(imm),
        umin: src_interval.bounds.umin.saturating_add(imm as u64),
        umax: src_interval.bounds.umax.saturating_add(imm as u64),
    };

    // Preserve pointer offset info, adjusting the offset
    let new_ptr_offset = src_interval.ptr_offset.map(|po| PtrOffset {
        anchor: po.anchor,
        offset: po.offset.saturating_add(imm),
        range: po.range,
    });

    state.set(dst, RegInterval {
        bounds: new_bounds,
        ptr_offset: new_ptr_offset,
    });
}

/// Assigns a concrete interval to a register
pub fn assign_interval(state: &mut IntervalState, r: Reg, min: i64, max: i64) {
    if r != Reg::Zero && !r.is_anchor() {
        state.set(r, RegInterval {
            bounds: ScalarBounds {
                smin: min,
                smax: max,
                umin: if min >= 0 { min as u64 } else { 0 },
                umax: if max >= 0 { max as u64 } else { u64::MAX },
            },
            ptr_offset: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
//  Arithmetic Transformations
// ══════════════════════════════════════════════════════════════════════════════

/// Performs dst += imm
pub fn apply_add_imm(state: &mut IntervalState, dst: Reg, imm: i64) {
    if dst == Reg::Zero || dst.is_anchor() {
        return;
    }

    let bounds = state.get_bounds_mut(dst);
    bounds.smin = bounds.smin.saturating_add(imm);
    bounds.smax = bounds.smax.saturating_add(imm);
    bounds.umin = bounds.umin.saturating_add(imm as u64);
    bounds.umax = bounds.umax.saturating_add(imm as u64);

    // Update pointer offset if present
    if let Some(ref mut po) = state.get_mut(dst).ptr_offset {
        po.offset = po.offset.saturating_add(imm);
    }
}

/// Performs dst += src
pub fn apply_add_reg(state: &mut IntervalState, dst: Reg, src: Reg) {
    if dst == Reg::Zero || dst.is_anchor() {
        return;
    }

    let src_bounds = state.get_bounds(src).clone();
    let dst_bounds = state.get_bounds_mut(dst);

    // Add intervals: [a, b] + [c, d] = [a+c, b+d]
    dst_bounds.smin = dst_bounds.smin.saturating_add(src_bounds.smin);
    dst_bounds.smax = dst_bounds.smax.saturating_add(src_bounds.smax);
    dst_bounds.umin = dst_bounds.umin.saturating_add(src_bounds.umin);
    dst_bounds.umax = dst_bounds.umax.saturating_add(src_bounds.umax);

    // Adding variable destroys fixed pointer offset precision
    // But we can preserve if src is constant
    if let Some(src_const) = src_bounds.get_constant() {
        if let Some(ref mut po) = state.get_mut(dst).ptr_offset {
            po.offset = po.offset.saturating_add(src_const);
        }
    } else {
        // Variable addition increases range
        if let Some(ref mut po) = state.get_mut(dst).ptr_offset {
            let src_range = src_bounds.umax.saturating_sub(src_bounds.umin);
            po.range = po.range.saturating_add(src_range);
        }
    }
}

/// Performs dst -= src
pub fn apply_sub_reg(state: &mut IntervalState, dst: Reg, src: Reg) {
    if dst == Reg::Zero || dst.is_anchor() {
        return;
    }

    let src_bounds = state.get_bounds(src).clone();
    let dst_bounds = state.get_bounds_mut(dst);

    // Subtract intervals: [a, b] - [c, d] = [a-d, b-c]
    dst_bounds.smin = dst_bounds.smin.saturating_sub(src_bounds.smax);
    dst_bounds.smax = dst_bounds.smax.saturating_sub(src_bounds.smin);
    dst_bounds.umin = dst_bounds.umin.saturating_sub(src_bounds.umax);
    dst_bounds.umax = dst_bounds.umax.saturating_sub(src_bounds.umin);

    // Subtracting variable destroys pointer offset info
    state.get_mut(dst).ptr_offset = None;
}

/// Performs dst &= mask (0 <= result <= mask for non-negative mask)
pub fn apply_and_imm(state: &mut IntervalState, dst: Reg, mask: i64) {
    if dst == Reg::Zero || dst.is_anchor() {
        return;
    }

    // AND with mask bounds result to [0, mask] for non-negative mask
    let bounds = state.get_bounds_mut(dst);
    if mask >= 0 {
        bounds.smin = 0;
        bounds.smax = mask;
        bounds.umin = 0;
        bounds.umax = mask as u64;
    } else {
        // Negative mask - conservative
        *bounds = ScalarBounds::unknown();
    }

    // AND destroys pointer relationship
    state.get_mut(dst).ptr_offset = None;
}

/// Performs dst *= imm
pub fn apply_mul_imm(state: &mut IntervalState, dst: Reg, imm: i64) {
    if dst == Reg::Zero || dst.is_anchor() {
        return;
    }

    if imm == 0 {
        assign_zero(state, dst);
        return;
    }

    if imm == 1 {
        return;
    }

    let bounds = state.get_bounds(dst).clone();

    if imm > 0 {
        // Positive multiplier preserves sign
        let new_bounds = ScalarBounds {
            smin: bounds.smin.saturating_mul(imm),
            smax: bounds.smax.saturating_mul(imm),
            umin: bounds.umin.saturating_mul(imm as u64),
            umax: bounds.umax.saturating_mul(imm as u64),
        };
        state.get_bounds_mut(dst).clone_from(&new_bounds);
    } else {
        // Negative multiplier - go conservative
        forget(state, dst);
        return;
    }

    // Multiplication destroys pointer relationship
    state.get_mut(dst).ptr_offset = None;
}

/// Performs reg /= imm
pub fn apply_div_imm(state: &mut IntervalState, reg: Reg, imm: i64) {
    if reg == Reg::Zero || reg.is_anchor() || imm == 0 {
        return;
    }

    let bounds = state.get_bounds(reg).clone();

    // Only handle positive divisor with non-negative dividend
    if imm > 0 && bounds.smin >= 0 {
        let new_bounds = ScalarBounds {
            smin: bounds.smin / imm,
            smax: bounds.smax / imm,
            umin: bounds.umin / (imm as u64),
            umax: bounds.umax / (imm as u64),
        };
        state.get_bounds_mut(reg).clone_from(&new_bounds);
    } else {
        forget(state, reg);
        return;
    }

    // Division destroys pointer relationship
    state.get_mut(reg).ptr_offset = None;
}

/// Performs dst /= src (conservative: forgets destination)
pub fn apply_div_reg(state: &mut IntervalState, dst: Reg) {
    forget(state, dst);
}

/// Performs reg = -reg
pub fn apply_neg(state: &mut IntervalState, reg: Reg) {
    if reg == Reg::Zero || reg.is_anchor() {
        return;
    }

    let bounds = state.get_bounds(reg).clone();
    let new_bounds = ScalarBounds {
        smin: bounds.smax.wrapping_neg(),
        smax: bounds.smin.wrapping_neg(),
        umin: 0, // Conservative for unsigned after negation
        umax: u64::MAX,
    };
    state.get_bounds_mut(reg).clone_from(&new_bounds);

    // Negation destroys pointer relationship
    state.get_mut(reg).ptr_offset = None;
}

// ══════════════════════════════════════════════════════════════════════════════
//  Constraint Refinement (Branch conditions)
// ══════════════════════════════════════════════════════════════════════════════

/// Assumes x <= y
pub fn assume_le(state: &mut IntervalState, x: Reg, y: Reg) {
    let y_max = state.get_bounds(y).smax;
    let x_min = state.get_bounds(x).smin;
    state.get_bounds_mut(x).assume_sle(y_max);
    state.get_bounds_mut(y).assume_sge(x_min);
}

/// Assumes x >= y
pub fn assume_ge(state: &mut IntervalState, x: Reg, y: Reg) {
    assume_le(state, y, x);
}

/// Assumes x > y
pub fn assume_gt(state: &mut IntervalState, x: Reg, y: Reg) {
    let y_max = state.get_bounds(y).smax;
    let x_min = state.get_bounds(x).smin;
    state.get_bounds_mut(x).assume_sge(y_max.saturating_add(1));
    state.get_bounds_mut(y).assume_sle(x_min.saturating_sub(1));
}

/// Assumes x <= y + c (not directly expressible without relational info)
/// We approximate by: x <= max(y) + c
pub fn assume_le_offset(state: &mut IntervalState, x: Reg, y: Reg, c: i64) {
    let y_max = state.get_bounds(y).smax;
    if y_max != i64::MAX {
        state.get_bounds_mut(x).assume_sle(y_max.saturating_add(c));
    }
}

/// Assumes x <= c
pub fn assume_le_imm(state: &mut IntervalState, x: Reg, c: i64) {
    state.get_bounds_mut(x).assume_sle(c);
}

/// Assumes x >= c
pub fn assume_ge_imm(state: &mut IntervalState, x: Reg, c: i64) {
    state.get_bounds_mut(x).assume_sge(c);
}

/// Assumes min <= x <= max
pub fn assume_range(state: &mut IntervalState, x: Reg, min: i64, max: i64) {
    assume_ge_imm(state, x, min);
    assume_le_imm(state, x, max);
}

/// Assumes x == c
pub fn assume_eq_imm(state: &mut IntervalState, x: Reg, c: i64) {
    if x != Reg::Zero && !x.is_anchor() {
        // Preserve pointer offset if it's consistent with the constant
        let ptr_offset = state.get_ptr_offset(x).cloned();
        state.set(x, RegInterval {
            bounds: ScalarBounds::constant(c),
            ptr_offset,
        });
    }
}

/// Assumes x < c
pub fn assume_lt_imm(state: &mut IntervalState, x: Reg, c: i64) {
    if c != i64::MIN {
        state.get_bounds_mut(x).assume_sle(c - 1);
    }
}

// ══════════════════════════════════════════════════════════════════════════════
//  Packet Geometry
// ══════════════════════════════════════════════════════════════════════════════

/// Establishes the invariant: data_meta <= data <= data_end
pub fn init_packet_anchors(state: &mut IntervalState) {
    // Set up anchor registers with their identity offsets
    state.set(Reg::AnchorDataMeta, RegInterval::with_ptr_offset(
        ScalarBounds::unknown(),
        PtrOffset::at_anchor(Reg::AnchorDataMeta),
    ));
    state.set(Reg::AnchorData, RegInterval::with_ptr_offset(
        ScalarBounds::unknown(),
        PtrOffset::at_anchor(Reg::AnchorData),
    ));
    state.set(Reg::AnchorDataEnd, RegInterval::with_ptr_offset(
        ScalarBounds::unknown(),
        PtrOffset::at_anchor(Reg::AnchorDataEnd),
    ));
    // Note: The ordering data_meta <= data <= data_end is implicit
    // and will be used during bounds checking
}

/// Binds a register to a packet anchor (reg == anchor)
pub fn bind_to_anchor(state: &mut IntervalState, reg: Reg, anchor: Reg) {
    if !anchor.is_anchor() {
        return;
    }

    state.set(reg, RegInterval::with_ptr_offset(
        ScalarBounds::unknown(), // Value unknown, but offset is known
        PtrOffset::at_anchor(anchor),
    ));
}

/// Check if a memory access [off, off + size) is within [anchor_start, anchor_end]
/// Returns (start_safe, end_safe)
pub fn check_region_access(
    state: &IntervalState,
    base: Reg,
    off: i64,
    size: i64,
    anchor_start: Reg,
    _anchor_end: Reg,
) -> (bool, bool) {
    let base_offset = state.get_ptr_offset(base);

    match base_offset {
        Some(po) if po.anchor == anchor_start => {
            // Base is relative to anchor_start
            // start_safe: base >= anchor_start, i.e., offset >= 0
            let min_off = po.min_offset().saturating_add(off);
            let start_safe = min_off >= 0;

            // end_safe: base + off + size <= anchor_end
            // This requires knowing anchor_end - anchor_start
            // Use packet_size_lower_bound if available
            let end_safe = if let Some(packet_size) = state.get_packet_size_bound() {
                let max_off = po.max_offset().saturating_add(off).saturating_add(size);
                max_off <= packet_size as i64
            } else {
                false // Cannot prove without knowing packet size
            };

            (start_safe, end_safe)
        }
        _ => {
            // Cannot determine relationship
            (false, false)
        }
    }
}

/// Convenience check for the packet metadata region [data_meta, data)
pub fn verify_packet_meta_bounds(state: &IntervalState, base: Reg, off: i64, size: i64) -> (bool, bool) {
    check_region_access(state, base, off, size, Reg::AnchorDataMeta, Reg::AnchorData)
}

/// Convenience check for the packet region [data, data_end)
pub fn verify_packet_bounds(state: &IntervalState, base: Reg, off: i64, size: i64) -> (bool, bool) {
    check_region_access(state, base, off, size, Reg::AnchorData, Reg::AnchorDataEnd)
}

/// Re-initializes anchoring constraints to their default states
pub fn reset_packet_anchors(state: &mut IntervalState) {
    init_packet_anchors(state);
    // Clear packet size bound since we're resetting
    // Note: This might be too aggressive - consider keeping if still valid
}

/// Merges anchor-to-anchor constraints from callee to caller
/// For interval domain, this is mostly a no-op since we don't track relations
pub fn preserve_anchor_constraints(_caller: &mut IntervalState, callee: &IntervalState) {
    // In interval domain, we might want to preserve packet_size_lower_bound
    // But since callee is separate, we generally don't merge these
    let _ = callee; // Acknowledge parameter
}
