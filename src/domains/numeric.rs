// Unified numeric domain abstraction
//
// This enum wraps the different numeric abstract domains (Zone, Interval)
// and provides a unified interface for the verifier.

use super::interval::IntervalState;
use super::interval::ops as interval_ops;
use super::zone::dbm::{Dbm, INF};
use super::zone::ops as zone_ops;
use crate::analysis::machine::reg::Reg;

/// Unified numeric domain that abstracts over Zone (DBM) and Interval
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NumericDomain {
    /// Zone domain using Difference Bound Matrix
    /// Tracks relational constraints: x - y <= c
    Zone(Dbm),

    /// Interval domain (kernel verifier style)
    /// Tracks per-register bounds only
    Interval(IntervalState),
}

impl NumericDomain {
    // ══════════════════════════════════════════════════════════════════════════
    //  Constructors
    // ══════════════════════════════════════════════════════════════════════════

    /// Create a new Zone domain
    pub fn new_zone() -> Self {
        NumericDomain::Zone(Dbm::new())
    }

    /// Create a new Interval domain
    pub fn new_interval() -> Self {
        NumericDomain::Interval(IntervalState::new())
    }

    /// Check if this is an Interval domain
    pub fn is_interval_mode(&self) -> bool {
        matches!(self, NumericDomain::Interval(_))
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Query & Interval Analysis
    // ══════════════════════════════════════════════════════════════════════════

    /// Extracts the interval [lower_bound, upper_bound] for a register
    pub fn get_interval(&self, x: Reg) -> (i64, i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::get_interval(dbm, x),
            NumericDomain::Interval(ivl) => interval_ops::get_interval(ivl, x),
        }
    }

    /// Returns the interval of the distance between two registers: [lo, hi] where lo <= x - y <= hi
    pub fn get_distance_interval(&self, x: Reg, y: Reg) -> (i64, i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::get_distance_interval(dbm, x, y),
            NumericDomain::Interval(ivl) => interval_ops::get_distance_interval(ivl, x, y),
        }
    }

    /// Extacts the 32-bit signed bounds for a register
    pub fn get_s32_bounds(&self, x: Reg) -> (i32, i32) {
        match self {
            NumericDomain::Zone(dbm) => {
                let b = &dbm.bounds[x.idx()];
                (b.s32_min, b.s32_max)
            }
            NumericDomain::Interval(ivl) => {
                let st = ivl.get_bounds(x);
                (st.smin as i32, st.smax as i32)
            }
        }
    }

    /// Returns the exact distance between two registers if constant
    pub fn get_distance_fixed(&self, x: Reg, y: Reg) -> Option<i64> {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::get_distance_fixed(dbm, x, y),
            NumericDomain::Interval(ivl) => interval_ops::get_distance_fixed(ivl, x, y),
        }
    }

    /// Returns the fixed concrete value of a register if constant
    pub fn get_fixed_value(&self, x: Reg) -> Option<i64> {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::get_fixed_value(dbm, x),
            NumericDomain::Interval(ivl) => interval_ops::get_fixed_value(ivl, x),
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Predicates & Proofs
    // ══════════════════════════════════════════════════════════════════════════

    /// Returns true if the register is proven to be exactly zero
    pub fn proven_zero(&self, x: Reg) -> bool {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::proven_zero(dbm, x),
            NumericDomain::Interval(ivl) => interval_ops::proven_zero(ivl, x),
        }
    }

    /// Returns true if the register is proven to be >= 0
    pub fn proven_nonnegative(&self, x: Reg) -> bool {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::proven_nonnegative(dbm, x),
            NumericDomain::Interval(ivl) => interval_ops::proven_nonnegative(ivl, x),
        }
    }

    /// Returns true if the register is proven to be > 0
    pub fn proven_positive(&self, x: Reg) -> bool {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::proven_positive(dbm, x),
            NumericDomain::Interval(ivl) => interval_ops::proven_positive(ivl, x),
        }
    }

    /// Returns true if a register is proven to be in the u32 range [0, 2^32-1]
    pub fn proven_u32_range(&self, v: Reg, _zero: Reg) -> bool {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::proven_u32_range(dbm, v, Reg::Zero),
            NumericDomain::Interval(ivl) => interval_ops::proven_u32_range(ivl, v),
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Value Assignments
    // ══════════════════════════════════════════════════════════════════════════

    /// Removes all constraints related to the specified register
    pub fn forget(&mut self, x: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::forget(dbm, x),
            NumericDomain::Interval(ivl) => interval_ops::forget(ivl, x),
        }
    }

    /// Overwrites a register with a specific constant value
    #[allow(dead_code)]
    pub fn assign_imm(&mut self, x: Reg, imm: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assign_imm(dbm, x, imm),
            NumericDomain::Interval(ivl) => interval_ops::assign_imm(ivl, x, imm),
        }
    }

    /// Overwrites a register with the value of another register
    pub fn assign_reg(&mut self, x: Reg, y: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assign_reg(dbm, x, y),
            NumericDomain::Interval(ivl) => interval_ops::assign_reg(ivl, x, y),
        }
    }

    /// Explicitly sets the 32-bit signed bounds for a register
    pub fn set_s32_bounds(&mut self, x: Reg, min: i32, max: i32) {
        match self {
            NumericDomain::Zone(dbm) => {
                dbm.bounds[x.idx()].s32_min = min;
                dbm.bounds[x.idx()].s32_max = max;
                zone_ops::sync_bounds(dbm, x);
            }
            NumericDomain::Interval(_) => {} // Not needed for this domain here
        }
    }

    /// Establishes the relationship dst = src + imm
    pub fn assign_reg_offset(&mut self, dst: Reg, src: Reg, imm: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assign_reg_offset(dbm, dst, src, imm),
            NumericDomain::Interval(ivl) => interval_ops::assign_reg_offset(ivl, dst, src, imm),
        }
    }

    /// Assigns a concrete interval to a register
    pub fn assign_interval(&mut self, r: Reg, min: i64, max: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assign_interval(dbm, r, min, max),
            NumericDomain::Interval(ivl) => interval_ops::assign_interval(ivl, r, min, max),
        }
    }

    /// Initializes a register as a map value pointer (interval mode only)
    /// Sets up PtrOffset tracking for bounds checking
    pub fn init_map_value_ptr(&mut self, reg: Reg) {
        if let NumericDomain::Interval(ivl) = self {
            interval_ops::init_map_value_ptr(ivl, reg);
        }
        // Zone domain doesn't need special setup - it tracks via DBM constraints
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Arithmetic Transformations
    // ══════════════════════════════════════════════════════════════════════════

    /// Performs dst += imm
    pub fn apply_add_imm(&mut self, dst: Reg, imm: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_add_imm(dbm, dst, imm),
            NumericDomain::Interval(ivl) => interval_ops::apply_add_imm(ivl, dst, imm),
        }
    }

    /// Performs dst += src
    pub fn apply_add_reg(&mut self, dst: Reg, src: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_add_reg(dbm, dst, src),
            NumericDomain::Interval(ivl) => interval_ops::apply_add_reg(ivl, dst, src),
        }
    }

    /// Performs dst = scalar_dst + ptr_src (interval mode only)
    /// Creates a new PtrOffset for dst combining ptr's offset with scalar's range
    pub fn apply_scalar_add_ptr(&mut self, dst: Reg, ptr_src: Reg, scalar_lo: i64, scalar_hi: i64) {
        if let NumericDomain::Interval(ivl) = self {
            interval_ops::apply_scalar_add_ptr(ivl, dst, ptr_src, scalar_lo, scalar_hi);
        }
        // Zone domain handles this via constraints, no special action needed
    }

    /// Performs dst -= src
    pub fn apply_sub_reg(&mut self, dst: Reg, src: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_sub_reg(dbm, dst, src),
            NumericDomain::Interval(ivl) => interval_ops::apply_sub_reg(ivl, dst, src),
        }
    }

    /// Performs dst &= mask
    pub fn apply_and_imm(&mut self, dst: Reg, mask: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_and_imm(dbm, dst, mask),
            NumericDomain::Interval(ivl) => interval_ops::apply_and_imm(ivl, dst, mask),
        }
    }

    /// Performs dst *= imm
    pub fn apply_mul_imm(&mut self, dst: Reg, imm: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_mul_imm(dbm, dst, imm),
            NumericDomain::Interval(ivl) => interval_ops::apply_mul_imm(ivl, dst, imm),
        }
    }

    /// Performs dst /= imm
    pub fn apply_div_imm(&mut self, reg: Reg, imm: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_div_imm(dbm, reg, imm),
            NumericDomain::Interval(ivl) => interval_ops::apply_div_imm(ivl, reg, imm),
        }
    }

    /// Performs dst /= src (conservative: forgets destination)
    pub fn apply_div_reg(&mut self, dst: Reg, _src: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_div_reg(dbm, dst, _src),
            NumericDomain::Interval(ivl) => interval_ops::apply_div_reg(ivl, dst),
        }
    }

    /// Performs reg = -reg
    pub fn apply_neg(&mut self, reg: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::apply_neg(dbm, reg),
            NumericDomain::Interval(ivl) => interval_ops::apply_neg(ivl, reg),
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Constraint Refinement (Branch conditions)
    // ══════════════════════════════════════════════════════════════════════════

    /// Assumes x <= y
    pub fn assume_le(&mut self, x: Reg, y: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_le(dbm, x, y),
            NumericDomain::Interval(ivl) => interval_ops::assume_le(ivl, x, y),
        }
    }

    /// Assumes x >= y
    pub fn assume_ge(&mut self, x: Reg, y: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_ge(dbm, x, y),
            NumericDomain::Interval(ivl) => interval_ops::assume_ge(ivl, x, y),
        }
    }

    /// Assumes x > y
    pub fn assume_gt(&mut self, x: Reg, y: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_gt(dbm, x, y),
            NumericDomain::Interval(ivl) => interval_ops::assume_gt(ivl, x, y),
        }
    }

    /// Assumes x <= y + c
    pub fn assume_le_offset(&mut self, x: Reg, y: Reg, c: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_le_offset(dbm, x, y, c),
            NumericDomain::Interval(ivl) => interval_ops::assume_le_offset(ivl, x, y, c),
        }
    }

    /// Assumes x <= c
    pub fn assume_le_imm(&mut self, x: Reg, c: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_le_imm(dbm, x, c),
            NumericDomain::Interval(ivl) => interval_ops::assume_le_imm(ivl, x, c),
        }
    }

    /// Assumes x >= c
    pub fn assume_ge_imm(&mut self, x: Reg, c: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_ge_imm(dbm, x, c),
            NumericDomain::Interval(ivl) => interval_ops::assume_ge_imm(ivl, x, c),
        }
    }

    /// Assumes min <= x <= max
    pub fn assume_range(&mut self, x: Reg, min: i64, max: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_range(dbm, x, min, max),
            NumericDomain::Interval(ivl) => interval_ops::assume_range(ivl, x, min, max),
        }
    }

    /// Assumes x == c
    pub fn assume_eq_imm(&mut self, x: Reg, c: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_eq_imm(dbm, x, c),
            NumericDomain::Interval(ivl) => interval_ops::assume_eq_imm(ivl, x, c),
        }
    }

    /// Assumes x < c
    pub fn assume_lt_imm(&mut self, x: Reg, c: i64) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::assume_lt_imm(dbm, x, c),
            NumericDomain::Interval(ivl) => interval_ops::assume_lt_imm(ivl, x, c),
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Width Truncation
    // ══════════════════════════════════════════════════════════════════════════

    /// Apply W32 truncation to a register's bounds.
    /// If the current bounds exceed [0, 0xFFFFFFFF], widen to that range.
    pub fn apply_w32_truncation(&mut self, dst: Reg) {
        let (lo, hi) = self.get_interval(dst);
        let safe = lo >= 0 && hi <= 0xFFFFFFFF;

        if !safe {
            // Check if the lower 32 bits form a non-wrapping range.
            let tight = if lo != i64::MIN && hi != i64::MAX {
                let l_u = lo as u64;
                let h_u = hi as u64;
                (l_u >> 32) == (h_u >> 32)
            } else {
                false
            };

            if tight {
                let new_lo = (lo as u64 & 0xFFFFFFFF) as i64;
                let new_hi = (hi as u64 & 0xFFFFFFFF) as i64;
                self.forget(dst);
                self.assume_ge_imm(dst, new_lo);
                self.assume_le_imm(dst, new_hi);
            } else {
                self.forget(dst);
                self.assume_ge_imm(dst, 0);
                self.assume_le_imm(dst, 0xFFFFFFFF);
            }
        }
    }

    /// Check if value is known to be in u32 range [0, 0xFFFFFFFF]
    pub fn fits_in_u32_range(&self, reg: Reg) -> bool {
        let (lo, hi) = self.get_interval(reg);
        if lo != i64::MIN && hi != i64::MAX {
            lo >= 0 && hi <= 0xFFFFFFFF
        } else {
            false
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Packet Geometry
    // ══════════════════════════════════════════════════════════════════════════

    /// Establishes the invariant: data_meta <= data <= data_end
    pub fn init_packet_anchors(&mut self) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::init_packet_anchors(dbm),
            NumericDomain::Interval(ivl) => interval_ops::init_packet_anchors(ivl),
        }
    }

    /// Binds a register to a packet anchor (reg == anchor)
    pub fn bind_to_anchor(&mut self, reg: Reg, anchor: Reg) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::bind_to_anchor(dbm, reg, anchor),
            NumericDomain::Interval(ivl) => interval_ops::bind_to_anchor(ivl, reg, anchor),
        }
    }

    /// Check if a memory access [off, off + size) is within [anchor_start, anchor_end]
    #[allow(dead_code)]
    pub fn check_region_access(
        &self,
        base: Reg,
        off: i64,
        size: i64,
        anchor_start: Reg,
        anchor_end: Reg,
    ) -> (bool, bool) {
        match self {
            NumericDomain::Zone(dbm) => {
                zone_ops::check_region_access(dbm, base, off, size, anchor_start, anchor_end)
            }
            NumericDomain::Interval(ivl) => {
                interval_ops::check_region_access(ivl, base, off, size, anchor_start, anchor_end)
            }
        }
    }

    /// Check for the packet metadata region [data_meta, data)
    pub fn verify_packet_meta_bounds(&self, base: Reg, off: i64, size: i64) -> (bool, bool) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::verify_packet_meta_bounds(dbm, base, off, size),
            NumericDomain::Interval(ivl) => {
                interval_ops::verify_packet_meta_bounds(ivl, base, off, size)
            }
        }
    }

    /// Check for the packet region [data, data_end)
    pub fn verify_packet_bounds(&self, base: Reg, off: i64, size: i64) -> (bool, bool) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::verify_packet_bounds(dbm, base, off, size),
            NumericDomain::Interval(ivl) => {
                interval_ops::verify_packet_bounds(ivl, base, off, size)
            }
        }
    }

    /// Re-initializes anchoring constraints to their default states
    pub fn reset_packet_anchors(&mut self) {
        match self {
            NumericDomain::Zone(dbm) => zone_ops::reset_packet_anchors(dbm),
            NumericDomain::Interval(ivl) => interval_ops::reset_packet_anchors(ivl),
        }
    }

    /// Clear packet and meta size bounds (interval mode only).
    /// Called when entering a function to match kernel behavior where each
    /// function tracks its own bounds independently.
    pub fn clear_packet_size_bounds(&mut self) {
        if let NumericDomain::Interval(ivl) = self {
            ivl.clear_packet_size_bounds();
        }
        // Zone mode doesn't have global packet size bounds - it uses DBM constraints
    }

    /// Merges anchor-to-anchor constraints from callee to caller
    pub fn preserve_anchor_constraints(&mut self, callee: &NumericDomain) {
        match (self, callee) {
            (NumericDomain::Zone(caller_dbm), NumericDomain::Zone(callee_dbm)) => {
                zone_ops::preserve_anchor_constraints(caller_dbm, callee_dbm)
            }
            (NumericDomain::Interval(caller_ivl), NumericDomain::Interval(callee_ivl)) => {
                interval_ops::preserve_anchor_constraints(caller_ivl, callee_ivl)
            }
            _ => {
                // Mismatched domains - should not happen in practice
                panic!("Cannot preserve anchor constraints between different domain types");
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  DBM-specific operations (for compatibility during migration)
    // ══════════════════════════════════════════════════════════════════════════

    /// Returns true if the domain is inconsistent (infeasible state)
    pub fn is_inconsistent(&self) -> bool {
        match self {
            NumericDomain::Zone(dbm) => dbm.is_inconsistent(),
            NumericDomain::Interval(ivl) => ivl.is_inconsistent(),
        }
    }

    /// Close the domain (compute transitive closure for Zone)
    pub fn close(&mut self) {
        match self {
            NumericDomain::Zone(dbm) => dbm.close(),
            NumericDomain::Interval(_ivl) => {
                // Interval domain doesn't need closure
            }
        }
    }

    /// Add a raw constraint i - j <= c (Zone-specific)
    pub fn add_constraint(&mut self, i: Reg, j: Reg, c: i64) {
        match self {
            NumericDomain::Zone(dbm) => {
                dbm.add_constraint(i, j, c);
            }
            NumericDomain::Interval(ivl) => {
                // Interval domain: convert relational constraint to bounds if possible
                // For i - Zero <= c: i <= c (upper bound on i)
                // For Zero - i <= c: i >= -c (lower bound on i)
                if j == Reg::Zero {
                    interval_ops::assume_le_imm(ivl, i, c);
                } else if i == Reg::Zero {
                    interval_ops::assume_ge_imm(ivl, j, -c);
                }
                // Other relational constraints cannot be expressed in interval domain
            }
        }
    }

    /// Get raw constraint value (Zone-specific)
    pub fn get(&self, i: Reg, j: Reg) -> i64 {
        match self {
            NumericDomain::Zone(dbm) => dbm.get(i, j),
            NumericDomain::Interval(_ivl) => {
                // Return INF (no constraint) for interval domain
                INF
            }
        }
    }

    /// Set raw constraint value (Zone-specific)
    #[allow(dead_code)]
    pub fn set(&mut self, i: Reg, j: Reg, val: i64) {
        match self {
            NumericDomain::Zone(dbm) => dbm.set(i, j, val),
            NumericDomain::Interval(_ivl) => {
                // Interval domain: no-op for relational constraints
            }
        }
    }

    /// Widen for loop convergence (Zone-specific, interval doesn't need it)
    pub fn widen(&self, newer: &NumericDomain) -> NumericDomain {
        match (self, newer) {
            (NumericDomain::Zone(old), NumericDomain::Zone(new)) => {
                NumericDomain::Zone(old.widen(new))
            }
            (NumericDomain::Interval(_), NumericDomain::Interval(new_ivl)) => {
                // Interval domain: no widening, preserve the newer state
                // (widening would corrupt the state by replacing it with old values)
                NumericDomain::Interval(new_ivl.clone())
            }
            _ => panic!("Cannot widen between different domain types"),
        }
    }

    /// Debug: dump the domain state
    pub fn dump(&self) {
        match self {
            NumericDomain::Zone(dbm) => dbm.pretty_print(),
            NumericDomain::Interval(_ivl) => {
                // TODO: Implement pretty print for interval domain
            }
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    //  Direct DBM access (for code that needs Zone-specific features)
    // ══════════════════════════════════════════════════════════════════════════

    /// Get reference to underlying Dbm if this is a Zone domain
    #[allow(dead_code)]
    pub fn as_zone(&self) -> Option<&Dbm> {
        match self {
            NumericDomain::Zone(dbm) => Some(dbm),
            NumericDomain::Interval(_) => None,
        }
    }

    /// Get mutable reference to underlying Dbm if this is a Zone domain
    #[allow(dead_code)]
    pub fn as_zone_mut(&mut self) -> Option<&mut Dbm> {
        match self {
            NumericDomain::Zone(dbm) => Some(dbm),
            NumericDomain::Interval(_) => None,
        }
    }

    /// Get reference to underlying IntervalState if this is an Interval domain
    #[allow(dead_code)]
    pub fn as_interval(&self) -> Option<&IntervalState> {
        match self {
            NumericDomain::Zone(_) => None,
            NumericDomain::Interval(ivl) => Some(ivl),
        }
    }

    /// Get mutable reference to underlying IntervalState if this is an Interval domain
    #[allow(dead_code)]
    pub fn as_interval_mut(&mut self) -> Option<&mut IntervalState> {
        match self {
            NumericDomain::Zone(_) => None,
            NumericDomain::Interval(ivl) => Some(ivl),
        }
    }

    /// Check if this is a Zone domain
    #[allow(dead_code)]
    pub fn is_zone(&self) -> bool {
        matches!(self, NumericDomain::Zone(_))
    }

    /// Check if this is an Interval domain
    #[allow(dead_code)]
    pub fn is_interval(&self) -> bool {
        matches!(self, NumericDomain::Interval(_))
    }
}

impl Default for NumericDomain {
    fn default() -> Self {
        NumericDomain::new_zone()
    }
}
