// Zone domain operations - high-level API for the DBM
use super::dbm::{Dbm, INF, clamped_add};
use crate::analysis::machine::reg::{REG_ENV, Reg};

// ══════════════════════════════════════════════════════════════════════════════
//  1. Query & Interval Analysis
//  Functions for extracting concrete bounds and intervals from the DBM.
// ══════════════════════════════════════════════════════════════════════════════

/// Extracts the interval [lower_bound, upper_bound] for a register.
/// Unbounded minimum is i64::MIN and unbounded maximum is i64::MAX.
pub fn get_interval(dbm: &Dbm, x: Reg) -> (i64, i64) {
    let ub = dbm.get(x, Reg::Zero);
    let lb_neg = dbm.get(Reg::Zero, x);

    let ub_val = if ub >= INF { i64::MAX } else { ub };
    let lb_val = if lb_neg >= INF { i64::MIN } else { -lb_neg };

    (lb_val, ub_val)
}

/// Returns the interval of the distance between two registers: [lo, hi] such that lo <= x - y <= hi.
pub fn get_distance_interval(dbm: &Dbm, x: Reg, y: Reg) -> (i64, i64) {
    let x_minus_y = dbm.get(x, y);
    let y_minus_x = dbm.get(y, x);

    let ub_val = if x_minus_y >= INF {
        i64::MAX
    } else {
        x_minus_y
    };
    let lb_val = if y_minus_x >= INF {
        i64::MIN
    } else {
        -y_minus_x
    };

    (lb_val, ub_val)
}

/// Returns the exact distance between two registers if it is constant (lo == hi).
pub fn get_distance_fixed(dbm: &Dbm, x: Reg, y: Reg) -> Option<i64> {
    let (lo, hi) = get_distance_interval(dbm, x, y);
    if lo == hi && lo != i64::MIN && lo != i64::MAX {
        Some(lo)
    } else {
        None
    }
}

/// Returns the fixed concrete value of a register if it is constant.
pub fn get_fixed_value(dbm: &Dbm, x: Reg) -> Option<i64> {
    let (lo, hi) = get_interval(dbm, x);
    if lo == hi && lo != i64::MIN && lo != i64::MAX {
        return Some(lo);
    }
    None
}

// ══════════════════════════════════════════════════════════════════════════════
//  2. Predicates & Proofs
//  Functions for verifying properties and properties about the current state.
// ══════════════════════════════════════════════════════════════════════════════

/// Returns true if the register is proven to be exactly zero.
pub fn proven_zero(dbm: &Dbm, x: Reg) -> bool {
    let (l, u) = get_interval(dbm, x);
    l == u && l == 0
}

/// Returns true if the register is proven to be >= 0.
pub fn proven_nonnegative(dbm: &Dbm, x: Reg) -> bool {
    let (lo, _) = get_interval(dbm, x);
    lo >= 0
}

/// Returns true if the register is proven to be > 0.
pub fn proven_positive(dbm: &Dbm, x: Reg) -> bool {
    let (lo, _) = get_interval(dbm, x);
    lo > 0
}

/// Returns true if a register is proven to be in the u32 range [0, 2^32-1].
pub fn proven_u32_range(dbm: &Dbm, v: Reg, zero: Reg) -> bool {
    let vi = REG_ENV.index(v);
    let zi = REG_ENV.index(zero);
    let ub = dbm.raw(vi, zi);
    let lb = dbm.raw(zi, vi);
    // 0 <= v <= u32::MAX
    ub <= 0xffff_ffff && lb <= 0
}

// ══════════════════════════════════════════════════════════════════════════════
//  3. Value Assignments
//  Destructive updates that overwrite a register's current state.
// ══════════════════════════════════════════════════════════════════════════════

/// Removes all constraints related to the specified register.
pub fn forget(dbm: &mut Dbm, x: Reg) {
    dbm.forget_var(x);
    dbm.close(); // Maintain the "always closed" invariant
}

/// Overwrites a register with a specific constant value.
pub fn assign_imm(dbm: &mut Dbm, x: Reg, imm: i64) {
    dbm.forget_var(x);
    dbm.add_constraint(x, Reg::Zero, imm);
    if imm > i64::MIN {
        dbm.add_constraint(Reg::Zero, x, -imm);
    }
    dbm.bounds[x.idx()].s64_min = imm;
    dbm.bounds[x.idx()].s64_max = imm;
    dbm.close();
    sync_bounds(dbm, x);
}

/// Overwrites a register with zero.
pub fn assign_zero(dbm: &mut Dbm, x: Reg) {
    assign_imm(dbm, x, 0);
}

/// Overwrites a register with the value of another register.
pub fn assign_reg(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.forget_var(x);
    dbm.add_constraint(x, y, 0);
    dbm.add_constraint(y, x, 0);
    dbm.close();
}

/// Establishes the relationship dst = src + imm (i.e., dst - src = imm).
pub fn assign_reg_offset(dbm: &mut Dbm, dst: Reg, src: Reg, imm: i64) {
    dbm.forget_var(dst);
    dbm.add_constraint(dst, src, imm);
    if imm > i64::MIN {
        dbm.add_constraint(src, dst, -imm);
    }
    dbm.close();
}

/// Utility to assign a concrete interval to a register.
pub fn assign_interval(dbm: &mut Dbm, r: Reg, min: i64, max: i64) {
    dbm.forget_var(r);
    assume_range(dbm, r, min, max);
    dbm.close();
}

// ══════════════════════════════════════════════════════════════════════════════
//  4. Arithmetic Transformations
//  Calculates the new state after an arithmetic operation (e.g., add, mul).
// ══════════════════════════════════════════════════════════════════════════════

/// Internal helper to shift a register's constraints by a constant (x = x + c).
pub fn add_imm(d: &mut Dbm, x: Reg, c: i64) {
    let xi = x.idx();
    let n = d.num_vars();

    for zj in 0..n {
        let old_xz = d.get_idx(xi, zj);
        if old_xz < INF {
            d.set_idx(xi, zj, old_xz.saturating_add(c));
        }
    }
    for zi in 0..n {
        let old_zx = d.get_idx(zi, xi);
        if old_zx < INF {
            d.set_idx(zi, xi, old_zx.saturating_sub(c));
        }
    }
    d.set_idx(xi, xi, 0);

    let b = &mut d.bounds[xi];
    b.s64_min = b.s64_min.saturating_add(c);
    b.s64_max = b.s64_max.saturating_add(c);
    b.u64_min = 0;
    b.u64_max = u64::MAX;
    b.s32_min = i32::MIN;
    b.s32_max = i32::MAX;
    b.u32_min = 0;
    b.u32_max = u32::MAX;

    d.close();
}

/// Performs dst += imm.
pub fn apply_add_imm(dbm: &mut Dbm, dst: Reg, imm: i64) {
    add_imm(dbm, dst, imm);
}

/// Performs dst += src. Shifts all dst's distance constraints by src's interval.
pub fn apply_add_reg(dbm: &mut Dbm, dst: Reg, src: Reg) {
    let (src_lo, src_hi) = get_interval(dbm, src);

    if src_lo != i64::MIN && src_hi != i64::MAX {
        let di = dst.idx();
        let n = dbm.num_vars();
        for j in 0..n {
            if j == di {
                continue;
            }
            let d_dj = dbm.get_idx(di, j);
            if d_dj < INF {
                dbm.set_idx(di, j, clamped_add(d_dj, src_hi));
            }
            let d_jd = dbm.get_idx(j, di);
            if d_jd < INF {
                dbm.set_idx(j, di, d_jd.saturating_sub(src_lo));
            }
        }
        dbm.set_idx(di, di, 0);

        let b = &mut dbm.bounds[di];
        b.s64_min = b.s64_min.saturating_add(src_lo);
        b.s64_max = b.s64_max.saturating_add(src_hi);
        b.u64_min = 0;
        b.u64_max = u64::MAX;
        b.s32_min = i32::MIN;
        b.s32_max = i32::MAX;
        b.u32_min = 0;
        b.u32_max = u32::MAX;

        dbm.close();
    } else {
        let (dst_lo, dst_hi) = get_interval(dbm, dst);
        dbm.forget_var(dst);
        if dst_lo != i64::MIN && src_lo != i64::MIN {
            assume_ge_imm(dbm, dst, dst_lo.saturating_add(src_lo));
        }
        if dst_hi != i64::MAX && src_hi != i64::MAX {
            assume_le_imm(dbm, dst, dst_hi.saturating_add(src_hi));
        }
        dbm.close();
    }
}

/// Performs dst -= src.
pub fn apply_sub_reg(dbm: &mut Dbm, dst: Reg, src: Reg) {
    let (src_lo, src_hi) = get_interval(dbm, src);

    if src_lo != i64::MIN && src_hi != i64::MAX {
        let di = dst.idx();
        let n = dbm.num_vars();

        for j in 0..n {
            if j == di {
                continue;
            }
            let d_dj = dbm.get_idx(di, j);
            if d_dj < INF {
                dbm.set_idx(di, j, d_dj.saturating_sub(src_lo));
            }
            let d_jd = dbm.get_idx(j, di);
            if d_jd < INF {
                dbm.set_idx(j, di, clamped_add(d_jd, src_hi));
            }
        }
        dbm.set_idx(di, di, 0);

        let b = &mut dbm.bounds[di];
        b.s64_min = b.s64_min.saturating_sub(src_hi);
        b.s64_max = b.s64_max.saturating_sub(src_lo);
        b.u64_min = 0;
        b.u64_max = u64::MAX;
        b.s32_min = i32::MIN;
        b.s32_max = i32::MAX;
        b.u32_min = 0;
        b.u32_max = u32::MAX;

        dbm.close();
    } else {
        let (dst_lo, dst_hi) = get_interval(dbm, dst);
        dbm.forget_var(dst);
        if dst_lo != i64::MIN && src_hi != i64::MAX {
            assume_ge_imm(dbm, dst, dst_lo.saturating_sub(src_hi));
        }
        if dst_hi != i64::MAX && src_lo != i64::MIN {
            assume_le_imm(dbm, dst, dst_hi.saturating_sub(src_lo));
        }
        dbm.close();
    }
}

/// Performs dst &= mask. Establishes the bounded property 0 <= dst <= mask.
pub fn apply_and_imm(dbm: &mut Dbm, dst: Reg, mask: i64) {
    dbm.forget_var(dst);
    dbm.add_constraint(dst, Reg::Zero, mask);
    dbm.add_constraint(Reg::Zero, dst, 0);
    dbm.close();
}

/// Performs dst *= imm. Scales the bounds if the multiplier is positive.
pub fn apply_mul_imm(dbm: &mut Dbm, dst: Reg, imm: i64) {
    if imm == 0 {
        assign_zero(dbm, dst);
        return;
    }
    if imm == 1 {
        return;
    }
    if imm < 0 {
        forget(dbm, dst);
        return;
    }

    let (ld, ud) = get_interval(dbm, dst);
    dbm.forget_var(dst);

    if ld != i64::MIN {
        let new_lb = ld.saturating_mul(imm);
        assume_ge_imm(dbm, dst, new_lb);
    }
    if ud != i64::MAX {
        let new_ub = ud.saturating_mul(imm);
        assume_le_imm(dbm, dst, new_ub);
    }
    dbm.close();
}

/// Performs dst /= imm.
pub fn apply_div_imm(dbm: &mut Dbm, reg: Reg, imm: i64) {
    if imm == 0 {
        return;
    }
    let (l, h) = get_interval(dbm, reg);
    forget(dbm, reg);

    if l != i64::MIN && h != i64::MAX && l >= 0 && h >= 0 {
        let new_lo = l / imm;
        let new_hi = h / imm;
        assume_ge_imm(dbm, reg, new_lo);
        assume_le_imm(dbm, reg, new_hi);
    }
}

/// Performs dst /= src. Conservative: forgets the destination.
pub fn apply_div_reg(dbm: &mut Dbm, dst: Reg, _src: Reg) {
    forget(dbm, dst);
}

/// Performs reg = -reg. Scales/flips the bounds.
pub fn apply_neg(dbm: &mut Dbm, reg: Reg) {
    let (l, h) = get_interval(dbm, reg);
    forget(dbm, reg);

    if l != i64::MIN && h != i64::MAX {
        let new_lo = h.wrapping_neg();
        let new_hi = l.wrapping_neg();
        assume_ge_imm(dbm, reg, new_lo);
        assume_le_imm(dbm, reg, new_hi);
    }
}

// ══════════════════════════════════════════════════════════════════════════════
//  5. Constraint Refinement
//  Non-destructive operations that narrow the possible values based on branches.
// ══════════════════════════════════════════════════════════════════════════════

/// Assumes x <= y.
pub fn assume_le(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(x, y, 0);
    dbm.close();
}

/// Assumes x >= y.
pub fn assume_ge(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(y, x, 0);
    dbm.close();
}

/// Assumes x > y.
pub fn assume_gt(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(y, x, -1);
    dbm.close();
}

/// Assumes x <= y + c.
pub fn assume_le_offset(dbm: &mut Dbm, x: Reg, y: Reg, c: i64) {
    dbm.add_constraint(x, y, c);
    dbm.close();
}

/// Assumes x <= c.
pub fn assume_le_imm(dbm: &mut Dbm, x: Reg, c: i64) {
    if c == i64::MAX || c >= INF {
        return;
    }
    dbm.add_constraint(x, Reg::Zero, c);
    dbm.close();
    sync_bounds(dbm, x);
}

/// Assumes x >= c.
pub fn assume_ge_imm(dbm: &mut Dbm, x: Reg, c: i64) {
    if c == i64::MIN {
        return;
    }
    dbm.add_constraint(Reg::Zero, x, -c);
    dbm.close();
    sync_bounds(dbm, x);
}

/// Assumes min <= x <= max.
pub fn assume_range(dbm: &mut Dbm, x: Reg, min: i64, max: i64) {
    assume_ge_imm(dbm, x, min);
    assume_le_imm(dbm, x, max);
}

/// Assumes x == c.
pub fn assume_eq_imm(dbm: &mut Dbm, x: Reg, c: i64) {
    dbm.add_constraint(x, Reg::Zero, c);
    if c > i64::MIN {
        dbm.add_constraint(Reg::Zero, x, -c);
    }
    dbm.close();
    sync_bounds(dbm, x);
}

/// Assumes x < c.
pub fn assume_lt_imm(d: &mut Dbm, x: Reg, c: i64) {
    if c == i64::MIN {
        d.set(Reg::R0, Reg::R0, -1);
        return;
    }
    if c == i64::MAX || c >= INF {
        return;
    }
    let bound = c - 1;
    d.add_constraint(x, Reg::Zero, bound);
    d.close();
    sync_bounds(d, x);
}

// ══════════════════════════════════════════════════════════════════════════════
//  6. Packet Geometry
//  Management of packet boundaries (data, data_end, data_meta) and offset checks.
// ══════════════════════════════════════════════════════════════════════════════

/// Establishes the invariant: data_meta <= data <= data_end.
pub fn init_packet_anchors(dbm: &mut Dbm) {
    let meta = Reg::AnchorDataMeta;
    let data = Reg::AnchorData;
    let end = Reg::AnchorDataEnd;

    dbm.add_constraint(meta, data, 0);
    dbm.add_constraint(data, end, 0);
    dbm.close();
}

/// Binds a register to a packet anchor (reg == anchor).
pub fn bind_to_anchor(dbm: &mut Dbm, reg: Reg, anchor: Reg) {
    debug_assert!(anchor.is_anchor(), "bind_to_anchor requires an anchor");
    dbm.add_constraint(reg, anchor, 0);
    dbm.add_constraint(anchor, reg, 0);
    dbm.close();
}

/// Core function to check if a memory access [off, off + size) is within [anchor_start, anchor_end].
/// Returns (start_safe, end_safe).
pub fn check_region_access(
    dbm: &Dbm,
    base: Reg,
    off: i64,
    size: i64,
    anchor_start: Reg,
    anchor_end: Reg,
) -> (bool, bool) {
    let start_bound = dbm.get(anchor_start, base);
    let start_safe = start_bound < INF && start_bound <= off;

    let end_bound = dbm.get(base, anchor_end);
    let end_safe = end_bound < INF && (end_bound + off + size) <= 0;

    (start_safe, end_safe)
}

/// Convenience check for the packet metadata region [data_meta, data).
pub fn verify_packet_meta_bounds(dbm: &Dbm, base: Reg, off: i64, size: i64) -> (bool, bool) {
    check_region_access(dbm, base, off, size, Reg::AnchorDataMeta, Reg::AnchorData)
}

/// Convenience check for the packet region [data, data_end).
pub fn verify_packet_bounds(dbm: &Dbm, base: Reg, off: i64, size: i64) -> (bool, bool) {
    check_region_access(dbm, base, off, size, Reg::AnchorData, Reg::AnchorDataEnd)
}

/// Re-initializes anchoring constraints to their default states.
pub fn reset_packet_anchors(dbm: &mut Dbm) {
    for &anchor in &[Reg::AnchorDataMeta, Reg::AnchorData, Reg::AnchorDataEnd] {
        let i = anchor.idx();
        let n = dbm.num_vars();
        for j in 0..n {
            if i == j {
                dbm.set_idx(i, j, 0);
            } else {
                dbm.set_idx(i, j, INF);
                dbm.set_idx(j, i, INF);
            }
        }
    }
    init_packet_anchors(dbm);
}

/// Merges anchor-to-anchor constraints from callee to caller.
pub fn preserve_anchor_constraints(caller_dbm: &mut Dbm, callee_dbm: &Dbm) {
    let anchors = [Reg::AnchorData, Reg::AnchorDataEnd, Reg::AnchorDataMeta];
    for &a in &anchors {
        for &b in &anchors {
            if a == b {
                continue;
            }
            let callee_bound = callee_dbm.get(a, b);
            let caller_bound = caller_dbm.get(a, b);
            if callee_bound < caller_bound {
                caller_dbm.add_constraint(a, b, callee_bound);
            }
        }
    }
    caller_dbm.close();
}

/// Synchronizes the relational DBM constraints with absolute 4-tuple bounds for a given register.
/// Implements the Sync Contract to prevent divergence.
pub fn sync_bounds(dbm: &mut Dbm, x: Reg) {
    if x == Reg::Zero || x.is_anchor() {
        return;
    }

    let idx = x.idx();

    // 1. DBM -> Bounds (s64 wrapper)
    let dbm_max = dbm.get(x, Reg::Zero);
    if dbm_max < INF {
        dbm.bounds[idx].s64_max = dbm.bounds[idx].s64_max.min(dbm_max);
    }
    let dbm_min_neg = dbm.get(Reg::Zero, x);
    if dbm_min_neg < INF {
        dbm.bounds[idx].s64_min = dbm.bounds[idx].s64_min.max(-dbm_min_neg);
    }

    // 2. Cross-pollinate bounds within the bounds array
    let b = &mut dbm.bounds[idx];

    // s64 <-> u64
    if b.s64_min >= 0 {
        b.u64_min = b.u64_min.max(b.s64_min as u64);
        b.u64_max = b.u64_max.min(b.s64_max as u64);
    }
    if b.u64_max <= i64::MAX as u64 {
        b.s64_min = b.s64_min.max(b.u64_min as i64);
        b.s64_max = b.s64_max.min(b.u64_max as i64);
    }

    // s32 <-> u32
    if b.s32_min >= 0 {
        b.u32_min = b.u32_min.max(b.s32_min as u32);
        b.u32_max = b.u32_max.min(b.s32_max as u32);
    }
    if b.u32_max <= i32::MAX as u32 {
        b.s32_min = b.s32_min.max(b.u32_min as i32);
        b.s32_max = b.s32_max.min(b.u32_max as i32);
    }

    // 64-bit into 32-bit (if fitting completely)
    if b.s64_min >= i32::MIN as i64 && b.s64_max <= i32::MAX as i64 {
        b.s32_min = b.s32_min.max(b.s64_min as i32);
        b.s32_max = b.s32_max.min(b.s64_max as i32);
    }
    if b.u64_max <= u32::MAX as u64 {
        b.u32_min = b.u32_min.max(b.u64_min as u32);
        b.u32_max = b.u32_max.min(b.u64_max as u32);
    }

    // 32-bit back into 64-bit (only valid if we already know top 32 bits are clean due to zero-extension)
    if b.u64_max <= u32::MAX as u64 {
        b.u64_min = b.u64_min.max(b.u32_min as u64);
        b.u64_max = b.u64_max.min(b.u32_max as u64);

        // At this point, u64_max <= u32::MAX, which is < i64::MAX, so s64 is non-negative
        b.s64_min = b.s64_min.max(b.u64_min as i64);
        b.s64_max = b.s64_max.min(b.u64_max as i64);
    }

    // 3. Bounds -> DBM (s64 back to relational edge)
    let final_s64_max = b.s64_max;
    let final_s64_min = b.s64_min;

    // Drop mutable borrow of dbm.bounds before calling dbm.add_constraint

    if final_s64_max < i64::MAX {
        dbm.add_constraint(x, Reg::Zero, final_s64_max);
    }
    if final_s64_min > i64::MIN {
        dbm.add_constraint(Reg::Zero, x, -final_s64_min);
    }
}
