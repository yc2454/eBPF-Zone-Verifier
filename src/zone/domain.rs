// src/domain.rs
use crate::{common::utils::clamped_add, zone::dbm::{Dbm, INF}};
use crate::analysis::machine::reg::{Reg, REG_ENV};

// ══════════════════════════════════════════════════════════════════════════════
//  1. Query & Interval Analysis
//  Functions for extracting concrete bounds and intervals from the DBM.
// ══════════════════════════════════════════════════════════════════════════════

/// Extracts the interval [lower_bound, upper_bound] for a register if they are finite.
/// Returns (Option(lb), Option(ub)) where None represents infinity.
pub fn get_interval(dbm: &Dbm, x: Reg) -> (Option<i64>, Option<i64>) {
    let ub = dbm.get(x, Reg::Zero);
    let lb_neg = dbm.get(Reg::Zero, x);

    let ub_opt = if ub >= INF { None } else { Some(ub) };
    let lb_opt = if lb_neg >= INF { None } else { Some(-lb_neg) };

    (lb_opt, ub_opt)
}

/// Convenience version of `get_interval` that returns i64::MIN/MAX for infinite bounds.
pub fn get_interval_i64(dbm: &Dbm, x: Reg) -> (i64, i64) {
    let (lo_opt, hi_opt) = get_interval(dbm, x);
    let lo = lo_opt.unwrap_or(i64::MIN);
    let hi = hi_opt.unwrap_or(i64::MAX);
    (lo, hi)
}

/// Returns the interval of the distance between two registers: [lo, hi] such that lo <= x - y <= hi.
pub fn get_distance_interval(dbm: &Dbm, x: Reg, y: Reg) -> (Option<i64>, Option<i64>) {
    let x_minus_y = dbm.get(x, y);
    let y_minus_x = dbm.get(y, x);

    let ub_opt = if x_minus_y >= INF { None } else { Some(x_minus_y) };
    let lb_opt = if y_minus_x >= INF { None } else { Some(-y_minus_x) };

    (lb_opt, ub_opt)
}

/// Returns the exact distance between two registers if it is constant (lo == hi).
pub fn get_distance_fixed(dbm: &Dbm, x: Reg, y: Reg) -> Option<i64> {
    let (lo, hi) = get_distance_interval(dbm, x, y);
    match (lo, hi) {
        (Some(l), Some(h)) if l == h => Some(l),
        _ => None,
    }
}

/// Returns the fixed concrete value of a register if it is constant.
pub fn get_fixed_value(dbm: &Dbm, x: Reg) -> Option<i64> {
    if let (Some(lo), Some(hi)) = get_interval(dbm, x) {
        if lo == hi {
            return Some(lo);
        }
    }
    None
}

// ══════════════════════════════════════════════════════════════════════════════
//  2. Predicates & Proofs
//  Functions for verifying properties and properties about the current state.
// ══════════════════════════════════════════════════════════════════════════════

/// Returns true if the register is proven to be exactly zero.
pub fn proven_zero(dbm: &Dbm, x: Reg) -> bool {
    if let (Some(l), Some(u)) = get_interval(dbm, x) {
        l == u && l == 0
    } else {
        false
    }
}

/// Returns true if the register is proven to be >= 0.
pub fn proven_nonnegative(dbm: &Dbm, x: Reg) -> bool {
    let (lo, _) = get_interval(dbm, x);
    lo.map_or(false, |l| l >= 0)
}

/// Returns true if the register is proven to be > 0.
pub fn proven_positive(dbm: &Dbm, x: Reg) -> bool {
    let (lo, _) = get_interval(dbm, x);
    lo.map_or(false, |l| l > 0)
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
    dbm.close();
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
    d.close();
}

/// Performs dst += imm.
pub fn apply_add_imm(dbm: &mut Dbm, dst: Reg, imm: i64) {
    add_imm(dbm, dst, imm);
}

/// Performs dst += src. Shifts all dst's distance constraints by src's interval.
pub fn apply_add_reg(dbm: &mut Dbm, dst: Reg, src: Reg) {
    let (src_lo, src_hi) = get_interval(dbm, src);

    match (src_lo, src_hi) {
        (Some(lo), Some(hi)) => {
            let di = dst.idx();
            let n = dbm.num_vars();
            for j in 0..n {
                if j == di { continue; }
                let d_dj = dbm.get_idx(di, j);
                if d_dj < INF {
                    dbm.set_idx(di, j, clamped_add(d_dj, hi));
                }
                let d_jd = dbm.get_idx(j, di);
                if d_jd < INF {
                    dbm.set_idx(j, di, d_jd.saturating_sub(lo));
                }
            }
            dbm.set_idx(di, di, 0);
            dbm.close();
        }
        _ => {
            let (dst_lo, dst_hi) = get_interval(dbm, dst);
            dbm.forget_var(dst);
            if let (Some(dl), Some(sl)) = (dst_lo, src_lo) {
                assume_ge_imm(dbm, dst, dl.saturating_add(sl));
            }
            if let (Some(dh), Some(sh)) = (dst_hi, src_hi) {
                assume_le_imm(dbm, dst, dh.saturating_add(sh));
            }
            dbm.close();
        }
    }
}

/// Performs dst -= src.
pub fn apply_sub_reg(dbm: &mut Dbm, dst: Reg, src: Reg) {
    let (src_lo, src_hi) = get_interval(dbm, src);

    match (src_lo, src_hi) {
        (Some(lo), Some(hi)) => {
            let di = dst.idx();
            let n = dbm.num_vars();

            for j in 0..n {
                if j == di { continue; }
                let d_dj = dbm.get_idx(di, j);
                if d_dj < INF {
                    dbm.set_idx(di, j, d_dj.saturating_sub(lo));
                }
                let d_jd = dbm.get_idx(j, di);
                if d_jd < INF {
                    dbm.set_idx(j, di, clamped_add(d_jd, hi));
                }
            }
            dbm.set_idx(di, di, 0);
            dbm.close();
        }
        _ => {
            let (dst_lo, dst_hi) = get_interval(dbm, dst);
            dbm.forget_var(dst);
            if let (Some(dl), Some(sh)) = (dst_lo, src_hi) {
                assume_ge_imm(dbm, dst, dl.saturating_sub(sh));
            }
            if let (Some(dh), Some(sl)) = (dst_hi, src_lo) {
                assume_le_imm(dbm, dst, dh.saturating_sub(sl));
            }
            dbm.close();
        }
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

    let (ld_opt, ud_opt) = get_interval(dbm, dst);
    dbm.forget_var(dst);

    if let Some(ld) = ld_opt {
        let new_lb = ld.saturating_mul(imm);
        assume_ge_imm(dbm, dst, new_lb);
    }
    if let Some(ud) = ud_opt {
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
    let (lo, hi) = get_interval(dbm, reg);
    forget(dbm, reg);

    if let (Some(l), Some(h)) = (lo, hi) {
        if l >= 0 && h >= 0 {
            let new_lo = l / imm;
            let new_hi = h / imm;
            assume_ge_imm(dbm, reg, new_lo);
            assume_le_imm(dbm, reg, new_hi);
        }
    }
}

/// Performs dst /= src. Conservative: forgets the destination.
pub fn apply_div_reg(dbm: &mut Dbm, dst: Reg, _src: Reg) {
    forget(dbm, dst);
}

/// Performs reg = -reg. Scales/flips the bounds.
pub fn apply_neg(dbm: &mut Dbm, reg: Reg) {
    let (lo, hi) = get_interval(dbm, reg);
    forget(dbm, reg);

    if let (Some(l), Some(h)) = (lo, hi) {
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
    dbm.add_constraint(x, Reg::Zero, c);
    dbm.close();
}

/// Assumes x >= c.
pub fn assume_ge_imm(dbm: &mut Dbm, x: Reg, c: i64) {
    if c == i64::MIN {
        return; 
    }
    dbm.add_constraint(Reg::Zero, x, -c);
    dbm.close();
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
}

/// Assumes x < c.
pub fn assume_lt_imm(d: &mut Dbm, x: Reg, c: i64) {
    if c == i64::MIN {
        d.set(Reg::R0, Reg::R0, -1);
        return;
    }
    let bound = c - 1;
    d.add_constraint(x, Reg::Zero, bound);
    d.close();
}

// ══════════════════════════════════════════════════════════════════════════════
//  6. Packet Geometry
//  Management of packet boundaries (data, data_end, data_meta) and offset checks.
// ══════════════════════════════════════════════════════════════════════════════

/// Establishes the invariant: data_meta <= data <= data_end.
pub fn init_packet_anchors(dbm: &mut Dbm) {
    let meta = Reg::AnchorDataMeta;
    let data = Reg::AnchorData;
    let end  = Reg::AnchorDataEnd;

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
            if i == j { dbm.set_idx(i, j, 0); }
            else      { dbm.set_idx(i, j, INF); dbm.set_idx(j, i, INF); }
        }
    }
    init_packet_anchors(dbm);
}

/// Merges anchor-to-anchor constraints from callee to caller.
pub fn preserve_anchor_constraints(caller_dbm: &mut Dbm, callee_dbm: &Dbm) {
    let anchors = [Reg::AnchorData, Reg::AnchorDataEnd, Reg::AnchorDataMeta];
    for &a in &anchors {
        for &b in &anchors {
            if a == b { continue; }
            let callee_bound = callee_dbm.get(a, b);
            let caller_bound = caller_dbm.get(a, b);
            if callee_bound < caller_bound {
                caller_dbm.add_constraint(a, b, callee_bound);
            }
        }
    }
    caller_dbm.close();
}
