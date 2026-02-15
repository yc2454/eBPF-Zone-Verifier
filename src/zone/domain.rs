// src/domain.rs
use crate::{common::utils::clamped_add, zone::dbm::{Dbm, INF}};
use crate::analysis::machine::reg::{Reg, REG_ENV};

/// --- analysis helpers ---
/// 
// Extract bounds if finite.
// ub from: x - 0 <= ub
// lb from: 0 - x <= -lb  => lb = - (0 - x bound)
pub fn get_bounds(dbm: &Dbm, x: Reg) -> (Option<i64>, Option<i64>) {
    let ub = dbm.get(x, Reg::Zero);
    let lb_neg = dbm.get(Reg::Zero, x);

    let ub_opt = if ub >= INF { None } else { Some(ub) };
    let lb_opt = if lb_neg >= INF { None } else { Some(-lb_neg) };

    (lb_opt, ub_opt)
}

pub fn get_simple_bounds(dbm: &Dbm, x: Reg) -> (i64, i64) {
    let (lo_opt, hi_opt) = get_bounds(dbm, x);
    let lo = lo_opt.unwrap_or(i64::MIN);
    let hi = hi_opt.unwrap_or(i64::MAX);
    (lo, hi)
}

pub fn get_relative_bound(dbm: &Dbm, x: Reg, y: Reg) -> (Option<i64>, Option<i64>) {
    let x_minus_y = dbm.get(x, y);
    let y_minus_x = dbm.get(y, x);

    let ub_opt = if x_minus_y >= INF { None } else { Some(x_minus_y) };
    let lb_opt = if y_minus_x >= INF { None } else { Some(-y_minus_x) };

    (lb_opt, ub_opt)
}

pub fn get_relative_constant(dbm: &Dbm, x: Reg, y: Reg) -> Option<i64> {
    let (lo, hi) = get_relative_bound(dbm, x, y);
    match (lo, hi) {
        (Some(l), Some(h)) if l == h => Some(l),
        _ => None,
    }
}

pub fn get_constant_value(dbm: &Dbm, x: Reg) -> Option<i64> {
    if let (Some(lo), Some(hi)) = get_bounds(dbm, x) {
        if lo == hi {
            return Some(lo);
        }
    }
    None
}

pub fn is_zero(dbm: &Dbm, x: Reg) -> bool {
    if let (Some(l), Some(u)) = get_bounds(dbm, x) {
        return l == u && l == 0;
    } else {
        return false;
    }
}

pub fn nonneg(dbm: &Dbm, x: Reg) -> bool {
    let (lo, _) = get_bounds(dbm, x);
    lo.map_or(false, |l| l >= 0)
}

pub fn positive(dbm: &Dbm, x: Reg) -> bool {
    let (lo, _) = get_bounds(dbm, x);
    lo.map_or(false, |l| l > 0)
}

pub fn set_bounds(dbm: &mut Dbm, r: Reg, min: i64, max: i64) {
    assume_ge_const(dbm, r, min);
    assume_le_const(dbm, r, max);
}

// --- transfer functions ---
// exec.rs wants a uniform name.
pub fn forget(dbm: &mut Dbm, x: Reg) {
    dbm.forget_var(x);
    dbm.close(); // keep the "always closed" invariant
}

/// Establishes the relationship dst = src + imm (i.e., dst - src = imm)
/// This records the exact difference between two registers in the DBM.
pub fn link_regs_with_offset(dbm: &mut Dbm, dst: Reg, src: Reg, imm: i64) {
    // 1. Clear any old information about the destination register
    dbm.forget_var(dst);

    // 2. Add the bidirectional constraints to enforce equality: dst - src == imm
    // dst - src <= imm
    dbm.add_constraint(dst, src, imm);

    // src - dst <= -imm (equivalent to dst - src >= imm)
    // Handle i64::MIN edge case to avoid negation panic
    if imm > i64::MIN {
        dbm.add_constraint(src, dst, -imm);
    }

    // 3. Re-close the DBM to propagate this new relationship to other registers
    // (e.g., if src was linked to R10, dst is now also linked to R10)
    dbm.close();
}

// dst += imm
pub fn assign_add_imm(dbm: &mut Dbm, dst: Reg, imm: i64) {
    add_imm(dbm, dst, imm);
}

// dst += src
pub fn assign_add_reg(dbm: &mut Dbm, dst: Reg, src: Reg) {
    let (src_lo, src_hi) = get_bounds(dbm, src);

    match (src_lo, src_hi) {
        (Some(lo), Some(hi)) => {
            // src ∈ [lo, hi], so shift dst's relationships by that interval:
            //   new(dst - z) <= old(dst - z) + hi
            //   new(z - dst) <= old(z - dst) - lo
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
            // src is unbounded — no choice but to lose relational info
            let (dst_lo, dst_hi) = get_bounds(dbm, dst);
            dbm.forget_var(dst);
            if let (Some(dl), Some(sl)) = (dst_lo, src_lo) {
                assume_ge_const(dbm, dst, dl.saturating_add(sl));
            }
            if let (Some(dh), Some(sh)) = (dst_hi, src_hi) {
                assume_le_const(dbm, dst, dh.saturating_add(sh));
            }
            dbm.close();
        }
    }
}

/// Handle: dst = dst - src
pub fn assign_sub_reg(dbm: &mut Dbm, dst: Reg, src: Reg) {
    let (src_lo, src_hi) = get_bounds(dbm, src);

    match (src_lo, src_hi) {
        (Some(lo), Some(hi)) => {
            // dst -= src where src ∈ [lo, hi]
            //   new(dst - z) <= old(dst - z) - lo
            //   new(z - dst) <= old(z - dst) + hi
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
            let (dst_lo, dst_hi) = get_bounds(dbm, dst);
            dbm.forget_var(dst);
            if let (Some(dl), Some(sh)) = (dst_lo, src_hi) {
                assume_ge_const(dbm, dst, dl.saturating_sub(sh));
            }
            if let (Some(dh), Some(sl)) = (dst_hi, src_lo) {
                assume_le_const(dbm, dst, dh.saturating_sub(sl));
            }
            dbm.close();
        }
    }
}

// dst &= mask
pub fn assign_and_mask(dbm: &mut Dbm, dst: Reg, mask: i64) {
    dbm.forget_var(dst);
    
    // 0 <= dst <= mask
    dbm.add_constraint(dst, Reg::Zero, mask);
    dbm.add_constraint(Reg::Zero, dst, 0);

    dbm.close();
}

// x <= y  encoded as: x - y <= 0
pub fn assume_le_var(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(x, y, 0);
    dbm.close();
}

// x >= y  encoded as: y - x <= 0
pub fn assume_ge_var(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(y, x, 0);
    dbm.close();
}

// x > y  encoded as: y - x <= -1
pub fn assume_gt_var(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.add_constraint(y, x, -1);
    dbm.close();
}

// x <= y + c  encoded as: x - y <= c
pub fn assume_le_var_plus_const(dbm: &mut Dbm, x: Reg, y: Reg, c: i64) {
    dbm.add_constraint(x, y, c);
    dbm.close();
}

pub fn assign_zero(dbm: &mut Dbm, x: Reg) {
    // Overwrite x: kill all old info about x
    dbm.forget_var(x);

    // Now enforce x == 0 (relative to `zero` var)
    dbm.add_constraint(x, Reg::Zero, 0);   // x - 0 ≤ 0  ⇒ x ≤ 0
    dbm.add_constraint(Reg::Zero, x, 0);   // 0 - x ≤ 0  ⇒ x ≥ 0

    dbm.close();
}

pub fn assign_eq(dbm: &mut Dbm, x: Reg, y: Reg) {
    dbm.forget_var(x);
    dbm.add_constraint(x, y, 0);
    dbm.add_constraint(y, x, 0);
    dbm.close();
}

// x <= c   encoded as: x - 0 <= c
pub fn assume_le_const(dbm: &mut Dbm, x: Reg, c: i64) {
    dbm.add_constraint(x, Reg::Zero, c);
    dbm.close();
}

// x >= c   encoded as: 0 - x <= -c
pub fn assume_ge_const(dbm: &mut Dbm, x: Reg, c: i64) {
    // Since x is an i64, x >= i64::MIN is always true (tautology).
    // Attempting -c would panic, so we simply skip adding the constraint.
    if c == i64::MIN {
        return; 
    }

    dbm.add_constraint(Reg::Zero, x, -c);
    dbm.close();
}

// lo <= x <= hi
pub fn assume_range(dbm: &mut Dbm, x: Reg, lo: i64, hi: i64) {
    assume_ge_const(dbm, x, lo);
    assume_le_const(dbm, x, hi);
}

// x == c   encoded as: x <= c AND x >= c
pub fn assume_eq_const(dbm: &mut Dbm, x: Reg, c: i64) {
    dbm.add_constraint(x, Reg::Zero, c);
    if c > i64::MIN {
        dbm.add_constraint(Reg::Zero, x, -c);
    }
    dbm.close();
}

pub fn assume_less_than(d: &mut Dbm, x: Reg, c: i64) {
    // Handle edge case where c is i64::MIN.
    // x < i64::MIN is impossible (contradiction).
    // In a DBM, we represent "impossible" by setting the matrix to an inconsistent state.
    if c == i64::MIN {
        // Mark DBM as inconsistent (0 - 0 <= -1 is false)
        d.set(Reg::R0, Reg::R0, -1);
        return;
    }
    let bound = c - 1;
    d.add_constraint(x, Reg::Zero, bound);
    d.close();
}

pub fn add_imm(d: &mut Dbm, x: Reg, c: i64) {
    let xi = x.idx();
    let n = d.num_vars();

    // Shift row/col for x
    for zj in 0..n {
        // x - z <= old(x - z) + c
        let old_xz = d.get_idx(xi, zj);
        if old_xz < INF {
            d.set_idx(xi, zj, old_xz.saturating_add(c));
        }
    }
    for zi in 0..n {
        // z - x <= old(z - x) - c
        let old_zx = d.get_idx(zi, xi);
        if old_zx < INF {
            d.set_idx(zi, xi, old_zx.saturating_sub(c));
        }
    }
    // keep diagonal sane
    d.set_idx(xi, xi, 0);

    d.close();
}

// dst *= imm
pub fn assign_mul_imm(dbm: &mut Dbm, dst: Reg, imm: i64) {
    // Handle easy special cases first.
    if imm == 0 {
        // dst = 0
        assign_zero(dbm, dst);
        return;
    }

    if imm == 1 {
        // No-op on zones.
        return;
    }

    if imm < 0 {
        // Multiplication by negative constant flips the ordering of bounds.
        // We *could* do the full interval transform here, but for now stay
        // simple and sound: drop info about dst.
        forget(dbm, dst);
        return;
    }

    // imm > 0: monotone scaling, so we can scale bounds.
    let (ld_opt, ud_opt) = get_bounds(dbm, dst);

    // Kill old relational info about dst.
    dbm.forget_var(dst);

    if let Some(ld) = ld_opt {
        let new_lb = ld.saturating_mul(imm);
        assume_ge_const(dbm, dst, new_lb);
    }
    if let Some(ud) = ud_opt {
        let new_ub = ud.saturating_mul(imm);
        assume_le_const(dbm, dst, new_ub);
    }

    // If we had no bounds, dst just becomes unconstrained.
    dbm.close();
}

/// Handle: dst = dst / imm
pub fn assign_div_imm(dbm: &mut Dbm, reg: Reg, imm: i64) {
    if imm == 0 {
        // Technically this is a runtime crash. 
        // We leave the state as is (or top) and let the verifier fail logic handle it.
        return; 
    }

    // 1. Get current concrete bounds (Interval Analysis)
    let (lo, hi) = get_bounds(dbm, reg);

    // 2. Division breaks linear relationships. We must FORGET the register.
    forget(dbm, reg);

    // 3. Compute new bounds
    // BPF Div is unsigned. We assume values are treated as u64.
    // However, our DBM is i64. We treat negative numbers as "Large Positive" (Unknown).
    if let (Some(l), Some(h)) = (lo, hi) {
        if l >= 0 && h >= 0 {
            // Safe positive range
            let new_lo = l / imm;
            let new_hi = h / imm;
            
            // 4. Constrain with new bounds
            // dst >= new_lo  =>  0 - dst <= -new_lo
            // dst <= new_hi  =>  dst - 0 <= new_hi
            assume_ge_const(dbm, reg, new_lo);
            assume_le_const(dbm, reg, new_hi);
        }
    } else {
        // If we didn't know the bounds, or they were "negative",
        // we know nothing about the result except that it is smaller than u64::MAX.
        // Since we forgot the register in step 2, it is already "Unknown".
    }
}

/// Handle: dst = dst / src
pub fn assign_div_reg(dbm: &mut Dbm, dst: Reg, _src: Reg) {
    // We know very little about division by a variable.
    // dst / src results in a value smaller than dst (if src > 1).
    
    // 1. Conservative approach: Forget the destination
    forget(dbm, dst);

    // 2. We could add constraints if we knew bounds of src, 
    // but for now, "Unknown" is the safest sound approximation.
}

/// Simulates `reg &= imm`.
/// Since bitwise AND is non-linear, we forget precise relationships but 
/// deduce that the result is in the range [0, imm].
pub fn bit_and_const(dbm: &mut Dbm, reg: Reg, imm: i64) {
    // 1. Bitwise operations destroy linear relationships (e.g. x < y).
    // We must remove 'reg' from the matrix to avoid unsound conclusions.
    forget(dbm, reg);

    // 2. Apply new bounds derived from the mask.
    // The result of (x & imm) is treated as unsigned, so it is >= 0.
    assume_ge_const(dbm, reg, 0);

    // The result cannot be larger than the mask itself (if mask is positive).
    // e.g. (x & 0xFF) <= 255.
    if imm >= 0 {
        assume_le_const(dbm, reg, imm);
    }
}

pub fn assign_neg(dbm: &mut Dbm, reg: Reg) {
    // 1. Get current concrete bounds [lo, hi]
    let (lo, hi) = get_bounds(dbm, reg); // r10/zero
    
    // 2. Forget existing relationships (destroy x - y <= c)
    forget(dbm, reg);

    // 3. Apply new bounds: [-hi, -lo]
    // Note: checking for overflow (i64::MIN) is good practice but BPF implies wrapping.
    if let (Some(l), Some(h)) = (lo, hi) {
        // new_lower = -old_upper
        // new_upper = -old_lower
        let new_lo = h.wrapping_neg();
        let new_hi = l.wrapping_neg();
        
        assume_ge_const(dbm, reg, new_lo);
        assume_le_const(dbm, reg, new_hi);
    }
}

pub fn proven_u32_range(dbm: &Dbm, v: Reg, zero: Reg) -> bool {
    let vi = REG_ENV.index(v);
    let zi = REG_ENV.index(zero);
    let ub = dbm.raw(vi, zi);
    let lb = dbm.raw(zi, vi);
    // 0 <= v <= u32::MAX
    ub <= 0xffff_ffff && lb <= 0
}

// ═══════════════════════════════════════════════════════════
//  Packet region anchors
// ═══════════════════════════════════════════════════════════

/// Call once when the program type is known (e.g., XDP/SK_BUFF).
/// Establishes the invariant: data_meta <= data <= data_end.
pub fn init_packet_anchors(dbm: &mut Dbm) {
    let meta = Reg::AnchorDataMeta;
    let data = Reg::AnchorData;
    let end  = Reg::AnchorDataEnd;

    // data_meta <= data  (meta - data <= 0)
    dbm.add_constraint(meta, data, 0);
    // data <= data_end   (data - end <= 0)
    dbm.add_constraint(data, end, 0);
    // transitive: meta <= end
    dbm.close();
}

/// Call when a context load produces a packet pointer.
/// Links the register to the appropriate anchor with offset 0.
///   e.g., bind_to_anchor(dbm, R2, AnchorDataMeta) after loading data_meta
pub fn bind_to_anchor(dbm: &mut Dbm, reg: Reg, anchor: Reg) {
    debug_assert!(anchor.is_anchor(), "bind_to_anchor requires an anchor");
    // reg == anchor  (reg - anchor <= 0 AND anchor - reg <= 0)
    dbm.add_constraint(reg, anchor, 0);
    dbm.add_constraint(anchor, reg, 0);
    dbm.close();
}

/// Unified packet/meta region access check.
/// Returns (start_safe, end_safe).
///
/// Checks:  anchor_start + 0 <= base + off          (lower bound)
///          base + off + size <= anchor_end + 0      (upper bound)
///
/// In DBM terms:
///   start:  anchor_start - base <= off
///   end:    base - anchor_end   <= -(off + size)
pub fn check_region_access(
    dbm: &Dbm,
    base: Reg,
    off: i64,
    size: i64,
    anchor_start: Reg,
    anchor_end: Reg,
) -> (bool, bool) {
    let start_bound = dbm.get(anchor_start, base);  // anchor_start - base <= ?
    let start_safe = start_bound < INF && start_bound <= off;

    let end_bound = dbm.get(base, anchor_end);       // base - anchor_end <= ?
    let end_safe = end_bound < INF && (end_bound + off + size) <= 0;

    (start_safe, end_safe)
}

/// Convenience: check access into the metadata region [data_meta, data).
pub fn check_meta_access(dbm: &Dbm, base: Reg, off: i64, size: i64) -> (bool, bool) {
    check_region_access(dbm, base, off, size, Reg::AnchorDataMeta, Reg::AnchorData)
}

/// Convenience: check access into the packet region [data, data_end).
pub fn check_packet_access_dbm(dbm: &Dbm, base: Reg, off: i64, size: i64) -> (bool, bool) {
    check_region_access(dbm, base, off, size, Reg::AnchorData, Reg::AnchorDataEnd)
}

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

/// Merge anchor-to-anchor constraints from the callee into the caller's DBM.
/// Anchors represent packet boundaries (data, data_end, data_meta) which are
/// global — a bounds check in the callee is valid in the caller too.
/// For each pair, we keep the tighter (smaller) constraint.
pub fn preserve_anchor_constraints(caller_dbm: &mut Dbm, callee_dbm: &Dbm) {
    let anchors = [Reg::AnchorData, Reg::AnchorDataEnd, Reg::AnchorDataMeta];

    for &a in &anchors {
        for &b in &anchors {
            if a == b {
                continue;
            }
            let callee_bound = callee_dbm.get(a, b);
            let caller_bound = caller_dbm.get(a, b);

            // A smaller value means a tighter constraint
            // (a - b <= X, smaller X = tighter)
            if callee_bound < caller_bound {
                caller_dbm.add_constraint(a, b, callee_bound);
            }
        }
    }
    caller_dbm.close();
}
