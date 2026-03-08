// src/analysis/transfer/branch/constraints.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Width};
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;
use either::Either::{self};

use super::outcome::{fits_in_i32, fits_in_u32, get_combined_signed_bounds};

/// Propagate a constraint to all registers with the same scalar_id as source_reg.
/// This is used in the interval domain to track bounds across register copies.
fn interval_propagate_scalars<F>(domain: &mut NumericDomain, source_reg: Reg, apply: F)
where
    F: Fn(&mut NumericDomain, Reg),
{
    if let NumericDomain::Interval(ivl) = domain {
        let source_id = ivl.get(source_reg).bounds.scalar_id;
        if let Some(id) = source_id {
            // Collect registers with matching scalar_id
            let matching_regs: Vec<Reg> = Reg::ALL
                .iter()
                .copied()
                .filter(|&r| {
                    r != source_reg
                        && r != Reg::Zero
                        && !r.is_anchor()
                        && ivl.get(r).bounds.scalar_id == Some(id)
                })
                .collect();
            // Apply constraint to each matching register
            for r in matching_regs {
                apply(domain, r);
            }
        }
    }
}

pub fn apply_jmp_constraints(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    op: CmpOp,
    width: Width,
    right: Either<Reg, i64>,
) {
    if op == CmpOp::Test {
        apply_test_constraints(then_s, else_s, left, width, right);
        return;
    }

    let (resolved, right_bounds) = resolve_right_operand(&then_s.domain, right, width, op);
    if can_apply_dbm_constraint(then_s, left, op, width, right_bounds, resolved) {
        apply_cmp_to_domain(&mut then_s.domain, &mut else_s.domain, left, op, resolved);
    } else if width == Width::W64 && matches!(op, CmpOp::UGt | CmpOp::UGe | CmpOp::ULt | CmpOp::ULe)
    {
        apply_unsigned_const_fallback(then_s, else_s, left, op, resolved);
    } else if width == Width::W32 && matches!(op, CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe)
    {
        apply_w32_signed_fallback(then_s, else_s, left, op, resolved);
    }

    let imm_val = match resolved {
        Either::Right(v) => Some(v),
        Either::Left(_) => None,
    };
    apply_eq_refinements(then_s, else_s, left, op, imm_val);
}

fn can_apply_dbm_constraint(
    state: &State,
    left: Reg,
    op: CmpOp,
    width: Width,
    right_bounds: (i64, i64),
    right: Either<Reg, i64>,
) -> bool {
    // For interval domain, skip scalar constraint propagation for packet pointer
    // comparisons. The relationship between pkt_data/pkt_end is tracked via
    // packet_size_lower_bound, not scalar bounds. Applying scalar constraints
    // to packet pointers with unknown absolute values incorrectly marks
    // branches as infeasible.
    if matches!(state.domain, NumericDomain::Interval(_)) {
        if !interval_can_apply_constraint(state, left, right) {
            return false;
        }
    }

    let dominated_by_signed = matches!(op, CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe);
    let dominated_by_unsigned = matches!(op, CmpOp::ULt | CmpOp::ULe | CmpOp::UGt | CmpOp::UGe);

    if width == Width::W32 {
        let left_bounds = get_combined_signed_bounds(state, left);
        if dominated_by_signed {
            return fits_in_i32(left_bounds) && fits_in_i32(right_bounds);
        } else if dominated_by_unsigned {
            return fits_in_u32(left_bounds) && fits_in_u32(right_bounds);
        }
    }

    if dominated_by_unsigned {
        let left_bounds = get_combined_signed_bounds(state, left);
        let left_nonneg = left_bounds.0 >= 0;
        let left_unbounded = {
            let (lo, _) = state.domain.get_interval(left);
            let tnum = state.get_tnum(left);
            lo == i64::MIN && tnum.max_value() > i64::MAX as u64
        };
        let right_nonneg = right_bounds.0 >= 0;
        let right_is_pointer = match right {
            Either::Left(reg) => state.types.get(reg).is_pointer(),
            _ => false,
        };
        return (left_nonneg || left_unbounded) && (right_nonneg || right_is_pointer);
    }

    true
}

fn apply_cmp_to_domain(
    then_domain: &mut NumericDomain,
    else_domain: &mut NumericDomain,
    left: Reg,
    op: CmpOp,
    right: Either<Reg, i64>,
) {
    match (op, right) {
        (CmpOp::Eq, Either::Right(imm)) => {
            then_domain.assume_eq_imm(left, imm);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_eq_imm(r, imm));
        }
        (CmpOp::Eq, Either::Left(reg)) => {
            then_domain.assign_reg(left, reg);
        }
        (CmpOp::Ne, Either::Right(imm)) => {
            else_domain.assume_eq_imm(left, imm);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_eq_imm(r, imm));
        }
        (CmpOp::Ne, Either::Left(reg)) => {
            else_domain.assign_reg(left, reg);
        }
        (CmpOp::UGe, Either::Right(imm)) => {
            then_domain.assume_ge_imm(left, imm);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, imm));
            else_domain.assume_lt_imm(left, imm);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_lt_imm(r, imm));
            if imm > 0 {
                else_domain.assume_ge_imm(left, 0);
                interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, 0));
            }
        }
        (CmpOp::SGe, Either::Right(imm)) => {
            then_domain.assume_ge_imm(left, imm);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, imm));
            else_domain.assume_lt_imm(left, imm);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_lt_imm(r, imm));
        }
        (CmpOp::UGe, Either::Left(reg)) => {
            then_domain.assume_ge(left, reg);
            else_domain.assume_le_offset(left, reg, -1);
            else_domain.assume_ge_imm(left, 0);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, 0));
        }
        (CmpOp::SGe, Either::Left(reg)) => {
            then_domain.assume_ge(left, reg);
            else_domain.assume_le_offset(left, reg, -1);
        }
        (CmpOp::UGt, Either::Right(imm)) => {
            then_domain.assume_ge_imm(left, imm + 1);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, imm + 1));
            else_domain.assume_le_imm(left, imm);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_le_imm(r, imm));
            else_domain.assume_ge_imm(left, 0);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, 0));
        }
        (CmpOp::SGt, Either::Right(imm)) => {
            then_domain.assume_ge_imm(left, imm + 1);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, imm + 1));
            else_domain.assume_le_imm(left, imm);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_le_imm(r, imm));
        }
        (CmpOp::UGt, Either::Left(reg)) => {
            then_domain.assume_gt(left, reg);
            else_domain.assume_le(left, reg);
            else_domain.assume_ge_imm(left, 0);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, 0));
        }
        (CmpOp::SGt, Either::Left(reg)) => {
            then_domain.assume_gt(left, reg);
            else_domain.assume_le(left, reg);
        }
        (CmpOp::ULe, Either::Right(imm)) => {
            then_domain.assume_le_imm(left, imm);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_le_imm(r, imm));
            then_domain.assume_ge_imm(left, 0);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, 0));
            else_domain.assume_ge_imm(left, imm + 1);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, imm + 1));
        }
        (CmpOp::SLe, Either::Right(imm)) => {
            then_domain.assume_le_imm(left, imm);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_le_imm(r, imm));
            else_domain.assume_ge_imm(left, imm + 1);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, imm + 1));
        }
        (CmpOp::ULe, Either::Left(reg)) => {
            then_domain.assume_le(left, reg);
            then_domain.assume_ge_imm(left, 0);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, 0));
            else_domain.assume_gt(left, reg);
        }
        (CmpOp::SLe, Either::Left(reg)) => {
            then_domain.assume_le(left, reg);
            else_domain.assume_gt(left, reg);
        }
        (CmpOp::ULt, Either::Right(imm)) => {
            then_domain.assume_lt_imm(left, imm);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_lt_imm(r, imm));
            if imm > 0 {
                then_domain.assume_ge_imm(left, 0);
                interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, 0));
            }
            else_domain.assume_ge_imm(left, imm);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, imm));
        }
        (CmpOp::SLt, Either::Right(imm)) => {
            then_domain.assume_lt_imm(left, imm);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_lt_imm(r, imm));
            else_domain.assume_ge_imm(left, imm);
            interval_propagate_scalars(else_domain, left, |d, r| d.assume_ge_imm(r, imm));
        }
        (CmpOp::ULt, Either::Left(reg)) => {
            then_domain.assume_le_offset(left, reg, -1);
            then_domain.assume_ge_imm(left, 0);
            interval_propagate_scalars(then_domain, left, |d, r| d.assume_ge_imm(r, 0));
            else_domain.assume_ge(left, reg);
        }
        (CmpOp::SLt, Either::Left(reg)) => {
            then_domain.assume_le_offset(left, reg, -1);
            else_domain.assume_ge(left, reg);
        }
        (CmpOp::Test, _) => {}
    }
}

fn apply_eq_refinements(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    op: CmpOp,
    imm: Option<i64>,
) {
    match (op, imm) {
        (CmpOp::Eq, Some(v)) => {
            then_s.set_tnum(left, Tnum::constant(v as u64));
        }
        (CmpOp::Ne, Some(v)) => {
            else_s.set_tnum(left, Tnum::constant(v as u64));
        }
        _ => {}
    }
}

fn apply_test_constraints(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    width: Width,
    right: Either<Reg, i64>,
) {
    let mask = match right {
        Either::Right(imm) => {
            if width == Width::W32 {
                (imm as u32) as u64
            } else {
                imm as u64
            }
        }
        Either::Left(reg) => {
            if let Some(val) = then_s.domain.get_fixed_value(reg) {
                if width == Width::W32 {
                    (val as u32) as u64
                } else {
                    val as u64
                }
            } else {
                return;
            }
        }
    };

    let else_tnum = else_s.get_tnum(left);
    let refined = Tnum {
        value: else_tnum.value & !mask,
        mask: else_tnum.mask & !mask,
    };
    else_s.set_tnum(left, refined);

    if mask.is_power_of_two() {
        let bit_pos = mask.trailing_zeros();
        let then_tnum = then_s.get_tnum(left);
        let refined = Tnum {
            value: then_tnum.value | mask,
            mask: then_tnum.mask & !mask,
        };
        then_s.set_tnum(left, refined);

        if width == Width::W32 && bit_pos == 31 {
            if then_s.domain.fits_in_u32_range(left) {
                then_s.domain.assume_ge_imm(left, 0x80000000);
                else_s.domain.assume_le_imm(left, 0x7FFFFFFF);
            }
        } else if width == Width::W64 && bit_pos == 63 {
            then_s.domain.assume_lt_imm(left, 0);
            else_s.domain.assume_ge_imm(left, 0);
        }
    }
}

fn resolve_right_operand(
    domain: &NumericDomain,
    right: Either<Reg, i64>,
    width: Width,
    op: CmpOp,
) -> (Either<Reg, i64>, (i64, i64)) {
    let is_signed = matches!(op, CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe);

    let truncate = |val: i64| -> i64 {
        if width == Width::W32 {
            if is_signed {
                (val as u32) as i32 as i64
            } else {
                (val as u32) as i64
            }
        } else {
            val
        }
    };

    match right {
        Either::Right(imm) => {
            let eff = truncate(imm);
            (Either::Right(eff), (eff, eff))
        }
        Either::Left(reg) => {
            if let Some(val) = domain.get_fixed_value(reg) {
                let eff = truncate(val);
                (Either::Right(eff), (eff, eff))
            } else {
                let bounds = domain.get_interval(reg);
                (Either::Left(reg), bounds)
            }
        }
    }
}

fn apply_unsigned_const_fallback(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    op: CmpOp,
    right: Either<Reg, i64>,
) {
    let left_const = then_s.domain.get_fixed_value(left).or_else(|| {
        let t = then_s.get_tnum(left);
        if t.is_const() {
            Some(t.value as i64)
        } else {
            None
        }
    });

    match (left_const, right) {
        (Some(k), Either::Left(reg)) => {
            let flipped = flip_unsigned_cmp(op);
            apply_unsigned_range_constraint_domain(
                &mut then_s.domain,
                &mut else_s.domain,
                reg,
                flipped,
                k as u64,
            );
        }
        (_, Either::Right(imm)) => {
            apply_unsigned_range_constraint_domain(
                &mut then_s.domain,
                &mut else_s.domain,
                left,
                op,
                imm as u64,
            );
        }
        _ => {}
    }
}

fn flip_unsigned_cmp(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::UGt => CmpOp::ULt,
        CmpOp::UGe => CmpOp::ULe,
        CmpOp::ULt => CmpOp::UGt,
        CmpOp::ULe => CmpOp::UGe,
        other => other,
    }
}

fn apply_unsigned_range_constraint_domain(
    then_domain: &mut NumericDomain,
    else_domain: &mut NumericDomain,
    reg: Reg,
    op: CmpOp,
    k: u64,
) {
    match op {
        CmpOp::UGt => {
            if k < u64::MAX {
                apply_signed_from_unsigned_range_domain(then_domain, reg, k + 1, u64::MAX);
            }
            apply_signed_from_unsigned_range_domain(else_domain, reg, 0, k);
        }
        CmpOp::UGe => {
            apply_signed_from_unsigned_range_domain(then_domain, reg, k, u64::MAX);
            if k > 0 {
                apply_signed_from_unsigned_range_domain(else_domain, reg, 0, k - 1);
            }
        }
        CmpOp::ULt => {
            if k > 0 {
                apply_signed_from_unsigned_range_domain(then_domain, reg, 0, k - 1);
            }
            apply_signed_from_unsigned_range_domain(else_domain, reg, k, u64::MAX);
        }
        CmpOp::ULe => {
            apply_signed_from_unsigned_range_domain(then_domain, reg, 0, k);
            if k < u64::MAX {
                apply_signed_from_unsigned_range_domain(else_domain, reg, k + 1, u64::MAX);
            }
        }
        _ => {}
    }
}

fn apply_signed_from_unsigned_range_domain(
    domain: &mut NumericDomain,
    reg: Reg,
    lo_u: u64,
    hi_u: u64,
) {
    if lo_u > hi_u {
        return;
    }

    let lo_s = lo_u as i64;
    let hi_s = hi_u as i64;

    if hi_u <= i64::MAX as u64 {
        domain.assume_ge_imm(reg, lo_s);
        domain.assume_le_imm(reg, hi_s);
    } else if lo_u >= 0x8000000000000000 {
        domain.assume_ge_imm(reg, lo_s);
        domain.assume_le_imm(reg, hi_s);
    }
}

fn apply_w32_signed_fallback(
    then_s: &mut State,
    else_s: &mut State,
    left: Reg,
    op: CmpOp,
    right: Either<Reg, i64>,
) {
    let right_imm = match right {
        Either::Right(imm) => imm,
        Either::Left(reg) => {
            if let Some(val) = then_s.domain.get_fixed_value(reg) {
                val
            } else {
                return;
            }
        }
    };

    let rv = right_imm as i32;

    let (mut t_s32_min, mut t_s32_max) = then_s.domain.get_s32_bounds(left);
    let (mut e_s32_min, mut e_s32_max) = else_s.domain.get_s32_bounds(left);

    match op {
        CmpOp::SGt => {
            t_s32_min = t_s32_min.max(rv.saturating_add(1));
            e_s32_max = e_s32_max.min(rv);
        }
        CmpOp::SGe => {
            t_s32_min = t_s32_min.max(rv);
            e_s32_max = e_s32_max.min(rv.saturating_sub(1));
        }
        CmpOp::SLt => {
            t_s32_max = t_s32_max.min(rv.saturating_sub(1));
            e_s32_min = e_s32_min.max(rv);
        }
        CmpOp::SLe => {
            t_s32_max = t_s32_max.min(rv);
            e_s32_min = e_s32_min.max(rv.saturating_add(1));
        }
        CmpOp::Eq => {
            t_s32_min = t_s32_min.max(rv);
            t_s32_max = t_s32_max.min(rv);
        }
        _ => return,
    }

    then_s.domain.set_s32_bounds(left, t_s32_min, t_s32_max);
    else_s.domain.set_s32_bounds(left, e_s32_min, e_s32_max);
}

fn interval_can_apply_constraint(state: &State, left: Reg, right: Either<Reg, i64>) -> bool {
    let left_is_packet = state.types.get(left).is_packet_ptr();
    let right_is_packet = match right {
        Either::Left(reg) => state.types.get(reg).is_packet_ptr(),
        Either::Right(_) => false,
    };
    if left_is_packet && right_is_packet {
        return false;
    }
    true
}
