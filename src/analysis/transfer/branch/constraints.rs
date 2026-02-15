// src/analysis/transfer/branch/constraints.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Width};
use crate::zone::dbm::Dbm;
use crate::zone::domain::{
    assign_reg, assume_eq_imm, assume_ge, assume_ge_imm, assume_gt, assume_le, assume_le_imm,
    assume_le_offset, assume_lt_imm, get_fixed_value,
};
use crate::zone::tnum::Tnum;
use either::Either::{self};

use super::outcome::{fits_in_i32, fits_in_u32, fits_in_u32_range, get_combined_signed_bounds};

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

    let (resolved, right_bounds) = resolve_right_operand(&then_s.dbm, right, width, op);
    if can_apply_dbm_constraint(then_s, left, op, width, right_bounds, resolved) {
        apply_cmp_to_dbm(&mut then_s.dbm, &mut else_s.dbm, left, op, resolved);
    } else if width == Width::W64 && matches!(op, CmpOp::UGt | CmpOp::UGe | CmpOp::ULt | CmpOp::ULe)
    {
        apply_unsigned_const_fallback(then_s, else_s, left, op, resolved);
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
            let (lo, _) = crate::zone::domain::get_interval(&state.dbm, left);
            let tnum = state.get_tnum(left);
            lo.is_none() && tnum.max_value() > i64::MAX as u64
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

fn apply_cmp_to_dbm(
    then_dbm: &mut Dbm,
    else_dbm: &mut Dbm,
    left: Reg,
    op: CmpOp,
    right: Either<Reg, i64>,
) {
    match (op, right) {
        (CmpOp::Eq, Either::Right(imm)) => {
            assume_eq_imm(then_dbm, left, imm);
        }
        (CmpOp::Eq, Either::Left(reg)) => {
            assign_reg(then_dbm, left, reg);
        }
        (CmpOp::Ne, Either::Right(imm)) => {
            assume_eq_imm(else_dbm, left, imm);
        }
        (CmpOp::Ne, Either::Left(reg)) => {
            assign_reg(else_dbm, left, reg);
        }
        (CmpOp::UGe, Either::Right(imm)) => {
            assume_ge_imm(then_dbm, left, imm);
            assume_lt_imm(else_dbm, left, imm);
            if imm > 0 {
                assume_ge_imm(else_dbm, left, 0);
            }
        }
        (CmpOp::SGe, Either::Right(imm)) => {
            assume_ge_imm(then_dbm, left, imm);
            assume_lt_imm(else_dbm, left, imm);
        }
        (CmpOp::UGe, Either::Left(reg)) => {
            assume_ge(then_dbm, left, reg);
            assume_le_offset(else_dbm, left, reg, -1);
            assume_ge_imm(else_dbm, left, 0);
        }
        (CmpOp::SGe, Either::Left(reg)) => {
            assume_ge(then_dbm, left, reg);
            assume_le_offset(else_dbm, left, reg, -1);
        }
        (CmpOp::UGt, Either::Right(imm)) => {
            assume_ge_imm(then_dbm, left, imm + 1);
            assume_le_imm(else_dbm, left, imm);
            assume_ge_imm(else_dbm, left, 0);
        }
        (CmpOp::SGt, Either::Right(imm)) => {
            assume_ge_imm(then_dbm, left, imm + 1);
            assume_le_imm(else_dbm, left, imm);
        }
        (CmpOp::UGt, Either::Left(reg)) => {
            assume_gt(then_dbm, left, reg);
            assume_le(else_dbm, left, reg);
            assume_ge_imm(else_dbm, left, 0);
        }
        (CmpOp::SGt, Either::Left(reg)) => {
            assume_gt(then_dbm, left, reg);
            assume_le(else_dbm, left, reg);
        }
        (CmpOp::ULe, Either::Right(imm)) => {
            assume_le_imm(then_dbm, left, imm);
            assume_ge_imm(then_dbm, left, 0);
            assume_ge_imm(else_dbm, left, imm + 1);
        }
        (CmpOp::SLe, Either::Right(imm)) => {
            assume_le_imm(then_dbm, left, imm);
            assume_ge_imm(else_dbm, left, imm + 1);
        }
        (CmpOp::ULe, Either::Left(reg)) => {
            assume_le(then_dbm, left, reg);
            assume_ge_imm(then_dbm, left, 0);
            assume_gt(else_dbm, left, reg);
        }
        (CmpOp::SLe, Either::Left(reg)) => {
            assume_le(then_dbm, left, reg);
            assume_gt(else_dbm, left, reg);
        }
        (CmpOp::ULt, Either::Right(imm)) => {
            assume_lt_imm(then_dbm, left, imm);
            if imm > 0 {
                assume_ge_imm(then_dbm, left, 0);
            }
            assume_ge_imm(else_dbm, left, imm);
        }
        (CmpOp::SLt, Either::Right(imm)) => {
            assume_lt_imm(then_dbm, left, imm);
            assume_ge_imm(else_dbm, left, imm);
        }
        (CmpOp::ULt, Either::Left(reg)) => {
            assume_le_offset(then_dbm, left, reg, -1);
            assume_ge_imm(then_dbm, left, 0);
            assume_ge(else_dbm, left, reg);
        }
        (CmpOp::SLt, Either::Left(reg)) => {
            assume_le_offset(then_dbm, left, reg, -1);
            assume_ge(else_dbm, left, reg);
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
            if let Some(val) = get_fixed_value(&then_s.dbm, reg) {
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
            if fits_in_u32_range(&then_s.dbm, left) {
                assume_ge_imm(&mut then_s.dbm, left, 0x80000000);
                assume_le_imm(&mut else_s.dbm, left, 0x7FFFFFFF);
            }
        } else if width == Width::W64 && bit_pos == 63 {
            assume_lt_imm(&mut then_s.dbm, left, 0);
            assume_ge_imm(&mut else_s.dbm, left, 0);
        }
    }
}

fn resolve_right_operand(
    dbm: &Dbm,
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
            if let Some(val) = get_fixed_value(dbm, reg) {
                let eff = truncate(val);
                (Either::Right(eff), (eff, eff))
            } else {
                let bounds = crate::zone::domain::get_interval(dbm, reg);
                let bounds = (bounds.0.unwrap_or(i64::MIN), bounds.1.unwrap_or(i64::MAX));
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
    let left_const = get_fixed_value(&then_s.dbm, left).or_else(|| {
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
            apply_unsigned_range_constraint(
                &mut then_s.dbm,
                &mut else_s.dbm,
                reg,
                flipped,
                k as u64,
            );
        }
        (_, Either::Right(imm)) => {
            apply_unsigned_range_constraint(&mut then_s.dbm, &mut else_s.dbm, left, op, imm as u64);
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

fn apply_unsigned_range_constraint(
    then_dbm: &mut Dbm,
    else_dbm: &mut Dbm,
    reg: Reg,
    op: CmpOp,
    k: u64,
) {
    match op {
        CmpOp::UGt => {
            if k < u64::MAX {
                apply_signed_from_unsigned_range(then_dbm, reg, k + 1, u64::MAX);
            }
            apply_signed_from_unsigned_range(else_dbm, reg, 0, k);
        }
        CmpOp::UGe => {
            apply_signed_from_unsigned_range(then_dbm, reg, k, u64::MAX);
            if k > 0 {
                apply_signed_from_unsigned_range(else_dbm, reg, 0, k - 1);
            }
        }
        CmpOp::ULt => {
            if k > 0 {
                apply_signed_from_unsigned_range(then_dbm, reg, 0, k - 1);
            }
            apply_signed_from_unsigned_range(else_dbm, reg, k, u64::MAX);
        }
        CmpOp::ULe => {
            apply_signed_from_unsigned_range(then_dbm, reg, 0, k);
            if k < u64::MAX {
                apply_signed_from_unsigned_range(else_dbm, reg, k + 1, u64::MAX);
            }
        }
        _ => {}
    }
}

fn apply_signed_from_unsigned_range(dbm: &mut Dbm, reg: Reg, lo_u: u64, hi_u: u64) {
    if lo_u > hi_u {
        return;
    }

    let lo_s = lo_u as i64;
    let hi_s = hi_u as i64;

    if hi_u <= i64::MAX as u64 {
        assume_ge_imm(dbm, reg, lo_s);
        assume_le_imm(dbm, reg, hi_s);
    } else if lo_u >= 0x8000000000000000 {
        assume_ge_imm(dbm, reg, lo_s);
        assume_le_imm(dbm, reg, hi_s);
    }
}
