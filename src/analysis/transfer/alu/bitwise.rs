// src/analysis/transfer/alu/bitwise.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{Operand, Width};
use crate::domains::tnum::Tnum;

use super::helpers::sync_tnum_to_dbm;

pub(crate) fn handle_mov(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(c) => {
            let v = if width == Width::W32 {
                (*c as u32) as u64
            } else {
                *c as u64
            };
            state.set_tnum(dst, Tnum::constant(v));
        }
        Operand::Reg(r) => {
            let t = if width == Width::W32 {
                state.get_tnum(*r).trunc32()
            } else {
                state.get_tnum(*r)
            };
            state.set_tnum(dst, t);
        }
    }

    match src {
        Operand::Reg(r) => {
            if width == Width::W32 {
                // Snapshot u32-range proof + u32 shadow bounds on `*r`
                // before forgetting `dst`, because (a) for self-mov
                // (dst == *r) forget() wipes the very bounds we need;
                // (b) when full bounds are unbounded but the W32 shadow
                // is tight (e.g. after a `if w1 > 10` jmp32 that only
                // narrowed the shadow), zero-extension `w_d = w_s`
                // makes upper 32 bits zero, so dst's full bound = the
                // source's u32 shadow. Without this, `if w1 > 10; w1
                // = w1; r1 *= 24; ptr += r1` rejects: the self-mov
                // would widen to [0, u32::MAX], blowing the Mul bound.
                let preserved = state.domain.proven_u32_range(*r, Reg::Zero);
                let (u32_min, u32_max) = state.domain.get_u32_bounds(*r);
                state.domain.forget(dst);
                if preserved {
                    state.domain.assign_reg(dst, *r);
                } else {
                    state.domain.assume_ge_imm(dst, u32_min as i64);
                    state.domain.assume_le_imm(dst, u32_max as i64);
                }
            } else {
                if dst == *r {
                    return;
                }
                // Copy register state including pointer offset info
                state.domain.assign_reg(dst, *r);
            }
        }
        Operand::Imm(c) => {
            let c = if width == Width::W32 {
                (*c as u32) as i64
            } else {
                *c
            };
            state.domain.forget(dst);
            state.domain.assume_le_imm(dst, c);
            state.domain.assume_ge_imm(dst, c);
        }
    }
}

pub(crate) fn handle_and(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    let (min_op, max_op) = state.domain.get_interval(dst);
    let input_nonnegative = min_op >= 0;

    let (old_s32_min, old_s32_max) = state.domain.get_s32_bounds(dst);

    state.domain.forget(dst);

    if let Operand::Imm(mask) = src {
        let mask = if width == Width::W32 {
            (*mask as u32) as i64
        } else {
            *mask
        };
        if mask >= 0 {
            state.domain.apply_and_imm(dst, mask);
        } else if input_nonnegative {
            state.domain.assume_ge_imm(dst, 0);
            if max_op != i64::MAX {
                state.domain.assume_le_imm(dst, max_op);
            }
        }
    } else if let Operand::Reg(_) = src {
        state.domain.assume_ge_imm(dst, 0);
    }

    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(mask) => {
            let mask = if width == Width::W32 {
                (*mask as u32) as u64
            } else {
                *mask as u64
            };
            t.and_imm(mask)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.and(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);

    if let Some(c) = new_t.const_value() {
        state.domain.assume_eq_imm(dst, c as i64);
    }

    if width == Width::W32 {
        if let Operand::Imm(mask) = src {
            let mask32 = *mask as i32;
            // If the value was exactly restricted to [-1, 0] (e.g. from arsh 31)
            // Then val & mask is strictly bounded by min(mask32, 0) and max(mask32, 0).
            if old_s32_min >= -1 && old_s32_max <= 0 {
                let new_min = mask32.min(0);
                let new_max = mask32.max(0);
                state.domain.set_s32_bounds(dst, new_min, new_max);
            }
        }
    }
}

pub(crate) fn handle_or(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    state.domain.forget(dst);

    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(c) => {
            let c = if width == Width::W32 {
                (*c as u32) as u64
            } else {
                *c as u64
            };
            t.or_imm(c)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.or(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);

    sync_tnum_to_dbm(state, dst);
}

pub(crate) fn handle_xor(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    state.domain.forget(dst);

    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(c) => {
            let c = if width == Width::W32 {
                (*c as u32) as u64
            } else {
                *c as u64
            };
            t.xor_imm(c)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.xor(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);

    sync_tnum_to_dbm(state, dst);
}
