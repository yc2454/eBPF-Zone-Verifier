// src/analysis/transfer/alu/bitwise.rs

use crate::analysis::machine::state::State;
use crate::analysis::machine::reg::Reg;
use crate::zone::domain::{assign_and_mask, assign_eq, assign_zero, assume_eq_const, assume_ge_const, assume_le_const, forget, get_bounds};
use crate::ast::{Operand, Width};
use crate::zone::tnum::{Tnum};

use super::helpers::{sync_tnum_to_dbm};

pub(crate) fn handle_mov(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
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
                forget(&mut state.dbm, dst);
                if crate::zone::domain::proven_u32_range(&mut state.dbm, *r, Reg::Zero) {
                    assign_eq(&mut state.dbm, dst, *r);
                } else {
                    assume_ge_const(&mut state.dbm, dst, 0);
                    assume_le_const(&mut state.dbm, dst, 0xFFFFFFFF);
                }
            } else {
                if dst == *r {
                    return;
                }
                if *r == Reg::R10 {
                    assign_zero(&mut state.dbm, dst);
                } else {
                    assign_eq(&mut state.dbm, dst, *r);
                }
            }
        }
        Operand::Imm(c) => {
            let c = if width == Width::W32 { (*c as u32) as i64 } else { *c };
            forget(&mut state.dbm, dst);
            assume_le_const(&mut state.dbm, dst, c);
            assume_ge_const(&mut state.dbm, dst, c);
        }
    }
}

pub(crate) fn handle_and(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    let (min_op, max_op) = get_bounds(&state.dbm, dst);
    let input_nonnegative = min_op.map_or(false, |m| m >= 0);

    forget(&mut state.dbm, dst);

    if let Operand::Imm(mask) = src {
        let mask = if width == Width::W32 { (*mask as u32) as i64 } else { *mask };
        if mask >= 0 {
            assign_and_mask(&mut state.dbm, dst, mask);
        } else if input_nonnegative {
            assume_ge_const(&mut state.dbm, dst, 0);
            if let Some(max) = max_op {
                assume_le_const(&mut state.dbm, dst, max);
            }
        }
    } else if let Operand::Reg(_) = src {
        assume_ge_const(&mut state.dbm, dst, 0);
    }
    
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(mask) => {
            let mask = if width == Width::W32 { (*mask as u32) as u64 } else { *mask as u64 };
            t.and_imm(mask)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.and(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);
    
    if let Some(c) = new_t.const_value() {
        assume_eq_const(&mut state.dbm, dst, c as i64);
    }
}

pub(crate) fn handle_or(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    forget(&mut state.dbm, dst);
    
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(c) => {
            let c = if width == Width::W32 { (*c as u32) as u64 } else { *c as u64 };
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

pub(crate) fn handle_xor(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    forget(&mut state.dbm, dst);
    
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(c) => {
            let c = if width == Width::W32 { (*c as u32) as u64 } else { *c as u64 };
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
