// src/analysis/transfer/alu/arithmetic.rs

use crate::analysis::machine::env::{VerifierEnv};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::ast::{Operand, Width};
use crate::analysis::machine::reg::Reg;
use crate::zone::domain::{
    apply_add_imm, apply_add_reg, apply_div_imm, apply_div_reg, apply_mul_imm, 
    apply_neg, apply_sub_reg, forget, get_interval, get_fixed_value, 
    assign_reg_offset, assign_interval, apply_and_imm, assume_ge_imm, assume_le_imm
};
use crate::zone::tnum::{Tnum};

use super::helpers::{apply_w32_truncation, check_ptr_bounds, sync_tnum_to_dbm};

pub(crate) fn handle_add(
    _env: &mut VerifierEnv,
    state: &mut State,
    in_types: &TypeState,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            apply_add_imm(&mut state.dbm, dst, *c);
        }
        Operand::Reg(r) => {
            let src_is_ptr = in_types.get(*r).is_pointer();
            let dst_is_ptr = in_types.get(dst).is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr += scalar: preserve relational info if possible
                let (lo, hi) = get_interval(&state.dbm, *r);
                if lo == hi && lo.is_some() {
                    // Known constant: shift all relations exactly
                    apply_add_imm(&mut state.dbm, dst, lo.unwrap());
                } else {
                    // Non-constant: fall back to interval
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(dst)) {
                        forget(&mut state.dbm, dst);
                        assign_interval(&mut state.dbm, dst, off, off);
                    }
                    apply_add_reg(&mut state.dbm, dst, *r);
                }
            } else if src_is_ptr && !dst_is_ptr {
                // scalar += ptr
                let (lo, hi) = get_interval(&state.dbm, dst);
                if lo == hi && lo.is_some() {
                    assign_reg_offset(&mut state.dbm, dst, *r, lo.unwrap());
                } else {
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(*r)) {
                        forget(&mut state.dbm, *r);
                        assign_interval(&mut state.dbm, *r, off, off);
                    }
                    forget(&mut state.dbm, dst);
                    if let Some(hi) = hi {
                        state.dbm.add_constraint(dst, *r, hi);
                    }
                    if let Some(lo) = lo {
                        if lo > i64::MIN {
                            state.dbm.add_constraint(*r, dst, -lo);
                        }
                    }
                    state.dbm.close();
                }
            } else {
                // scalar += scalar, ptr += ptr, etc.
                apply_add_reg(&mut state.dbm, dst, *r);
            }
        }
    }
    
    let dst_tnum = state.get_tnum(dst);
    let new_tnum = match src {
        Operand::Imm(c) => dst_tnum.add_imm(*c),
        Operand::Reg(r) => dst_tnum.add(state.get_tnum(*r)),
    };
    let new_tnum = if width == Width::W32 { new_tnum.trunc32() } else { new_tnum };
    state.set_tnum(dst, new_tnum);
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    check_ptr_bounds(state, dst);
    sync_tnum_to_dbm(state, dst);
}

pub(crate) fn handle_sub(
    _env: &mut VerifierEnv,
    state: &mut State,
    in_types: &TypeState,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            apply_add_imm(&mut state.dbm, dst, -c);
        }
        Operand::Reg(r) => {
            let dst_is_ptr = in_types.get(dst).is_pointer();
            let src_is_ptr = in_types.get(*r).is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr -= scalar: try to preserve relational info
                let const_value = get_fixed_value(&state.dbm, *r);
                
                if const_value.is_some() {
                    // Scalar is a known constant: exact relational shift
                    apply_add_imm(&mut state.dbm, dst, -const_value.unwrap());
                } else {
                    // Bounded but not constant: fall back to interval
                    apply_sub_reg(&mut state.dbm, dst, *r);
                }
            } else {
                // scalar -= scalar, scalar -= ptr, ptr -= ptr
                apply_sub_reg(&mut state.dbm, dst, *r);
            }
        }
    }

    let dst_tnum = state.get_tnum(dst);
    let new_tnum = match src {
        Operand::Imm(c) => dst_tnum.sub_imm(*c),
        Operand::Reg(r) => dst_tnum.sub(state.get_tnum(*r)),
    };
    let new_tnum = if width == Width::W32 { new_tnum.trunc32() } else { new_tnum };
    state.set_tnum(dst, new_tnum);
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    let dst_is_ptr = in_types.get(dst).is_pointer();
    let src_is_ptr = match src {
        Operand::Imm(_) => false,
        Operand::Reg(r) => in_types.get(*r).is_pointer()
    };
    if !(dst_is_ptr && src_is_ptr) {
        check_ptr_bounds(state, dst);
    }

    sync_tnum_to_dbm(state, dst);
}

pub(crate) fn handle_neg(
    state: &mut State,
    width: Width,
    dst: Reg,
) {
    apply_neg(&mut state.dbm, dst);

    if width == Width::W32 {
        apply_and_imm(&mut state.dbm, dst, 0xFFFFFFFF);
    }

    let t = state.get_tnum(dst);
    let new_t = if width == Width::W32 {
        t.trunc32()
    } else {
        Tnum::unknown()
    };
    state.set_tnum(dst, new_t);
}

pub(crate) fn handle_mul(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            apply_mul_imm(&mut state.dbm, dst, *c);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    state.set_tnum(dst, Tnum::unknown());
}

pub(crate) fn handle_mod(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            if *c > 0 {
                forget(&mut state.dbm, dst);
                assume_ge_imm(&mut state.dbm, dst, 0);
                assume_le_imm(&mut state.dbm, dst, c - 1);
            } else {
                forget(&mut state.dbm, dst);
            }
        }
        Operand::Reg(r) => {
            let (r_lo, r_hi) = get_interval(&state.dbm, *r);
            forget(&mut state.dbm, dst);
            
            match (r_lo, r_hi) {
                (Some(lo), Some(hi)) if lo > 0 => {
                    assume_ge_imm(&mut state.dbm, dst, 0);
                    assume_le_imm(&mut state.dbm, dst, hi - 1);
                }
                (Some(lo), _) if lo > 0 => {
                    assume_ge_imm(&mut state.dbm, dst, 0);
                }
                _ => {}
            }
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    state.set_tnum(dst, Tnum::unknown());
}

pub(crate) fn handle_div(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(imm) => apply_div_imm(&mut state.dbm, dst, *imm),
        Operand::Reg(r_src) => apply_div_reg(&mut state.dbm, dst, *r_src),
    }

    if width == Width::W32 {
        apply_and_imm(&mut state.dbm, dst, 0xFFFFFFFF);
    }

    state.set_tnum(dst, Tnum::unknown());
}
