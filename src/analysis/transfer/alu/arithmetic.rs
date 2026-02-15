// src/analysis/transfer/alu/arithmetic.rs

use crate::analysis::machine::env::{VerifierEnv};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::ast::{Operand, Width};
use crate::analysis::machine::reg::Reg;
use crate::zone::domain::{assign_add_imm, assign_add_reg, assign_div_imm, assign_div_reg, assign_mul_imm, assign_neg, assign_sub_reg, forget, get_bounds, get_constant_value, link_regs_with_offset, set_bounds};
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
            assign_add_imm(&mut state.dbm, dst, *c);
        }
        Operand::Reg(r) => {
            let src_is_ptr = in_types.get(*r).is_pointer();
            let dst_is_ptr = in_types.get(dst).is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr += scalar: preserve relational info if possible
                let (lo, hi) = get_bounds(&state.dbm, *r);
                if lo == hi && lo.is_some() {
                    // Known constant: shift all relations exactly
                    assign_add_imm(&mut state.dbm, dst, lo.unwrap());
                } else {
                    // Non-constant: fall back to interval
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(dst)) {
                        forget(&mut state.dbm, dst);
                        set_bounds(&mut state.dbm, dst, off, off);
                    }
                    assign_add_reg(&mut state.dbm, dst, *r);
                }
            } else if src_is_ptr && !dst_is_ptr {
                // scalar += ptr
                let (lo, hi) = get_bounds(&state.dbm, dst);
                if lo == hi && lo.is_some() {
                    link_regs_with_offset(&mut state.dbm, dst, *r, lo.unwrap());
                } else {
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(*r)) {
                        forget(&mut state.dbm, *r);
                        set_bounds(&mut state.dbm, *r, off, off);
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
                assign_add_reg(&mut state.dbm, dst, *r);
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
            assign_add_imm(&mut state.dbm, dst, -c);
        }
        Operand::Reg(r) => {
            let dst_is_ptr = in_types.get(dst).is_pointer();
            let src_is_ptr = in_types.get(*r).is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr -= scalar: try to preserve relational info
                let const_value = get_constant_value(&state.dbm, *r);
                
                if const_value.is_some() {
                    // Scalar is a known constant: exact relational shift
                    assign_add_imm(&mut state.dbm, dst, -const_value.unwrap());
                } else {
                    // Bounded but not constant: fall back to interval
                    assign_sub_reg(&mut state.dbm, dst, *r);
                }
            } else {
                // scalar -= scalar, scalar -= ptr, ptr -= ptr
                assign_sub_reg(&mut state.dbm, dst, *r);
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
    assign_neg(&mut state.dbm, dst);

    if width == Width::W32 {
        crate::zone::domain::bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
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
            assign_mul_imm(&mut state.dbm, dst, *c);
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
                crate::zone::domain::assume_ge_const(&mut state.dbm, dst, 0);
                crate::zone::domain::assume_le_const(&mut state.dbm, dst, c - 1);
            } else {
                forget(&mut state.dbm, dst);
            }
        }
        Operand::Reg(r) => {
            let (r_lo, r_hi) = get_bounds(&state.dbm, *r);
            forget(&mut state.dbm, dst);
            
            match (r_lo, r_hi) {
                (Some(lo), Some(hi)) if lo > 0 => {
                    crate::zone::domain::assume_ge_const(&mut state.dbm, dst, 0);
                    crate::zone::domain::assume_le_const(&mut state.dbm, dst, hi - 1);
                }
                (Some(lo), _) if lo > 0 => {
                    crate::zone::domain::assume_ge_const(&mut state.dbm, dst, 0);
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
        Operand::Imm(imm) => assign_div_imm(&mut state.dbm, dst, *imm),
        Operand::Reg(r_src) => assign_div_reg(&mut state.dbm, dst, *r_src),
    }

    if width == Width::W32 {
        crate::zone::domain::bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
    }

    state.set_tnum(dst, Tnum::unknown());
}
