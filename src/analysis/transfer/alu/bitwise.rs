// src/analysis/transfer/alu/bitwise.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{Operand, Width};
use crate::domains::tnum::Tnum;
use crate::refinement::bcf::BPF_AND;

use super::helpers::{bcf_reg_bounds, sync_tnum_to_dbm};

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
                let (s32_min, s32_max) = state.domain.get_s32_bounds(*r);
                state.domain.forget(dst);
                if preserved {
                    state.domain.assign_reg(dst, *r);
                } else {
                    state.domain.assume_ge_imm(dst, u32_min as i64);
                    state.domain.assume_le_imm(dst, u32_max as i64);
                }
                // Always propagate src's s32 shadow to dst — W32 mov
                // copies the low 32 bits unchanged, so the s32
                // interpretation of dst matches the s32 view of src.
                // Required for LSM int-hook `return ret;` patterns
                // where `ret` was bounded `[-MAX_ERRNO, 0]` in s32 at
                // entry and the W32 mov before exit must preserve
                // that band for the retval rule check.
                state.domain.set_s32_bounds(dst, s32_min, s32_max);
            } else {
                if dst == *r {
                    return;
                }
                // Copy register state including pointer offset info
                state.domain.assign_reg(dst, *r);
            }
        }
        Operand::Imm(c) => {
            let c64 = if width == Width::W32 {
                (*c as u32) as i64
            } else {
                *c
            };
            state.domain.forget(dst);
            state.domain.assume_le_imm(dst, c64);
            state.domain.assume_ge_imm(dst, c64);
            // For W32 mov of an immediate, also set the s32 shadow:
            // the assembler-encoded `c` is already a 32-bit value, and
            // `w0 = -1` lands as imm=0xFFFFFFFF (u32). The s32 view is
            // `c as i32` (= -1). Without this, the s32 shadow stays at
            // the default full s32 range and downstream W32 mov-from-reg
            // / retval checks (LSM int-hook `return -EPERM`) lose the
            // s32 precision the kernel uses for retval_range_s32.
            if width == Width::W32 {
                let c32 = *c as i32;
                state.domain.set_s32_bounds(dst, c32, c32);
            }
        }
    }

    // --- BCF symbolic mirror. Mirrors kernel `bcf_mov32` / `bcf_mov`
    //     (verifier.c:16325-16374) with the kernel-shape DAG layout. ---
    let src_bounds = match src {
        Operand::Reg(r) => Some(bcf_reg_bounds(state, *r)),
        _ => None,
    };
    if let (Some(bcf), Some(d)) = (state.bcf.as_mut(), dst.bcf_idx()) {
        match src {
            Operand::Imm(c) => {
                let v = if width == Width::W32 {
                    (*c as u32) as u64
                } else {
                    *c as u64
                };
                let idx = bcf.add_val64(v);
                bcf.bind_reg(d, idx);
            }
            Operand::Reg(r) => {
                let new_idx = match r.bcf_idx() {
                    Some(si) => {
                        let sb = src_bounds.unwrap();
                        let alu32 = width == Width::W32;
                        // 32-bit form for MOV32, 64-bit form for MOV64.
                        let src_expr = bcf.reg_expr(si, &sb, alu32);
                        if alu32 {
                            // MOV32 zero-extends low 32 bits into 64-bit dst.
                            bcf.add_extend(false, 32, 64, src_expr)
                        } else {
                            src_expr
                        }
                    }
                    None => bcf.add_val64(0),
                };
                bcf.bind_reg(d, new_idx);
            }
        }
    }
}

pub(crate) fn handle_and(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    let (min_op, max_op) = state.domain.get_interval(dst);
    let input_nonnegative = min_op >= 0;

    let (old_s32_min, old_s32_max) = state.domain.get_s32_bounds(dst);

    // Pre-op snapshot for BCF: capture dst's BCF bounds BEFORE the
    // abstract op modifies them. Mirrors the kernel's call ordering at
    // verifier.c:16178 (bcf_alu reads pre-op `dst_reg->bcf_expr` after the
    // abstract op runs, but the operands' bounds are pre-op via the
    // already-materialized cached values).
    let dst_bounds_pre = bcf_reg_bounds(state, dst);

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

    // --- BCF symbolic mirror. Mirrors kernel `bcf_alu` (verifier.c:15139)
    //     with the kernel-shape width discipline. For W32 AND with an
    //     immediate, emits AND_32(reg_expr32, val_32) then ZEXT to 64.
    //     For W64 AND where the post-op result fits in u32, the kernel
    //     STILL uses 32-bit BCF ops as a precision optimization. ---
    let dst_bounds_post = bcf_reg_bounds(state, dst);
    let op_u32 = dst_bounds_post.fit_u32();
    let op_s32 = dst_bounds_post.fit_s32();
    let alu32_class = width == Width::W32;
    let alu32 = alu32_class || op_u32 || op_s32;
    let bits: u16 = if alu32 { 32 } else { 64 };

    if let Some(d) = dst.bcf_idx() {
        if let (Some(bcf), Operand::Imm(mask)) = (state.bcf.as_mut(), src) {
            let dst_expr = bcf.reg_expr(d, &dst_bounds_pre, alu32);
            let mask_val = if width == Width::W32 {
                (*mask as u32) as u64
            } else {
                *mask as u64
            };
            let mask_expr = bcf.add_val(mask_val, alu32);
            let alu_result = bcf.add_alu(BPF_AND, dst_expr, mask_expr, bits);
            // Extend back to 64-bit for the cached reg slot. ZEXT for
            // alu32 or op_u32 cases; SEXT for op_s32; no-op for true 64-bit.
            let final_idx = if alu32 || op_u32 {
                bcf.add_extend(false, 32, 64, alu_result)
            } else if op_s32 {
                bcf.add_extend(true, 32, 64, alu_result)
            } else {
                alu_result
            };
            bcf.bind_reg(d, final_idx);
        } else if let Some(bcf) = state.bcf.as_mut() {
            // AND with a register: conservative — drop the symbolic expr.
            // (TODO Phase 4: support reg-reg AND via reg_expr on both.)
            bcf.clear_reg(d);
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
