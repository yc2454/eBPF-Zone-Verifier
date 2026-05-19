// src/analysis/transfer/alu/bitwise.rs

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{Operand, Width};
use crate::domains::tnum::Tnum;
use crate::refinement::bcf::{BPF_AND, BPF_OR, BPF_XOR};

use super::helpers::{bcf_reg_bounds, emit_bcf_alu_binop, sync_tnum_to_dbm};

// BCF symbolic mirror for `mov32 dst, src` (W32 Reg→Reg). Mirrors kernel
// `bcf_alu` (verifier.c:15139)'s mov32 shape: reads src in 32-bit form,
// wraps with ZEXT to 64 for the cached form. Without this hook,
// downstream ALU ops (handle_arsh, handle_and, ...) materialize a fresh
// VAR for dst from its current abstract bounds instead of chaining
// through the kernel's `ZEXT(EXTRACT_LO_32(...))` shape, and the
// canonical hash of any later path_cond involving dst diverges from
// the kernel's runtime hash.
fn emit_bcf_mov_w32_reg(state: &mut State, dst: Reg, src: Reg) {
    let (Some(d), Some(s)) = (dst.bcf_idx(), src.bcf_idx()) else { return };
    let src_bounds = bcf_reg_bounds(state, src);
    if let Some(bcf) = state.bcf.as_mut() {
        let src_expr32 = bcf.reg_expr(s, &src_bounds, true);
        let final_idx = bcf.add_extend(false, 32, 64, src_expr32);
        bcf.bind_reg(d, final_idx);
    }
}

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
            // BCF symbolic mirror — W32 mov needs to chain ZEXT(EXTRACT_LO_32(src))
            // for downstream ALU/branch ops to see the kernel-shape expression.
            // W64 mov shares src's full cached expr (handled by the catch-all
            // below via ptr_const_off propagation pathways; for scalars the
            // tnum is already copied).
            if width == Width::W32 && dst != *r {
                emit_bcf_mov_w32_reg(state, dst, *r);
            } else if width == Width::W64 && dst != *r {
                // W64 mov: dst.cache = src.cache. Pull src's cached 64-bit
                // expr and bind it to dst so the chain stays intact.
                if let (Some(d), Some(s)) = (dst.bcf_idx(), r.bcf_idx()) {
                    let src_bounds = bcf_reg_bounds(state, *r);
                    if let Some(bcf) = state.bcf.as_mut() {
                        let src_expr = bcf.reg_expr(s, &src_bounds, false);
                        bcf.bind_reg(d, src_expr);
                    }
                }
            }
        }
    }

    // Carry the kernel's `ptr_reg->off` (`ptr_const_off`) across a
    // pointer-to-pointer mov. The `transfer_alu` catch-all already
    // cleared `ptr_const_off[dst]` (mov isn't Add/Sub on a pointer);
    // re-insert here when the source is a pointer-typed register so the
    // copy carries the offset. W32 mov truncates to low 32 bits — if
    // the source is a pointer, treat it the same as W64 (the kernel
    // does W64 type-preservation for ptr-mov; W32 ptr-to-scalar
    // demotion happens later in update_alu_types). `mov dst, R10` has
    // no `ptr_const_off` entry for R10; that means K_dst = 0 (fresh
    // anchor at r10), which matches the kernel's initialization.
    if let Operand::Reg(r) = src {
        if state.types.get(*r).is_pointer() && dst != *r {
            match state.ptr_const_off.get(r).copied() {
                Some(k) => {
                    state.ptr_const_off.insert(dst, k);
                }
                None => {
                    // R10 (or other fresh anchor): K starts at 0.
                    state.ptr_const_off.insert(dst, 0);
                }
            }
            // Carry `var_off_contributor` alongside `ptr_const_off`. A
            // ptr→ptr mov copies the variable-offset chain: if the src
            // pointer had a scalar contributor recorded (from an earlier
            // `ptr += scalar`), the dst pointer inherits it. Without this,
            // refine_map's case classification at a later helper-mem
            // access misreads dst as a constant-offset pointer (`ptr_is_var
            // = false`) and falls into case (i), producing a refine_cond
            // that uses the size reg directly instead of building
            // `ADD(off_expr, size_expr)` for case (iii). cvc5's proof for
            // the case-(i) shape on the trace_sys_enter_execve / similar
            // `r6 += (r0 << 32 >> 32); r1 = r6` flow hits a 338-child
            // FACTORING resolution step (the case-(iii) shape produces a
            // narrow proof). transfer_alu's catch-all already removed
            // dst's entry for !Add/Sub-Imm; re-insert here from src.
            if let Some(&contributor) = state.var_off_contributor.get(r) {
                state.var_off_contributor.insert(dst, contributor);
            }
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
    // already-materialized cached values). For the reg-source case also
    // snapshot the src reg's bounds (the abstract op only mutates dst, so
    // src is stable, but we must capture before borrowing `state.bcf`).
    let dst_bounds_pre = bcf_reg_bounds(state, dst);
    let src_bounds_pre = match src {
        Operand::Reg(r) => Some(bcf_reg_bounds(state, *r)),
        _ => None,
    };

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

    // --- BCF symbolic mirror. Mirrors kernel `bcf_alu` (verifier.c:15166)
    //     with the kernel-shape width discipline. ---
    //
    // Width selection mirrors `adjust_scalar_min_max_vals`
    // (verifier.c:16123-16124, 16209-16210):
    //
    //     op_u32 = fit_u32(dst_reg) && fit_u32(&src_reg);  // PRE-op dst + src
    //     ... op runs ...
    //     op_u32 &= fit_u32(dst_reg);                       // AND POST-op dst
    //
    // i.e. `op_u32 = fit_u32(dst_pre) && fit_u32(src) && fit_u32(dst_post)`
    // (and likewise op_s32). Checking only `dst_post` (the previous
    // behaviour) wrongly narrowed a W64 op whose operand was a full u64
    // — `r9 &= 2` after `r9 = *(u64*)(r6+0x168)` — into the 32-bit
    // EXTRACT+ZEXT form; the kernel keeps it plain 64-bit because the
    // pre-op `r9` does not fit u32 (calico_tc_skb_accepted_entrypoint
    // pc723 K5 — the 6-byte / canonical-hash gap vs kernel
    // 0x1c0a558f34021ac3). For an immediate source the kernel builds a
    // const `src_reg` from the width-extended imm; a constant always
    // fits s32/u32 except a W64 imm outside the u32 / s32 range.
    let dst_bounds_post = bcf_reg_bounds(state, dst);
    let (src_fits_u32, src_fits_s32) = match (src, &src_bounds_pre) {
        (_, Some(sb)) => (sb.fit_u32(), sb.fit_s32()),
        (Operand::Imm(m), None) => {
            let v = if width == Width::W32 {
                (*m as u32) as i64
            } else {
                *m
            };
            (
                (0..=u32::MAX as i64).contains(&v),
                (i32::MIN as i64..=i32::MAX as i64).contains(&v),
            )
        }
        (Operand::Reg(_), None) => (false, false),
    };
    let op_u32 = dst_bounds_pre.fit_u32() && src_fits_u32 && dst_bounds_post.fit_u32();
    let op_s32 = dst_bounds_pre.fit_s32() && src_fits_s32 && dst_bounds_post.fit_s32();
    let alu32_class = width == Width::W32;
    let alu32 = alu32_class || op_u32 || op_s32;
    let bits: u16 = if alu32 { 32 } else { 64 };

    if let Some(d) = dst.bcf_idx() {
        // Extend the AND result back to the 64-bit cached reg slot. ZEXT
        // for alu32/op_u32 cases; SEXT for op_s32; no-op for true 64-bit.
        let extend_back = |bcf: &mut crate::refinement::symbolic::SymbolicState,
                           alu_result: u32|
         -> u32 {
            if alu32 || op_u32 {
                bcf.add_extend(false, 32, 64, alu_result)
            } else if op_s32 {
                bcf.add_extend(true, 32, 64, alu_result)
            } else {
                alu_result
            }
        };
        match src {
            Operand::Imm(mask) => {
                if let Some(bcf) = state.bcf.as_mut() {
                    let dst_expr = bcf.reg_expr(d, &dst_bounds_pre, alu32);
                    let mask_val = if width == Width::W32 {
                        (*mask as u32) as u64
                    } else {
                        *mask as u64
                    };
                    let mask_expr = bcf.add_val(mask_val, alu32);
                    let alu_result = bcf.add_alu(BPF_AND, dst_expr, mask_expr, bits);
                    let final_idx = extend_back(bcf, alu_result);
                    bcf.bind_reg(d, final_idx);
                }
            }
            Operand::Reg(r) => {
                // Reg-source AND: mirror kernel `bcf_alu` (verifier.c:15139)
                // reg-reg handling — `AND(reg_expr(dst), reg_expr(src))`.
                // The faithful analog of handle_add's reg-reg path. When
                // src is a known constant (e.g. an ld_imm64 mask register),
                // `reg_expr` materializes it via its const_val branch as
                // `VAL_64(c)`, so the result is `AND(dst_expr, VAL_64(c))`
                // — exactly the kernel's `r1 &= r3` (r3=ld_imm64) DAG.
                // Without this the expr was dropped and any later branch on
                // dst materialized a bare fresh var, losing the AND that
                // the kernel keeps (cilium path_cond #2 divergence).
                let si = r.bcf_idx();
                if let (Some(bcf), Some(si)) = (state.bcf.as_mut(), si) {
                    let dst_expr = bcf.reg_expr(d, &dst_bounds_pre, alu32);
                    let src_expr = bcf.reg_expr(
                        si,
                        src_bounds_pre.as_ref().unwrap(),
                        alu32,
                    );
                    let alu_result = bcf.add_alu(BPF_AND, dst_expr, src_expr, bits);
                    let final_idx = extend_back(bcf, alu_result);
                    bcf.bind_reg(d, final_idx);
                } else if let Some(bcf) = state.bcf.as_mut() {
                    // src reg has no BCF slot (shouldn't happen for R0–R10);
                    // stay conservative and drop the expr.
                    bcf.clear_reg(d);
                }
            }
        }
    }
}

pub(crate) fn handle_or(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    // Pre-op BCF snapshots (before forget), mirroring handle_and.
    let dst_bounds_pre = bcf_reg_bounds(state, dst);
    let src_bounds_pre = match src {
        Operand::Reg(r) => Some(bcf_reg_bounds(state, *r)),
        _ => None,
    };

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

    // BCF: kernel routes BPF_OR through bcf_alu (in is_safe set) —
    // build OR(reg_expr(dst), reg_expr(src)) unless dropped. Was a
    // STALE-bcf_expr gap (no build, no clear).
    emit_bcf_alu_binop(
        state,
        BPF_OR,
        width,
        dst,
        src,
        &dst_bounds_pre,
        src_bounds_pre.as_ref(),
    );
}

pub(crate) fn handle_xor(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    // Pre-op BCF snapshots (before forget), mirroring handle_and.
    let dst_bounds_pre = bcf_reg_bounds(state, dst);
    let src_bounds_pre = match src {
        Operand::Reg(r) => Some(bcf_reg_bounds(state, *r)),
        _ => None,
    };

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

    // BCF: kernel routes BPF_XOR through bcf_alu (in is_safe set).
    // Was a STALE-bcf_expr gap (no build, no clear).
    emit_bcf_alu_binop(
        state,
        BPF_XOR,
        width,
        dst,
        src,
        &dst_bounds_pre,
        src_bounds_pre.as_ref(),
    );
}
