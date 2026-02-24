// src/analysis/transfer/alu/arithmetic.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::ast::{Operand, Width};
use crate::zone::domain::{
    apply_add_imm, apply_add_reg, apply_and_imm, apply_div_imm, apply_div_reg, apply_mul_imm,
    apply_neg, apply_sub_reg, assign_interval, assign_reg_offset, assume_ge_imm, assume_le_imm,
    forget, get_fixed_value, get_interval,
};
use crate::zone::tnum::Tnum;
use log::debug;

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
                if lo == hi && lo != i64::MIN && lo != i64::MAX {
                    // Known constant: shift all relations exactly
                    apply_add_imm(&mut state.dbm, dst, lo);
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
                if lo == hi && lo != i64::MIN && lo != i64::MAX {
                    assign_reg_offset(&mut state.dbm, dst, *r, lo);
                } else {
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(*r)) {
                        forget(&mut state.dbm, *r);
                        assign_interval(&mut state.dbm, *r, off, off);
                    }
                    forget(&mut state.dbm, dst);
                    if hi != i64::MAX {
                        state.dbm.add_constraint(dst, *r, hi);
                    }
                    if lo != i64::MIN
                        && lo > i64::MIN {
                            state.dbm.add_constraint(*r, dst, -lo);
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
    let new_tnum = if width == Width::W32 {
        new_tnum.trunc32()
    } else {
        new_tnum
    };
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
            let dst_type = in_types.get(dst);
            let src_type = in_types.get(*r);
            let dst_is_ptr = dst_type.is_pointer();
            let src_is_ptr = src_type.is_pointer();

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
            } else if is_packet_ptr_subtraction(&dst_type, &src_type) {
                // ══════════════════════════════════════════════════════════════════
                // SPECIAL CASE: Packet Pointer Subtraction (Correlated Branch Support)
                // ══════════════════════════════════════════════════════════════════
                //
                // When computing `dst = packet_end - packet`, the result is a scalar
                // representing the packet length (i.e., @data_end - @data).
                //
                // PROBLEM: Standard DBM subtraction computes interval bounds but loses
                // the relationship between the scalar result and the anchor difference.
                // Later, when a branch constrains this scalar (e.g., `if (14 > length)`),
                // the constraint doesn't propagate to the anchor relationship, so packet
                // bounds checks fail even when they should succeed.
                //
                // SOLUTION: Link the scalar result to @data_end by copying the src
                // register's anchor constraints. This enables DBM closure to propagate
                // scalar constraints to anchor constraints:
                //
                //   1. Set D[dst, @data_end] = D[src, @data_end]  (typically 0)
                //   2. Set D[@data_end, dst] = D[@data_end, src]  (packet length bound)
                //
                // Then when we constrain `dst >= 14`:
                //   - Closure computes: D[@data, @data_end] = min(old, D[@data, dst] + D[dst, @data_end])
                //   - With D[@data, dst] = -14 and D[dst, @data_end] = 0, we get D[@data, @data_end] = -14
                //   - This means @data_end >= @data + 14, enabling the packet bounds check!
                //
                // ══════════════════════════════════════════════════════════════════
                handle_packet_ptr_subtraction(state, dst, *r);
            } else {
                // scalar -= scalar, scalar -= ptr, other ptr -= ptr
                apply_sub_reg(&mut state.dbm, dst, *r);
            }
        }
    }

    let dst_tnum = state.get_tnum(dst);
    let new_tnum = match src {
        Operand::Imm(c) => dst_tnum.sub_imm(*c),
        Operand::Reg(r) => dst_tnum.sub(state.get_tnum(*r)),
    };
    let new_tnum = if width == Width::W32 {
        new_tnum.trunc32()
    } else {
        new_tnum
    };
    state.set_tnum(dst, new_tnum);

    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    let dst_is_ptr = in_types.get(dst).is_pointer();
    let src_is_ptr = match src {
        Operand::Imm(_) => false,
        Operand::Reg(r) => in_types.get(*r).is_pointer(),
    };
    if !(dst_is_ptr && src_is_ptr) {
        check_ptr_bounds(state, dst);
    }

    sync_tnum_to_dbm(state, dst);
}

pub(crate) fn handle_neg(state: &mut State, width: Width, dst: Reg) {
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

pub(crate) fn handle_mul(state: &mut State, width: Width, dst: Reg, src: &Operand) {
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

pub(crate) fn handle_mod(state: &mut State, width: Width, dst: Reg, src: &Operand) {
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

            if r_lo > 0 && r_hi != i64::MAX {
                assume_ge_imm(&mut state.dbm, dst, 0);
                assume_le_imm(&mut state.dbm, dst, r_hi - 1);
            } else if r_lo > 0 {
                assume_ge_imm(&mut state.dbm, dst, 0);
            }
        }
    }

    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    state.set_tnum(dst, Tnum::unknown());
}

pub(crate) fn handle_div(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(imm) => apply_div_imm(&mut state.dbm, dst, *imm),
        Operand::Reg(r_src) => apply_div_reg(&mut state.dbm, dst, *r_src),
    }

    if width == Width::W32 {
        apply_and_imm(&mut state.dbm, dst, 0xFFFFFFFF);
    }

    state.set_tnum(dst, Tnum::unknown());
}

// ══════════════════════════════════════════════════════════════════════════════
//  Packet Pointer Subtraction Helpers
// ══════════════════════════════════════════════════════════════════════════════

/// Checks if this is a packet pointer subtraction that produces a packet length scalar.
///
/// Valid patterns:
///   - PtrToPacketEnd - PtrToPacket      → packet length (@data_end - @data)
///   - PtrToPacket - PtrToPacketMeta     → metadata length (@data - @data_meta)
///   - PtrToPacketEnd - PtrToPacketMeta  → total length (@data_end - @data_meta)
fn is_packet_ptr_subtraction(dst_type: &RegType, src_type: &RegType) -> bool {
    matches!(
        (dst_type, src_type),
        (RegType::PtrToPacketEnd, RegType::PtrToPacket)
            | (RegType::PtrToPacketEnd, RegType::PtrToPacketMeta)
            | (RegType::PtrToPacket, RegType::PtrToPacketMeta)
    )
}

/// Handles the special case of packet pointer subtraction.
///
/// When computing `dst = packet_end - packet`, we need to link the scalar result
/// to the anchor system so that future constraints on dst propagate to anchor
/// relationships via DBM closure.
///
/// # The Problem
///
/// After `dst = @data_end - @data`, the scalar `dst` represents the packet length.
/// When a branch establishes `dst >= 14`:
///   - This sets D[Zero, dst] = -14 (absolute bound)
///   - But packet bounds checks use D[base, @data_end] where base is at @data
///   - Without proper linkage, the constraint doesn't propagate
///
/// # DBM Constraint Setup
///
/// The key insight is that `dst = @data_end - @data` means:
///   - `dst == @data_end - @data`
///   - So `@data + dst == @data_end`
///   - Or: `@data - @data_end == -dst`
///
/// We establish this by linking both the scalar and @data to Zero:
///   1. D[dst, @data_end] = 0            (dst <= @data_end, from src at @data)
///   2. D[@data, Zero] = 0, D[Zero, @data] = 0  (link @data to Zero reference)
///
/// With these constraints, when `dst >= 14` is established:
///   - D[Zero, dst] = -14 (from assume_ge_imm)
///   - Closure: D[@data, dst] = min(old, D[@data, Zero] + D[Zero, dst]) = min(old, 0 + (-14)) = -14
///   - Closure: D[@data, @data_end] = min(old, D[@data, dst] + D[dst, @data_end]) = min(0, -14 + 0) = -14
///   - This means @data_end >= @data + 14 ✓
fn handle_packet_ptr_subtraction(state: &mut State, dst: Reg, src: Reg) {
    // First, perform standard subtraction to compute interval bounds
    apply_sub_reg(&mut state.dbm, dst, src);

    let start_anchor = Reg::AnchorData;
    let end_anchor = Reg::AnchorDataEnd;

    // Link dst to @data_end (dst <= @data_end)
    // Copy from src since src is at @data, and @data <= @data_end
    let dst_to_end = state.dbm.get(src, end_anchor);
    state.dbm.add_constraint(dst, end_anchor, dst_to_end);

    // Link dst to @data_end in reverse (@data_end - dst relationship)
    let end_to_dst = state.dbm.get(end_anchor, src);
    state.dbm.add_constraint(end_anchor, dst, end_to_dst);

    // KEY FIX: Link @data to Zero so that absolute constraints on dst
    // (like `dst >= 14`) propagate through to anchor relationships.
    //
    // The closure path is: @data → Zero → dst → @data_end
    //   D[@data, dst] = D[@data, Zero] + D[Zero, dst]
    //   D[@data, @data_end] = D[@data, dst] + D[dst, @data_end]
    //
    // By linking @data to Zero (both directions at 0), we ensure:
    //   - D[@data, Zero] = 0 and D[Zero, @data] = 0
    //   - When D[Zero, dst] = -14, then D[@data, dst] = -14
    //   - Then D[@data, @data_end] = -14 + 0 = -14
    state.dbm.add_constraint(start_anchor, Reg::Zero, 0);
    state.dbm.add_constraint(Reg::Zero, start_anchor, 0);

    state.dbm.close();

    debug!(
        "Packet ptr subtraction: linked {} to anchors (D[dst,end]={}, D[end,dst]={})",
        dst.name(),
        dst_to_end,
        end_to_dst
    );
}
