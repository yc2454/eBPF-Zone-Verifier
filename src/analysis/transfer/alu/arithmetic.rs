// src/analysis/transfer/alu/arithmetic.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::ast::{Operand, Width};
use crate::domains::tnum::Tnum;
use log::debug;

use super::helpers::{check_ptr_bounds, sync_tnum_to_dbm};

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
            state.domain.apply_add_imm(dst, *c);
        }
        Operand::Reg(r) => {
            let src_is_ptr = in_types.get(*r).is_pointer();
            let dst_is_ptr = in_types.get(dst).is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr += scalar: preserve relational info if possible
                let (lo, hi) = state.domain.get_interval(*r);
                if lo == hi && lo != i64::MIN && lo != i64::MAX {
                    // Known constant: shift all relations exactly
                    state.domain.apply_add_imm(dst, lo);
                } else {
                    // Non-constant: fall back to interval
                    if let Some(off) = RegType::get_ptr_offset(&in_types.get(dst)) {
                        state.domain.forget(dst);
                        state.domain.assign_interval(dst, off, off);
                    }
                    state.domain.apply_add_reg(dst, *r);
                }
            } else if src_is_ptr && !dst_is_ptr {
                // scalar += ptr
                let (lo, hi) = state.domain.get_interval(dst);
                if lo == hi && lo != i64::MIN && lo != i64::MAX {
                    state.domain.assign_reg_offset(dst, *r, lo);
                } else {
                    // For interval mode, combine ptr's PtrOffset with scalar's range
                    state.domain.apply_scalar_add_ptr(dst, *r, lo, hi);

                    // For zone domain, use constraint-based tracking
                    if !state.domain.is_interval_mode() {
                        if let Some(off) = RegType::get_ptr_offset(&in_types.get(*r)) {
                            state.domain.forget(*r);
                            state.domain.assign_interval(*r, off, off);
                        }
                        state.domain.forget(dst);
                        if hi != i64::MAX {
                            state.domain.add_constraint(dst, *r, hi);
                        }
                        if lo != i64::MIN && lo > i64::MIN {
                            state.domain.add_constraint(*r, dst, -lo);
                        }
                        state.domain.close();
                    }
                }
            } else {
                // scalar += scalar, ptr += ptr, etc.
                state.domain.apply_add_reg(dst, *r);
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
        state.domain.apply_w32_truncation(dst);
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
            state.domain.apply_add_imm(dst, -c);
        }
        Operand::Reg(r) => {
            let dst_type = in_types.get(dst);
            let src_type = in_types.get(*r);
            let dst_is_ptr = dst_type.is_pointer();
            let src_is_ptr = src_type.is_pointer();

            if dst_is_ptr && !src_is_ptr {
                // ptr -= scalar: try to preserve relational info
                let const_value = state.domain.get_fixed_value(*r);

                if const_value.is_some() {
                    // Scalar is a known constant: exact relational shift
                    state.domain.apply_add_imm(dst, -const_value.unwrap());
                } else {
                    // Bounded but not constant: fall back to interval
                    state.domain.apply_sub_reg(dst, *r);
                }
            } else if is_packet_ptr_subtraction(&dst_type, &src_type) {
                // SPECIAL CASE: Packet Pointer Subtraction (Correlated Branch Support)
                // When computing `dst = packet_end - packet`, the result is a scalar
                // representing the packet length (i.e., @data_end - @data).
                // Standard DBM subtraction computes interval bounds but loses
                // the relationship between the scalar result and the anchor difference.
                // We link the scalar result to @data_end by copying the src
                // register's anchor constraints so DBM closure propagates correctly.
                handle_packet_ptr_subtraction(state, dst, *r);
            } else {
                // scalar -= scalar, scalar -= ptr, other ptr -= ptr
                state.domain.apply_sub_reg(dst, *r);
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
        state.domain.apply_w32_truncation(dst);
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
    state.domain.apply_neg(dst);

    if width == Width::W32 {
        state.domain.apply_and_imm(dst, 0xFFFFFFFF);
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
            state.domain.apply_mul_imm(dst, *c);
        }
        Operand::Reg(_) => {
            state.domain.forget(dst);
        }
    }

    if width == Width::W32 {
        state.domain.apply_w32_truncation(dst);
    }

    state.set_tnum(dst, Tnum::unknown());
}

pub(crate) fn handle_mod(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(c) => {
            if *c > 0 {
                state.domain.forget(dst);
                state.domain.assume_ge_imm(dst, 0);
                state.domain.assume_le_imm(dst, c - 1);
            } else {
                state.domain.forget(dst);
            }
        }
        Operand::Reg(r) => {
            let (r_lo, r_hi) = state.domain.get_interval(*r);
            state.domain.forget(dst);

            if r_lo > 0 && r_hi != i64::MAX {
                state.domain.assume_ge_imm(dst, 0);
                state.domain.assume_le_imm(dst, r_hi - 1);
            } else if r_lo > 0 {
                state.domain.assume_ge_imm(dst, 0);
            }
        }
    }

    if width == Width::W32 {
        state.domain.apply_w32_truncation(dst);
    }

    state.set_tnum(dst, Tnum::unknown());
}

pub(crate) fn handle_div(state: &mut State, width: Width, dst: Reg, src: &Operand) {
    match src {
        Operand::Imm(imm) => state.domain.apply_div_imm(dst, *imm),
        Operand::Reg(r_src) => state.domain.apply_div_reg(dst, *r_src),
    }

    if width == Width::W32 {
        state.domain.apply_and_imm(dst, 0xFFFFFFFF);
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
/// When computing `dst = packet_end - packet`, we link the scalar result
/// to the anchor system so that future constraints on dst propagate to anchor
/// relationships via DBM closure.
fn handle_packet_ptr_subtraction(state: &mut State, dst: Reg, src: Reg) {
    // First, perform standard subtraction to compute interval bounds
    state.domain.apply_sub_reg(dst, src);

    let start_anchor = Reg::AnchorData;
    let end_anchor = Reg::AnchorDataEnd;

    // Link dst to @data_end (dst <= @data_end)
    // Copy from src since src is at @data, and @data <= @data_end
    let dst_to_end = state.domain.get(src, end_anchor);
    state.domain.add_constraint(dst, end_anchor, dst_to_end);

    // Link dst to @data_end in reverse (@data_end - dst relationship)
    let end_to_dst = state.domain.get(end_anchor, src);
    state.domain.add_constraint(end_anchor, dst, end_to_dst);

    // Link @data to Zero so that absolute constraints on dst
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
    state.domain.add_constraint(start_anchor, Reg::Zero, 0);
    state.domain.add_constraint(Reg::Zero, start_anchor, 0);

    state.domain.close();

    debug!(
        "Packet ptr subtraction: linked {} to anchors (D[dst,end]={}, D[end,dst]={})",
        dst.name(),
        dst_to_end,
        end_to_dst
    );
}
