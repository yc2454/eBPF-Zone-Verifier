use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/memory/transfer.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{AtomicOp, MemSize, Operand};
use crate::domains::tnum::Tnum;

use super::access::{self};
use crate::analysis::transfer::common::{
    check_operand_readable, check_reg_readable, check_reg_writable,
};
use crate::analysis::transfer::types::{update_load_types, update_store_types};

pub(crate) fn transfer_load(
    env: &mut VerifierEnv,
    mut state: State,
    size: MemSize,
    dst: Reg,
    base: Reg,
    off: i16,
) -> Vec<State> {
    if !check_reg_readable(env, &state, base) {
        return vec![];
    }
    if !check_reg_writable(env, &state, dst) {
        return vec![];
    }

    let access_size = size.bytes() as i64;
    access::check_load(env, &state, base, access_size, off);

    if try_load_from_rodata(env, &mut state, dst, base, off, size) {
        state.pc += 1;
        return vec![state];
    }

    if let RegType::PtrToStack { frame_level } = state.types.get(base)
        && let Some(base_off) = state.domain.get_distance_fixed(base, Reg::R10)
        && state.fill_at(frame_level, dst, off + base_off as i16, size)
    {
        state.pc += 1;
        return vec![state];
    }

    update_load_types(env, &mut state, access_size as usize, dst, base, off);
    state.domain.forget(dst);

    match size {
        MemSize::U8 => {
            state.domain.assume_ge_imm(dst, 0);
            state.domain.assume_le_imm(dst, 0xFF);
        }
        MemSize::U16 => {
            state.domain.assume_ge_imm(dst, 0);
            state.domain.assume_le_imm(dst, 0xFFFF);
        }
        MemSize::U32 => {
            state.domain.assume_ge_imm(dst, 0);
            state.domain.assume_le_imm(dst, 0xFFFFFFFF);
        }
        MemSize::U64 => {}
    }

    match state.types.get(dst) {
        RegType::PtrToPacket => {
            state.domain.bind_to_anchor(dst, Reg::AnchorData);
        }
        RegType::PtrToPacketMeta => {
            state.domain.bind_to_anchor(dst, Reg::AnchorDataMeta);
        }
        RegType::PtrToPacketEnd => {
            state.domain.bind_to_anchor(dst, Reg::AnchorDataEnd);
        }
        _ => {}
    }

    state.set_tnum(dst, Tnum::unknown());
    state.pc += 1;
    vec![state]
}

/// Sign-extending load (LDSX, v6.6).
///
/// Semantically: load `size` bytes from `[base + off]` and sign-extend the
/// result to 64 bits in `dst`. Access checks (readability of base, type-of-ptr
/// rules, stack fills, fault reporting) mirror a regular load; the only
/// difference is the bounds we assign to `dst` after the load. Instead of the
/// unsigned [0, 2^n - 1] range that a zero-extending load produces, LDSX
/// produces a two's-complement sign-extended value in the range
/// [-(2^(n-1)), 2^(n-1) - 1].
///
/// Precision loss: we always forget `dst` and re-clamp, even on stack-fill
/// paths where a constant value might otherwise be preserved. Threading the
/// sign extension through every fill path is future work; correctness is
/// the priority here.
pub(crate) fn transfer_load_sx(
    env: &mut VerifierEnv,
    state: State,
    size: MemSize,
    dst: Reg,
    base: Reg,
    off: i16,
) -> Vec<State> {
    let (lo, hi) = match size {
        MemSize::U8 => (i8::MIN as i64, i8::MAX as i64),
        MemSize::U16 => (i16::MIN as i64, i16::MAX as i64),
        MemSize::U32 => (i32::MIN as i64, i32::MAX as i64),
        // LDSX DW doesn't exist in the ISA; decode rejects it. Defensive clamp.
        MemSize::U64 => (i64::MIN, i64::MAX),
    };

    let origin_pc = state.pc;
    let mut results = transfer_load(env, state, size, dst, base, off);

    // LDSX of a location that would yield a pointer (e.g. __sk_buff->data via
    // ctx narrow-load, or a spilled pointer on stack) is rejected by the
    // kernel verifier: sign-extending a pointer produces meaningless bits.
    let any_ptr_load = results
        .iter()
        .any(|s| !matches!(s.types.get(dst), RegType::ScalarValue | RegType::NotInit));
    if any_ptr_load {
        env.fail(VerificationError::UnsupportedModernFeature {
            pc: origin_pc,
            feature: "LDSX of a pointer-typed field",
        });
        return vec![];
    }

    for s in results.iter_mut() {
        s.types.set(dst, RegType::ScalarValue);
        s.domain.forget(dst);
        s.domain.assume_ge_imm(dst, lo);
        s.domain.assume_le_imm(dst, hi);
        s.set_tnum(dst, Tnum::unknown());
    }
    results
}

pub(crate) fn transfer_store(
    env: &mut VerifierEnv,
    mut state: State,
    size: MemSize,
    base: Reg,
    off: i16,
    src: &Operand,
) -> Vec<State> {
    if !check_reg_readable(env, &state, base) {
        return vec![];
    }
    if !check_operand_readable(env, &state, src) {
        return vec![];
    }

    let access_size = size.bytes() as i64;
    let src_type = match src {
        Operand::Reg(r) => state.types.get(*r),
        Operand::Imm(_) => RegType::ScalarValue,
    };

    access::check_store(env, &state, base, access_size, off, src_type);

    let base_type = state.types.get(base);
    if let RegType::PtrToStack { frame_level } = base_type {
        if let Some(base_off) = state.domain.get_distance_fixed(base, Reg::R10) {
            let full_offset = base_off + off as i64;
            match src {
                Operand::Reg(r) => {
                    state.spill_at(frame_level, *r, full_offset as i16, size);
                }
                Operand::Imm(k) => {
                    state.store_imm_to_stack_at(frame_level, *k, full_offset as i16, size);
                }
            }
            state.update_frame_depth(off);
            update_store_types(
                state.stack_at_mut(frame_level),
                src_type,
                size,
                Some(full_offset),
            );
        } else {
            let (lo, hi) = state.domain.get_distance_interval(base, Reg::R10);
            if lo != i64::MIN && hi != i64::MAX {
                let min_slot = lo + off as i64;
                let max_slot = hi + off as i64 + size.bytes() as i64;
                let stack = state.stack_at_mut(frame_level);
                for slot in min_slot..max_slot {
                    stack.invalidate_slot(slot as i16);
                }
            }
            state.update_frame_depth(off);
        }
    }

    state.pc += 1;
    vec![state]
}

pub(crate) fn transfer_atomic(
    env: &mut VerifierEnv,
    mut state: State,
    op: AtomicOp,
    fetch: bool,
    size: MemSize,
    base: Reg,
    off: i16,
    src: Reg,
) -> Vec<State> {
    if off % size.bytes() as i16 != 0 {
        env.fail(VerificationError::MisalignedAccess {
            pc: state.pc,
            off: off.into(),
        });
        return vec![];
    }

    if !check_reg_readable(env, &state, base) {
        return vec![];
    }
    if !check_reg_readable(env, &state, src) {
        return vec![];
    }
    if op == AtomicOp::CmpXchg && !check_reg_readable(env, &state, Reg::R0) {
        return vec![];
    }

    if op == AtomicOp::CmpXchg {
        if !check_reg_writable(env, &state, Reg::R0) {
            return vec![];
        }
    } else if fetch && !check_reg_writable(env, &state, src) {
        return vec![];
    }

    let base_ty = state.types.get(base);
    if matches!(base_ty, RegType::PtrToCtx) {
        env.fail(VerificationError::InvalidArgType {
            pc: state.pc,
            reg: base,
        });
        return vec![];
    }

    let access_size = size.bytes() as i64;
    access::check_load(env, &state, base, access_size, off);
    access::check_store(env, &state, base, access_size, off, state.types.get(src));
    if env.failed() {
        return vec![];
    }

    let reloaded = if op == AtomicOp::CmpXchg {
        state.fill(Reg::R0, off, size)
    } else if fetch {
        state.fill(src, off, size)
    } else {
        false
    };

    let resolved_offset = if matches!(base_ty, RegType::PtrToStack { .. }) {
        state
            .domain
            .get_distance_fixed(base, Reg::R10)
            .map(|o| o + off as i64)
    } else {
        None
    };
    update_store_types(
        state.stack_mut(),
        RegType::ScalarValue,
        size,
        resolved_offset,
    );
    if base == Reg::R10 {
        state.stack_mut().invalidate_slot(off);
    }

    if op == AtomicOp::CmpXchg {
        if !reloaded {
            state.domain.forget(Reg::R0);
            state.set_tnum(Reg::R0, Tnum::unknown());
        }
    } else if fetch && !reloaded {
        state.domain.forget(src);
        state.set_tnum(src, Tnum::unknown());
    }

    if base == Reg::R10 {
        state.update_frame_depth(off);
    }

    state.pc += 1;
    vec![state]
}

pub fn try_load_from_rodata(
    env: &VerifierEnv,
    state: &mut State,
    dst: Reg,
    base: Reg,
    insn_off: i16,
    size: MemSize,
) -> bool {
    if let RegType::PtrToMapValue {
        id: _,
        map_idx,
        offset: base_offset,
    } = state.types.get(base)
        && let Some(ptr_val) = base_offset
    {
        let map = &env.ctx.map_defs[map_idx];

        if let Some(data) = &map.initial_data {
            let abs_off = ptr_val + insn_off as i64;

            if abs_off >= 0 {
                let start = abs_off as usize;
                let len = size.bytes();

                if start + len <= data.len() {
                    let bytes = &data[start..start + len];

                    let mut val: u64 = 0;
                    for (i, &b) in bytes.iter().enumerate() {
                        val |= (b as u64) << (i * 8);
                    }

                    state.domain.forget(dst);
                    state.domain.assume_eq_imm(dst, val as i64);
                    state.types.set(dst, RegType::ScalarValue);

                    return true;
                }
            }
        }
    }
    false
}
