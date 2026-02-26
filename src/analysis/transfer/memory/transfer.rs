use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/memory/transfer.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{AtomicOp, MemSize, Operand};
use crate::domains::domain::{
    assume_eq_imm, assume_ge_imm, assume_le_imm, bind_to_anchor, forget, get_distance_fixed,
    get_distance_interval,
};
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
        && let Some(base_off) = get_distance_fixed(state.dbm(), base, Reg::R10)
        && state.fill_at(frame_level, dst, off + base_off as i16, size)
    {
        state.pc += 1;
        return vec![state];
    }

    update_load_types(env, &mut state, access_size as usize, dst, base, off);
    forget(state.dbm_mut(), dst);

    match size {
        MemSize::U8 => {
            assume_ge_imm(state.dbm_mut(), dst, 0);
            assume_le_imm(state.dbm_mut(), dst, 0xFF);
        }
        MemSize::U16 => {
            assume_ge_imm(state.dbm_mut(), dst, 0);
            assume_le_imm(state.dbm_mut(), dst, 0xFFFF);
        }
        MemSize::U32 => {
            assume_ge_imm(state.dbm_mut(), dst, 0);
            assume_le_imm(state.dbm_mut(), dst, 0xFFFFFFFF);
        }
        MemSize::U64 => {}
    }

    match state.types.get(dst) {
        RegType::PtrToPacket => {
            bind_to_anchor(state.dbm_mut(), dst, Reg::AnchorData);
        }
        RegType::PtrToPacketMeta => {
            bind_to_anchor(state.dbm_mut(), dst, Reg::AnchorDataMeta);
        }
        RegType::PtrToPacketEnd => {
            bind_to_anchor(state.dbm_mut(), dst, Reg::AnchorDataEnd);
        }
        _ => {}
    }

    state.set_tnum(dst, Tnum::unknown());
    state.pc += 1;
    vec![state]
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
        if let Some(base_off) = get_distance_fixed(state.dbm(), base, Reg::R10) {
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
            let (lo, hi) = get_distance_interval(state.dbm(), base, Reg::R10);
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
        get_distance_fixed(state.dbm(), base, Reg::R10).map(|o| o + off as i64)
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
            forget(state.dbm_mut(), Reg::R0);
            state.set_tnum(Reg::R0, Tnum::unknown());
        }
    } else if fetch && !reloaded {
        forget(state.dbm_mut(), src);
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

                    forget(state.dbm_mut(), dst);
                    assume_eq_imm(state.dbm_mut(), dst, val as i64);
                    state.types.set(dst, RegType::ScalarValue);

                    return true;
                }
            }
        }
    }
    false
}
