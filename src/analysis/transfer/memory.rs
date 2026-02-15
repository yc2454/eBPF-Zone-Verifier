// src/analysis/transfer/memory.rs
//
// Load, Store, and AtomicAdd instruction handling

use crate::analysis::machine::env::{VerifierEnv, VerificationError};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType};
use crate::ast::{Operand, MemSize, AtomicOp};
use crate::analysis::machine::reg::Reg;
use crate::zone::domain::{assume_eq_imm, assume_ge_imm, assume_le_imm, bind_to_anchor, forget, get_distance_interval, get_distance_fixed};
use crate::zone::tnum::Tnum;
use crate::analysis::transfer::access;

use super::types::{update_load_types, update_store_types};
use super::common::{check_reg_readable, check_operand_readable, check_reg_writable};

/// Transfer function for Load instructions.
pub(crate) fn transfer_load(
    env: &mut VerifierEnv,
    mut state: State,
    size: MemSize,
    dst: Reg,
    base: Reg,
    off: i16,
) -> Vec<State> {
    // Check base register is readable
    if !check_reg_readable(env, &state, base) {
        return vec![];
    }

    // Check dst is writable
    if !check_reg_writable(env, &state, dst) {
        return vec![];
    }

    let access_size = size.bytes() as i64;

    access::check_load(env, &state, base, access_size, off);
    
    // Try to resolve concrete value from .rodata
    if try_load_from_rodata(env, &mut state, dst, base, off, size) {
        state.pc += 1;
        return vec![state];
    }

    // Try to reload from spilled stack slot
    if let RegType::PtrToStack { frame_level } = state.types.get(base) {
        if let Some(base_off) = get_distance_fixed(&state.dbm, base, Reg::R10) {
            if state.fill_at(frame_level, dst, off + base_off as i16, size) {
                state.pc += 1;
                return vec![state];
            }
        }
    }
    
    update_load_types(env, &mut state, access_size as usize, dst, base, off);
    forget(&mut state.dbm, dst);
    
    // Apply upper bounds for sub-64-bit loads
    match size {
        MemSize::U8 => {
            assume_ge_imm(&mut state.dbm, dst, 0);
            assume_le_imm(&mut state.dbm, dst, 0xFF);
        }
        MemSize::U16 => {
            assume_ge_imm(&mut state.dbm, dst, 0);
            assume_le_imm(&mut state.dbm, dst, 0xFFFF);
        }
        MemSize::U32 => {
            assume_ge_imm(&mut state.dbm, dst, 0);
            assume_le_imm(&mut state.dbm, dst, 0xFFFFFFFF);
        }
        MemSize::U64 => {}
    }

    // Bind dst reg to packet anchors if it's one of the packet pointers
    match state.types.get(dst) {
        RegType::PtrToPacket { .. } => {
            bind_to_anchor(&mut state.dbm, dst, Reg::AnchorData);
        },
        RegType::PtrToPacketMeta { .. } => {
            bind_to_anchor(&mut state.dbm, dst, Reg::AnchorDataMeta);
        },
        RegType::PtrToPacketEnd { .. } => {
            bind_to_anchor(&mut state.dbm, dst, Reg::AnchorDataEnd);
        },
        _ => {}
    }

    state.set_tnum(dst, Tnum::unknown());

    state.pc += 1;
    vec![state]
}

/// Transfer function for Store instructions.
pub(crate) fn transfer_store(
    env: &mut VerifierEnv,
    mut state: State,
    size: MemSize,
    base: Reg,
    off: i16,
    src: &Operand,
) -> Vec<State> {
    // Check base register and src operand are readable
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
    
    // Handle spilling to stack
    let base_type = state.types.get(base);
    if let RegType::PtrToStack { frame_level } = base_type {
        if let Some(base_off) = get_distance_fixed(&state.dbm, base, Reg::R10) {
            let full_offset = base_off + off as i64;
            match src {
                Operand::Reg(r) => {
                    // Full 64-bit register spill — snapshot the abstract state
                    state.spill_at(frame_level, *r, full_offset as i16, size);
                }
                Operand::Imm(k) => {
                    state.store_imm_to_stack_at(frame_level, *k, full_offset as i16, size);
                }
            }
            // Update frame depth
            state.update_frame_depth(off);
            update_store_types(state.stack_at_mut(frame_level), src_type, size, Some(full_offset));
        }
        // Variable offset: can't do precise spill, but must invalidate all
        // possibly-affected slots to prevent stale fills and mark as initialized.
        else {
            let (lo, hi) = get_distance_interval(&state.dbm, base, Reg::R10);
            if let (Some(l), Some(h)) = (lo, hi) {
                let min_slot = l + off as i64;
                let max_slot = h + off as i64 + size.bytes() as i64;
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
    // Alignment check 
    if off % size.bytes() as i16 != 0 {
        env.fail(VerificationError::MisalignedAccess { pc: state.pc, off: off.into() });
        return vec![];
    }

    // Check readability
    if !check_reg_readable(env, &state, base) { return vec![]; }
    if !check_reg_readable(env, &state, src) { return vec![]; }
    if op == AtomicOp::CmpXchg {
        if !check_reg_readable(env, &state, Reg::R0) { return vec![]; }
    }

    // Check writability
    if op == AtomicOp::CmpXchg {
        if !check_reg_writable(env, &state, Reg::R0) { return vec![]; }
    } else if fetch {
        if !check_reg_writable(env, &state, src) { return vec![]; }
    }

    let base_ty = state.types.get(base);

    // Context Pointer Check
    if matches!(base_ty, RegType::PtrToCtx) {
        env.fail(VerificationError::InvalidArgType { pc: state.pc, reg: base });
        return vec![];
    }

    // Memory Safety Check
    let access_size = size.bytes() as i64;
    access::check_load(env, &state, base, access_size, off);
    access::check_store(env, &state, base, access_size, off, state.types.get(src));
    if env.failed() { return vec![]; }

    // Try to reload spilled state BEFORE invalidating
    // (fetch reads the OLD value before the atomic op modifies it)
    let reloaded = if op == AtomicOp::CmpXchg {
        state.fill(Reg::R0, off, size)
    } else if fetch {
        state.fill(src, off, size)
    } else {
        false
    };

    // Update Memory State
    let resolved_offset = if matches!(base_ty, RegType::PtrToStack { .. }) {
        get_distance_fixed(&state.dbm, base, Reg::R10).map(|o| o + off as i64)
    } else {
        None
    };
    update_store_types(state.stack_mut(), RegType::ScalarValue, size, resolved_offset);
    if base == Reg::R10 {
        state.stack_mut().invalidate_slot(off);
    }

    // Update Register State (The "Fetch" part)
    // update_atomic_op_types(&mut state, op, base, src, fetch);
    if op == AtomicOp::CmpXchg {
        if !reloaded {
            forget(&mut state.dbm, Reg::R0);
            state.set_tnum(Reg::R0, Tnum::unknown());
        }
    } else if fetch {
        if !reloaded {
            forget(&mut state.dbm, src);
            state.set_tnum(src, Tnum::unknown());
        }
    }

    // Update frame depth if storing to stack
    if base == Reg::R10 {
        state.update_frame_depth(off);
    }

    state.pc += 1;
    vec![state]
}

/// Attempts to load a concrete value from .rodata section.
fn try_load_from_rodata(
    env: &VerifierEnv,
    state: &mut State,
    dst: Reg,
    base: Reg,
    insn_off: i16,
    size: MemSize,
) -> bool {
    if let RegType::PtrToMapValue { id: _, map_idx, offset: base_offset } = state.types.get(base) {
        if let Some(ptr_val) = base_offset {
            let map = &env.ctx.map_defs[map_idx];

            if let Some(data) = &map.initial_data {
                let abs_off = ptr_val + insn_off as i64;

                if abs_off >= 0 {
                    let start = abs_off as usize;
                    let len = size.bytes();

                    if start + len <= data.len() {
                        let bytes = &data[start .. start + len];

                        let mut val: u64 = 0;
                        for (i, &b) in bytes.iter().enumerate() {
                            val |= (b as u64) << (i * 8);
                        }

                        forget(&mut state.dbm, dst);
                        assume_eq_imm(&mut state.dbm, dst, val as i64);
                        state.types.set(dst, RegType::ScalarValue);

                        return true;
                    }
                }
            }
        }
    }
    false
}
