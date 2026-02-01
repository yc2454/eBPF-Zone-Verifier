// src/analysis/transfer/memory.rs
//
// Load, Store, and AtomicAdd instruction handling

use crate::analysis::env::{VerifierEnv, VerificationError};
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::analysis::transfer::types::update_atomic_op_types;
use crate::ast::{Operand, MemSize, AtomicOp};
use crate::zone::domain::{Reg, forget, assume_ge_const, assume_le_const, assume_eq_const};
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
    // If successful, this sets the register to an exact constant (e.g., 0 or 1)
    // and we return early. This enables pruning dead configuration paths.
    if try_load_from_rodata(env, &mut state, dst, base, off, size) {
        state.pc += 1;
        return vec![state];
    }
    
    update_load_types(env, &mut state.types, access_size as usize, dst, base, off);
    forget(&mut state.dbm, dst);
    
    // Apply upper bounds for sub-64-bit loads
    match size {
        MemSize::U8 => {
            assume_ge_const(&mut state.dbm, dst, 0);
            assume_le_const(&mut state.dbm, dst, 0xFF);
        }
        MemSize::U16 => {
            assume_ge_const(&mut state.dbm, dst, 0);
            assume_le_const(&mut state.dbm, dst, 0xFFFF);
        }
        MemSize::U32 => {
            assume_ge_const(&mut state.dbm, dst, 0);
            assume_le_const(&mut state.dbm, dst, 0xFFFFFFFF);
        }
        MemSize::U64 => {
            // U64 loads can produce any 64-bit value.
            // Values >= 0x8000000000000000 are negative in signed i64.
            // No constraints can be safely added.
        }
    }

    // Update tnum
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

    access::check_store(env, &state, base, access_size, off);
    
    let src_type = {
        match src {
            Operand::Reg(r) => state.types.get(*r),
            Operand::Imm(_) => RegType::ScalarValue,
        }
    };
    let base_type = state.types.get(base);
    update_store_types(&mut state.types, src_type, size, base_type, off);
    
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
    // 1. Check readability
    if !check_reg_readable(env, &state, base) { return vec![]; }
    if !check_reg_readable(env, &state, src) { return vec![]; }
    if op == AtomicOp::CmpXchg {
        if !check_reg_readable(env, &state, Reg::R0) { return vec![]; }
    }

    // 2. Check writability
    if op == AtomicOp::CmpXchg {
        // CmpXchg always writes to R0
        if !check_reg_writable(env, &state, Reg::R0) { return vec![]; }
    } else if fetch {
        // Fetch operations write to 'src'
        if !check_reg_writable(env, &state, src) { return vec![]; }
    }

    let base_ty = state.types.get(base);

    // 3. Context Pointer Check
    // Atomic ops on Context (sk_buff, etc.) are generally forbidden.
    if matches!(base_ty, RegType::PtrToCtx) {
        env.fail(VerificationError::InvalidArgType { pc: state.pc, reg: base });
        return vec![];
    }

    // 4. Memory Safety Check
    // Atomic ops (Add, Xchg, CmpXchg) read the value from memory first.
    // We must ensure the memory at [base + off] is readable (initialized).
    let access_size = size.bytes() as i64;
    access::check_load(env, &state, base, access_size, off);
    access::check_store(env, &state, base, access_size, off);
    if env.failed() { return vec![]; }

    // 5. Update Memory State
    // The value in memory is being modified (added to, xor'd, swapped, etc.).
    // We treat the result in memory as a Scalar (number).
    update_store_types(&mut state.types, RegType::ScalarValue, size, base_ty, off);

    // 6. Update Register State (The "Fetch" part)
    // If BPF_FETCH is set, the instruction loads the *old* value from memory
    // into a register.
    update_atomic_op_types(&mut state.types, op, src, fetch);
    if op == AtomicOp::CmpXchg {
        // We don't know what that value is (it came from memory), so forget constraints.
        forget(&mut state.dbm, Reg::R0);
    } else if fetch {
        // Add, And, Or, Xor, Xchg with Fetch:
        // The 'src' register is overwritten with the OLD value from memory.
        forget(&mut state.dbm, src);
    }

    state.pc += 1;
    vec![state]
}

/// Attempts to load a concrete value from .rodata section.
/// Returns true if successful (state was updated with exact constant).
fn try_load_from_rodata(
    env: &VerifierEnv,
    state: &mut State,
    dst: Reg,
    base: Reg,
    insn_off: i16,
    size: MemSize,
) -> bool {
    // 1. Check if we are loading from a Map Pointer
    if let RegType::PtrToMapValue { map_idx, offset: base_offset } = state.types.get(base) {
        // We can only read if the pointer offset is known (not variable)
        if let Some(ptr_val) = base_offset {
            let map = &env.ctx.map_defs[map_idx];

            // 2. Check if this map has static content (.rodata)
            if let Some(data) = &map.initial_data {
                // Calculate absolute byte offset
                // abs_off = (pointer's internal offset) + (instruction's load offset)
                let abs_off = ptr_val + insn_off as i64;

                if abs_off >= 0 {
                    let start = abs_off as usize;
                    let len = size.bytes();

                    // 3. Bounds Check against the static data
                    if start + len <= data.len() {
                        // 4. Read the Bytes
                        let bytes = &data[start .. start + len];

                        // Convert bytes to u64 (Little Endian, standard for BPF)
                        let mut val: u64 = 0;
                        for (i, &b) in bytes.iter().enumerate() {
                            val |= (b as u64) << (i * 8);
                        }

                        // 5. Update State
                        // Reset the register to remove old constraints
                        forget(&mut state.dbm, dst);
                        
                        // Assign the EXACT constant value
                        assume_eq_const(&mut state.dbm, dst, val as i64);
                        
                        // Set type to Scalar (constants are just numbers)
                        state.types.set(dst, RegType::ScalarValue);

                        return true; // Successfully handled
                    }
                }
            }
        }
    }
    false
}
