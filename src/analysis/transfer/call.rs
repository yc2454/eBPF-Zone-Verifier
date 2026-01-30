// src/analysis/transfer/call.rs
//
// Call and CallRel instruction handling, helper validation

use crate::analysis::env::{VerifierEnv, VerificationError};
use crate::analysis::state::State;
use crate::analysis::reg_types::{RegType, TypeState};
use crate::zone::domain::{Reg, forget, assume_ge_const, assume_le_const, is_zero, nonneg};
use crate::analysis::transfer::access;
use crate::common::constants;
use log::{error, warn};

use super::types::{update_call_types, helper_invalidates_packets};
use super::common::check_regs_readable;

/// Transfer function for helper Call instructions.
pub(crate) fn transfer_call(
    env: &mut VerifierEnv,
    mut state: State,
    helper: u32,
) -> Vec<State> {
    let in_types = state.types.clone();
    let pc = state.pc;

    // ========================================================================
    // Check argument registers are readable before the call
    // Most helpers use R1-R5 as arguments
    // ========================================================================
    let arg_regs = get_helper_arg_regs(helper);
    if !check_regs_readable(env, &state, &arg_regs) {
        return vec![];
    }

    // ========================================================================
    // Validate helper arguments BEFORE executing
    // ========================================================================
    validate_helper_args(env, &state, helper, &in_types, pc);
    
    // ========================================================================
    // SPECIAL CASE: bpf_tail_call
    // 
    // Semantics:
    //   - SUCCESS: Jump to target program, NEVER RETURNS (like exit)
    //   - FAILURE: Falls through to next instruction
    //
    // We only model the FAILURE path. Success means execution went elsewhere.
    // ========================================================================
    if helper == constants::BPF_TAIL_CALL {
        // Validate arguments (optional warnings)
        if !matches!(in_types.get(Reg::R1), RegType::PtrToCtx) {
            warn!("[Verifier] tail_call R1 should be PTR_TO_CTX at pc {}", pc);
        }
        if !matches!(in_types.get(Reg::R2), RegType::PtrToMapObject { .. }) {
            warn!("[Verifier] tail_call R2 should be PTR_TO_MAP at pc {}", pc);
        }
        
        // Update types (clobber caller-saved, R0 = scalar)
        update_call_types(&in_types, &mut state.types, helper);
        
        // Forget caller-saved in DBM
        for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            forget(&mut state.dbm, r);
        }
        
        // Return only the failure path (fall through)
        state.pc += 1;
        return vec![state];
    }
    
    // ========================================================================
    // Normal helper handling
    // ========================================================================

    // 1. Update types
    update_call_types(&in_types, &mut state.types, helper);
    
    // 2. Update DBM - forget caller-saved registers
    for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        forget(&mut state.dbm, r);
    }
    
    // 3. Apply return value bounds for specific helpers
    match helper {
        constants::BPF_REDIRECT => {
            // Returns TC_ACT_* (0-7)
            assume_ge_const(&mut state.dbm, Reg::R0, 0);
            assume_le_const(&mut state.dbm, Reg::R0, 7);
        }
        constants::BPF_FIB_LOOKUP => {
            // Returns BPF_FIB_LKUP_RET_* (0-8)
            assume_ge_const(&mut state.dbm, Reg::R0, 0);
            assume_le_const(&mut state.dbm, Reg::R0, 8);
        }
        constants::BPF_MAP_UPDATE_ELEM | 
        constants::BPF_MAP_DELETE_ELEM |
        constants::BPF_SKB_STORE_BYTES |
        constants::BPF_XDP_ADJUST_HEAD => {
            // Returns 0 on success, negative on error
            // Could add bounds but being conservative for now
        }
        _ => {}
    }
    
    // 4. Forget packet pointer DBM entries if they were invalidated
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            if r != Reg::R10 {
                match in_types.get(r) {
                    RegType::PtrToPacket { .. } | RegType::PtrToPacketEnd => {
                        forget(&mut state.dbm, r);
                    }
                    _ => {}
                }
            }
        }
    }
    
    // 5. Advance PC and return
    state.pc += 1;
    vec![state]
}

/// Transfer function for relative Call (BPF-to-BPF function call) instructions.
pub(crate) fn transfer_call_rel(
    env: &mut VerifierEnv,
    mut state: State,
    target: usize,
) -> Vec<State> {
    // Target cannot be a back edge
    if target <= state.pc {
        env.fail(VerificationError::BackEdge { pc: state.pc, target });
        return vec![];
    }

    // BPF enforces max call depth of 8
    if state.call_stack.len() >= 8 {
        env.fail(VerificationError::MaxCallDepthExceeded { pc: state.pc });
        return vec![];
    }

    // Push return address and jump to callee
    state.call_stack.push(state.pc + 1);
    state.pc = target;

    // Only the "enter callee" path — return path comes from callee's Exit
    vec![state]
}

/// Validates helper function arguments.
fn validate_helper_args(
    env: &mut VerifierEnv,
    state: &State,
    helper: u32,
    types: &TypeState,
    pc: usize,
) {
    match helper {
        constants::BPF_MAP_LOOKUP_ELEM => {
            // R1 = map, R2 = key pointer
            let key_size = get_map_key_size(types.get(Reg::R1), env);
            if let Some(size) = key_size {
                check_readable_arg(env, state, types, Reg::R2, size, pc);
            }
        }
        constants::BPF_MAP_UPDATE_ELEM => {
            // R1 = map, R2 = key pointer, R3 = value pointer, R4 = flags
            let (key_size, val_size) = get_map_key_value_size(types.get(Reg::R1), env);
            if let Some(size) = key_size {
                check_readable_arg(env, state, types, Reg::R2, size, pc);
            }
            if let Some(size) = val_size {
                check_readable_arg(env, state, types, Reg::R3, size, pc);
            }
        }
        constants::BPF_MAP_DELETE_ELEM => {
            // R1 = map, R2 = key pointer
            let key_size = get_map_key_size(types.get(Reg::R1), env);
            if let Some(size) = key_size {
                check_readable_arg(env, state, types, Reg::R2, size, pc);
            }
        }
        constants::BPF_GET_SOCKET_COOKIE | constants::BPF_CSUM_UPDATE  => { 
            // R1 must be PtrToCtx
            if !matches!(types.get(Reg::R1), RegType::PtrToCtx) {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            }
        }
        constants::BPF_SKB_ECN_SET_CE => {
            // R1 can be PtrToCtx or NULL
            if !matches!(types.get(Reg::R1), RegType::PtrToCtx) && !is_zero(&state.dbm, Reg::R1) {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            }
        }
        constants::BPF_SKB_LOAD_BYTES => {
            if !matches!(types.get(Reg::R1), RegType::PtrToCtx) {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            } else {
                // R4 cannot be negative because it's ARG_CONST_SIZE type
                if !nonneg(&state.dbm, Reg::R4) {
                    env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R4 });
                }
            }
        }
        _ => {
            warn!("Helper arg not checked.");
        }
    }
}

fn check_readable_arg(
    env: &mut VerifierEnv,
    state: &State,
    types: &TypeState,
    reg: Reg,
    size: u32,
    pc: usize,
) {
    match types.get(reg) {
        RegType::PtrToStack { offset: Some(off) } => {
            access::check_stack_arg_readable(env, state, off, size as i64, pc);
        }
        RegType::PtrToStack { offset: None } => {
            // Unknown stack offset - need to use DBM bounds
            // For now, reject conservatively
            env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
        }
        RegType::PtrToMapValue { .. } => {
            // Map values are always considered initialized
        }
        RegType::PtrToPacket { .. } => {
            // Packet data is initialized (bounds checked elsewhere)
        }
        _ => {
            // Not a valid pointer type for this argument
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!("Not a valid pointer type for argument")
        }
    }
}

fn get_map_key_size(map_type: RegType, env: &VerifierEnv) -> Option<u32> {
    match map_type {
        RegType::PtrToMapObject { map_idx } => 
            env.ctx.map_defs.get(map_idx).map(|md| md.key_size),
        _ => None,
    }
}

fn get_map_key_value_size(map_type: RegType, env: &VerifierEnv) -> (Option<u32>, Option<u32>) {
    match map_type {
        RegType::PtrToMapObject { map_idx } => {
            if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                (Some(map_def.key_size), Some(map_def.value_size))
            } else {
                (None, None)
            }
        }
        _ => (None, None),
    }
}

/// Returns the argument registers that must be readable for a given helper.
fn get_helper_arg_regs(helper: u32) -> Vec<Reg> {
    match helper {
        // 1 arg: R1
        constants::BPF_GET_SOCKET_COOKIE |
        constants::BPF_CSUM_UPDATE |
        constants::BPF_SKB_ECN_SET_CE => {
            vec![Reg::R1]
        }
        
        // 2 args: R1, R2
        constants::BPF_MAP_LOOKUP_ELEM |
        constants::BPF_MAP_DELETE_ELEM |
        constants::BPF_REDIRECT => {
            vec![Reg::R1, Reg::R2]
        }
        
        // 3 args: R1, R2, R3
        constants::BPF_TAIL_CALL |
        constants::BPF_SKC_LOOKUP_TCP => {
            vec![Reg::R1, Reg::R2, Reg::R3]
        }
        
        // 4 args: R1, R2, R3, R4
        constants::BPF_MAP_UPDATE_ELEM |
        constants::BPF_SKB_LOAD_BYTES |
        constants::BPF_SKB_STORE_BYTES => {
            vec![Reg::R1, Reg::R2, Reg::R3, Reg::R4]
        }
        
        // 5 args: R1, R2, R3, R4, R5
        constants::BPF_SK_LOOKUP_TCP |
        constants::BPF_SK_LOOKUP_UDP |
        constants::BPF_FIB_LOOKUP => {
            vec![Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5]
        }
        
        // Default: conservatively check R1 (most helpers need at least one arg)
        _ => {
            vec![Reg::R1]
        }
    }
}
