use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/call/transfer.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::analysis::transfer::types::{
    helper_invalidates_packets, update_call_rel_types, update_call_types,
};
use crate::ast::ProgramKind;
use crate::common::constants;
use crate::parsing::btf::SpecialFieldKind;
use crate::zone::domain::{
    self, assume_ge_imm, assume_le_imm, forget, get_interval_i64, proven_zero,
};
use crate::zone::tnum::Tnum;
use log::{error, info};

use super::checks::{check_mem_size_pairs, validate_helper_args};
use super::signatures::get_mem_size_pairs;

/// Transfer function for helper Call instructions.
pub(crate) fn transfer_call(env: &mut VerifierEnv, mut state: State, helper: u32) -> Vec<State> {
    let in_types = state.types.clone();
    let pc = state.pc;

    // ========================================================================
    // Check if the call is forbidden under an active lock
    // ========================================================================
    if state.has_active_lock() && !allowed_while_in_active_lock(helper) {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R0 });
        return vec![];
    }

    // ========================================================================
    // Validate pointer-size pairs
    // ========================================================================
    println!("[Verifier] pc {}: checking mem size pairs", pc);
    if !check_mem_size_pairs(env, &state, helper, pc) {
        return vec![];
    }

    // ========================================================================
    // Validate helper arguments BEFORE executing
    // ========================================================================
    println!("[Verifier] pc {}: validating helper arguments", pc);
    validate_helper_args(env, &state, helper, &in_types, pc);

    // ========================================================================
    // SPECIAL CASES
    // ========================================================================

    // bpf_tail_call
    if helper == constants::BPF_TAIL_CALL {
        if state.has_unreleased_refs() {
            error!("Entering tail calls but has unreleased references!");
            env.fail(VerificationError::UnreleasedReference {});
            return vec![];
        }
        update_call_types(env, &in_types, &mut state, helper);

        for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            forget(&mut state.dbm, r);
        }

        state.pc += 1;
        return vec![state];
    }

    // Special check for sk_release: R1 must have a reference
    if helper == constants::BPF_SK_RELEASE {
        if state.types.get(Reg::R1).get_ref_id().is_none() {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
    }

    // bpf_spin_lock and bpf_spin_unlock
    if helper == constants::BPF_SPIN_LOCK || helper == constants::BPF_SPIN_UNLOCK {
        if !check_and_handle_spin_lock(env, &mut state, helper) {
            return vec![];
        }
    }

    // bpf_sock_map_update: only allowed in BPF_PROG_TYPE_SOCK_OPS programs
    if helper == constants::BPF_SOCK_MAP_UPDATE {
        if !matches!(env.ctx.prog_kind, ProgramKind::SockOps) {
            env.fail(VerificationError::HelperNotAllowedForProgram {
                pc,
                helper,
                kind: env.ctx.prog_kind,
            });
            return vec![];
        }
    }

    // bpf_d_path is restrictive
    if helper == constants::BPF_D_PATH {
        if !matches!(env.ctx.prog_kind, ProgramKind::Tracing | ProgramKind::Lsm) {
            env.fail(VerificationError::HelperNotAllowedForProgram {
                pc,
                helper,
                kind: env.ctx.prog_kind,
            });
            return vec![];
        } else {
            if matches!(env.ctx.prog_kind, ProgramKind::Tracing)
                && matches!(env.ctx.kfunc.as_deref(), Some("d_path"))
            {
                env.fail(VerificationError::HelperNotAllowedForProgram {
                    pc,
                    helper,
                    kind: env.ctx.prog_kind,
                });
                return vec![];
            }
        }
    }

    // bpf_get_local_storage doesn't not support type 1 map and flag must be 0
    if helper == constants::BPF_GET_LOCAL_STORAGE {
        if let RegType::PtrToMapObject { map_idx } = state.types.get(Reg::R1) {
            if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                if map_def.type_ == constants::BPF_MAP_TYPE_HASH {
                    env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
                    return vec![];
                }
            }
        }
        if !proven_zero(&state.dbm, Reg::R2) {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R2 });
            return vec![];
        }
    }

    // ========================================================================
    // Normal helper handling
    // ========================================================================

    // 1. Update types
    update_call_types(env, &in_types, &mut state, helper);

    // 2. Apply return value bounds for specific helpers
    apply_return_bounds(&mut state, helper);

    // 3. Update DBM - forget caller-saved registers and reset Tnums
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        forget(&mut state.dbm, r);
        state.set_tnum(r, Tnum::unknown());
    }

    // 4. Forget packet pointer DBM entries if they were invalidated
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            if r != Reg::R10 {
                match in_types.get(r) {
                    RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta => {
                        forget(&mut state.dbm, r);
                    }
                    _ => {}
                }
            }
        }
        domain::reset_packet_anchors(&mut state.dbm);
    }

    // 5. Advance PC and return
    state.pc += 1;
    vec![state]
}

/// Apply return value bounds based on helper semantics.
fn apply_return_bounds(state: &mut State, helper: u32) {
    forget(&mut state.dbm, Reg::R0);
    state.set_tnum(Reg::R0, Tnum::unknown());
    match helper {
        constants::BPF_REDIRECT => {
            assume_ge_imm(&mut state.dbm, Reg::R0, 0);
            assume_le_imm(&mut state.dbm, Reg::R0, 7);
        }
        constants::BPF_FIB_LOOKUP => {
            assume_ge_imm(&mut state.dbm, Reg::R0, 0);
            assume_le_imm(&mut state.dbm, Reg::R0, 8);
        }
        constants::BPF_MAP_UPDATE_ELEM
        | constants::BPF_MAP_DELETE_ELEM
        | constants::BPF_SKB_STORE_BYTES
        | constants::BPF_SKB_LOAD_BYTES
        | constants::BPF_XDP_ADJUST_HEAD
        | constants::BPF_L3_CSUM_REPLACE
        | constants::BPF_L4_CSUM_REPLACE
        | constants::BPF_GET_CURRENT_COMM
        | constants::BPF_SOCK_MAP_UPDATE => {
            // Returns 0 on success, or -errno
            assume_le_imm(&mut state.dbm, Reg::R0, 0);
            assume_ge_imm(&mut state.dbm, Reg::R0, -constants::MAX_ERRNO);
        }
        constants::BPF_GET_PRANDOM_U32
        | constants::BPF_GET_CGROUP_CLASS_ID
        | constants::BPF_GET_HASH_RECALC => {
            // Returns a positive u32
            assume_ge_imm(&mut state.dbm, Reg::R0, 0);
            assume_le_imm(&mut state.dbm, Reg::R0, 0xFFFF_FFFF);
            state.set_tnum(Reg::R0, Tnum::u32_unknown());
        }
        constants::BPF_CSUM_DIFF => {
            // Returns a positive u32 (checksum) or negative error
            assume_ge_imm(&mut state.dbm, Reg::R0, -constants::MAX_ERRNO);
            assume_le_imm(&mut state.dbm, Reg::R0, 0xFFFF_FFFF);
            state.set_tnum(Reg::R0, Tnum::u32_unknown());
        }
        constants::BPF_GET_TASK_STACK => {
            let mem_size_pairs = get_mem_size_pairs(helper);
            let size_reg = mem_size_pairs[0].size_reg;
            let (_, hi) = get_interval_i64(&state.dbm, size_reg);
            println!("Size reg {} bound: {}", size_reg.name(), hi);
            assume_le_imm(&mut state.dbm, Reg::R0, hi);
        }
        constants::BPF_GET_STACK => {
            let mem_size_pairs = get_mem_size_pairs(helper);
            let size_reg = mem_size_pairs[0].size_reg;
            let (_, hi) = get_interval_i64(&state.dbm, size_reg);
            println!("Size reg {} bound: {}", size_reg.name(), hi);
            assume_le_imm(&mut state.dbm, Reg::R0, hi);
            assume_ge_imm(&mut state.dbm, Reg::R0, -constants::MAX_ERRNO);
        }
        _ => {}
    }
}

fn allowed_while_in_active_lock(helper: u32) -> bool {
    match helper {
        constants::BPF_GET_PRANDOM_U32 => false,
        _ => true,
    }
}

/// Transfer function for relative Call (BPF-to-BPF function call) instructions.
pub(crate) fn transfer_call_rel(
    env: &mut VerifierEnv,
    mut state: State,
    target: usize,
) -> Vec<State> {
    let pc = state.pc;
    info!(
        "[Verifier] pc {}: current call depth = {}",
        pc,
        state.num_frames()
    );
    if state.num_frames() >= 8 {
        env.fail(VerificationError::MaxCallDepthExceeded { pc });
        return vec![];
    }

    state.push_frame(pc + 1);
    update_call_rel_types(&mut state);
    state.pc = target;

    vec![state]
}

fn check_and_handle_spin_lock(env: &mut VerifierEnv, state: &mut State, helper: u32) -> bool {
    let pc = state.pc;
    match state.types.get(Reg::R1) {
        RegType::PtrToMapValue {
            offset: _,
            map_idx,
            id,
        } => match env.ctx.map_defs.get(map_idx) {
            Some(map_def) => {
                if let Some(val_type_id) = map_def.btf_val_type_id {
                    if helper == constants::BPF_SPIN_LOCK {
                        if state.has_active_lock() {
                            env.fail(VerificationError::LockAlreadyHeld { pc });
                            return false;
                        }
                        let special_fields = env.ctx.btf.find_special_fields(val_type_id);
                        let lock_offset_op = special_fields
                            .iter()
                            .find(|f| f.kind == SpecialFieldKind::SpinLock)
                            .map(|f| f.offset);
                        if lock_offset_op.is_none() {
                            env.fail(VerificationError::InvalidBtfType);
                            return false;
                        } else {
                            let lock_offset = lock_offset_op.unwrap();
                            state.acquire_lock(id, lock_offset);
                        }
                    } else {
                        if !state.has_active_lock() {
                            env.fail(VerificationError::LockNotHeld { pc });
                            return false;
                        } else {
                            let lock = state.get_active_lock().unwrap();
                            if lock.ptr_id != id {
                                env.fail(VerificationError::LockNotHeld { pc });
                                return false;
                            }
                        }
                        state.release_lock();
                    }
                } else {
                    env.fail(VerificationError::InvalidBtfType);
                    return false;
                }
            }
            _ => {
                env.fail(VerificationError::MapNotFound { pc, map_idx });
                return false;
            }
        },
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return false;
        }
    }
    return true;
}
