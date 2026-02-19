// src/analysis/transfer/call/checks.rs

use crate::analysis::machine::env::{VerificationError, VerifierEnv};
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::analysis::transfer::memory::access::{self, AccessKind};
use crate::analysis::transfer::memory::{
    check_map_access, check_map_rw, check_packet_access, check_stack_access,
    check_stack_arg_readable, check_stack_no_pointers,
};
use crate::common::constants;
use crate::zone::domain::{
    get_distance_fixed, get_distance_interval, get_interval, proven_nonnegative, proven_positive,
    proven_zero,
};
use log::{error, info, warn};

use super::signatures::{
    BpfArgType, get_helper_signature, get_mem_size_pairs, get_nullable_ptr_size_pair,
    helper_rejects_packet_for_arg,
};

/// Information about a BPF map needed for validation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct MapInfo {
    pub(crate) key_size: u32,
    pub(crate) value_size: u32,
}

pub(crate) fn get_map_info(map_type: RegType, env: &VerifierEnv) -> Option<MapInfo> {
    match map_type {
        RegType::PtrToMapObject { map_idx } => env.ctx.map_defs.get(map_idx).map(|md| MapInfo {
            key_size: md.key_size,
            value_size: md.value_size,
        }),
        _ => None,
    }
}

/// Validates all arguments for a helper function based on its signature.
pub(crate) fn validate_helper_args(
    env: &mut VerifierEnv,
    state: &State,
    helper: u32,
    types: &TypeState,
    pc: usize,
) {
    let Some(sig) = get_helper_signature(helper) else {
        warn!(
            "[Verifier] Unknown helper {} at pc {}, skipping arg validation",
            helper, pc
        );
        return;
    };

    // Get map info if first arg is a map (needed for key/value size validation)
    let map_info = if sig.args[0] == BpfArgType::ConstMapPtr {
        get_map_info(types.get(Reg::R1), env)
    } else {
        None
    };

    // Validate each argument
    let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];

    for (i, (&arg_type, &reg)) in sig.args.iter().zip(arg_regs.iter()).enumerate() {
        info!(
            "[Verifier] pc {}: validating arg R{} as {:?}",
            pc,
            i + 1,
            arg_type
        );
        if arg_type == BpfArgType::DontCare {
            break; // No more arguments
        }

        let reg_type = types.get(reg);

        if !validate_single_arg(
            env, state, types, helper, pc, reg, arg_type, reg_type, &map_info, i,
        ) {
            // Validation failed, error already reported
            return;
        }
    }
}

/// Validates a single argument against its expected type.
/// Returns true if valid, false if invalid (error already reported).
pub(crate) fn validate_single_arg(
    env: &mut VerifierEnv,
    state: &State,
    types: &TypeState,
    helper: u32,
    pc: usize,
    reg: Reg,
    expected: BpfArgType,
    actual: RegType,
    map_info: &Option<MapInfo>,
    arg_index: usize,
) -> bool {
    match expected {
        BpfArgType::DontCare => true,

        // ---- Map pointer ----
        BpfArgType::ConstMapPtr => {
            let is_inner_map_ptr = match actual {
                RegType::PtrToMapValue {
                    map_idx,
                    offset: Some(0),
                    ..
                } => env
                    .ctx
                    .map_defs
                    .get(map_idx)
                    .map(|m| {
                        matches!(
                            m.type_,
                            constants::BPF_MAP_TYPE_ARRAY_OF_MAPS
                                | constants::BPF_MAP_TYPE_HASH_OF_MAPS
                        )
                    })
                    .unwrap_or(false),
                _ => false,
            };

            if !matches!(actual, RegType::PtrToMapObject { .. }) && !is_inner_map_ptr {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_MAP, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            // There are special requirements for bpf_map_lookup_elem
            else if helper == constants::BPF_MAP_LOOKUP_ELEM {
                match actual {
                    RegType::PtrToMapObject { map_idx } => {
                        let map_def = env.ctx.map_defs.get(map_idx);
                        if map_def.is_none() {
                            env.fail(VerificationError::InvalidArgType { pc, reg });
                            return false;
                        } else {
                            let map_def = map_def.unwrap();
                            if matches!(
                                map_def.type_,
                                constants::BPF_MAP_TYPE_STACK_TRACE
                                    | constants::BPF_MAP_TYPE_PROG_ARRAY
                                    | constants::BPF_MAP_TYPE_SK_STORAGE
                            ) {
                                env.fail(VerificationError::InvalidArgType { pc, reg });
                                return false;
                            }
                        }
                    }
                    _ => return true,
                }
            } else if helper == constants::BPF_TAIL_CALL {
                if let RegType::PtrToMapObject { map_idx } = actual {
                    if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                        if map_def.type_ != constants::BPF_MAP_TYPE_PROG_ARRAY {
                            env.fail(VerificationError::InvalidArgType { pc, reg });
                            error!(
                                "[Verifier] pc {}: bpf_tail_call requires PROG_ARRAY map, got type {}",
                                pc, map_def.type_
                            );
                            return false;
                        }
                    }
                }
            } else if helper == constants::BPF_PERF_EVENT_OUTPUT {
                if let RegType::PtrToMapObject { map_idx } = actual {
                    if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                        if map_def.type_ != constants::BPF_MAP_TYPE_PERF_EVENT_ARRAY {
                            env.fail(VerificationError::InvalidArgType { pc, reg });
                            error!(
                                "[Verifier] pc {}: bpf_perf_event_output requires PERF_EVENT_ARRAY map, got type {}",
                                pc, map_def.type_
                            );
                            return false;
                        }
                    }
                }
            }
            true
        }

        // ---- Map key pointer ----
        BpfArgType::PtrToMapKey => {
            let Some(target_info) = map_info else {
                return true;
            };

            if let RegType::PtrToMapValue { map_idx, .. } = actual {
                if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                    println!(
                        "Validating map value size: expected {}, got {}",
                        target_info.value_size, map_def.value_size
                    );
                    if map_def.value_size != target_info.value_size {
                        env.fail(VerificationError::InvalidArgType { pc, reg });
                        error!(
                            "[Verifier] pc {}: R{} map value size mismatch: expected {}, got {}",
                            pc,
                            arg_index + 1,
                            target_info.value_size,
                            map_def.key_size
                        );
                        return false;
                    }
                } else {
                    env.fail(VerificationError::MapNotFound { pc, map_idx });
                    return false;
                }
            }

            // For stack pointers used as keys in bpf_map_update_elem, check that
            // the memory doesn't contain pointers that would be leaked to the map.
            // Note: bpf_map_lookup_elem only reads the key for comparison, so it's
            // okay to have pointers in the key for lookup operations.
            if helper == constants::BPF_MAP_UPDATE_ELEM {
                if let RegType::PtrToStack { .. } = actual {
                    if let Some(off) = get_distance_fixed(&state.dbm, reg, Reg::R10) {
                        check_stack_no_pointers(
                            env,
                            state,
                            off,
                            target_info.key_size as i64,
                            pc,
                        );
                        if env.failed() {
                            return false;
                        }
                    }
                }
            }

            validate_readable_mem(env, state, pc, reg, actual, Some(target_info.key_size))
        }

        // ---- Map value pointer ----
        BpfArgType::PtrToMapValue => {
            let Some(target_info) = map_info else {
                return true;
            };

            if !matches!(
                actual,
                RegType::PtrToMapValue { .. }
                    | RegType::PtrToStack { .. }
                    | RegType::PtrToPacket
                    | RegType::PtrToPacketMeta
            ) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_MAP_VALUE, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }

            if let RegType::PtrToMapValue { map_idx, .. } = actual {
                if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                    if map_def.value_size != target_info.value_size {
                        env.fail(VerificationError::InvalidArgType { pc, reg });
                        error!(
                            "[Verifier] pc {}: R{} map value size mismatch: expected {}, got {}",
                            pc,
                            arg_index + 1,
                            target_info.value_size,
                            map_def.value_size
                        );
                        return false;
                    }
                } else {
                    env.fail(VerificationError::MapNotFound { pc, map_idx });
                    return false;
                }
            }

            // For stack pointers, check that the memory doesn't contain pointers
            // that would be leaked to the map
            if let RegType::PtrToStack { .. } = actual {
                if let Some(off) = get_distance_fixed(&state.dbm, reg, Reg::R10) {
                    check_stack_no_pointers(
                        env,
                        state,
                        off,
                        target_info.value_size as i64,
                        pc,
                    );
                    if env.failed() {
                        return false;
                    }
                }
            }

            validate_readable_mem(env, state, pc, reg, actual, Some(target_info.value_size))
        }

        BpfArgType::PtrToMapValueOrNull => {
            let reg_type = types.get(reg);
            if reg_type.is_scalar() && proven_zero(&state.dbm, reg) {
                return true;
            } else {
                if !matches!(
                    reg_type,
                    RegType::PtrToMapValue { .. }
                        | RegType::PtrToMapValueOrNull { .. }
                        | RegType::PtrToStack { .. }
                        | RegType::PtrToPacket { .. }
                        | RegType::PtrToPacketMeta { .. }
                ) {
                    env.fail(VerificationError::InvalidArgType { pc, reg });
                    error!(
                        "[Verifier] pc {}: R{} expected PTR_TO_MAP_VALUE or NULL, got {:?}",
                        pc,
                        arg_index + 1,
                        actual
                    );
                    return false;
                }
                true
            }
        }

        // ---- Uninitialized map value (output buffer) ----
        BpfArgType::PtrToUninitMapValue => {
            let Some(info) = map_info else {
                return true;
            };
            validate_writable_mem(env, state, types, pc, reg, actual, Some(info.value_size))
        }

        // ---- Generic memory pointer ----
        BpfArgType::PtrToMem => {
            if checked_by_mem_size_pairs(helper, reg) {
                return true;
            }
            // Some helpers reject packet pointers for specific args
            if matches!(actual, RegType::PtrToPacket { .. })
                && helper_rejects_packet_for_arg(helper, arg_index)
            {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: helper {} does not accept packet pointer for R{}",
                    pc,
                    helper,
                    arg_index + 1
                );
                return false;
            }
            validate_readable_mem(env, state, pc, reg, actual, None)
        }

        // ---- Uninitialized memory (output buffer) ----
        BpfArgType::PtrToUninitMem => {
            validate_writable_mem(env, state, types, pc, reg, actual, None)
        }

        // ---- Allocated memory (by bpf_ringbuf_reserve for example) ----
        BpfArgType::PtrToAllocMem => {
            if !matches!(actual, RegType::PtrToAllocMem { .. }) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                return false;
            }
            true
        }

        // ---- Size arguments ----
        BpfArgType::ConstSize => {
            // Must be positive
            if !proven_positive(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} (ConstSize) must be positive",
                    pc,
                    arg_index + 1
                );
                return false;
            }
            true
        }

        BpfArgType::ConstSizeOrZero | BpfArgType::ConstAllocSizeOrZero => {
            // Can be zero or positive
            if !proven_nonnegative(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} (ConstSizeOrZero) must be non-negative",
                    pc,
                    arg_index + 1
                );
                return false;
            }
            true
        }

        // ---- Context pointer ----
        BpfArgType::PtrToCtx => {
            if !matches!(actual, RegType::PtrToCtx) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_CTX, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        // ---- Context pointer or NULL ----
        BpfArgType::PtrToCtxOrNull => {
            if state.types.get(reg).is_scalar() && proven_zero(&state.dbm, reg) {
                return true;
            }
            if !matches!(actual, RegType::PtrToCtx) && !proven_zero(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_CTX or NULL, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        // ---- Any initialized value ----
        BpfArgType::Anything => {
            // Just needs to be readable (not uninitialized)
            // The check_regs_readable at the start of transfer_call handles this
            true
        }

        // ---- Socket types ----
        BpfArgType::PtrToSocket => {
            if !matches!(
                actual,
                RegType::PtrToSocket { .. }
                    | RegType::PtrToSockCommon { .. }
                    | RegType::PtrToStack { .. }
            ) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_SOCKET, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        BpfArgType::PtrToSockCommon => {
            if !matches!(
                actual,
                RegType::PtrToSockCommon { .. }
                    | RegType::PtrToSocket { .. }
                    | RegType::PtrToTcpSock { .. }
            ) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_SOCK_COMMON, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        BpfArgType::PtrToBTFIdSockCommon => {
            if !matches!(
                actual,
                RegType::PtrToSockCommon { .. }
                    | RegType::PtrToSocket { .. }
                    | RegType::PtrToTcpSock { .. }
            ) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_BTF_ID_SOCK_COMMON, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        // ---- BTF ID pointer ----
        BpfArgType::PtrToBtfId => {
            if !matches!(actual, RegType::PtrToBtfId { .. }) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_BTF_ID, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        // ---- Stack pointer ----
        BpfArgType::PtrToStack => {
            if !matches!(actual, RegType::PtrToStack { .. }) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_STACK, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        BpfArgType::PtrToStackOrNull => {
            if state.types.get(reg).is_scalar() && proven_zero(&state.dbm, reg) {
                return true;
            }
            if !matches!(actual, RegType::PtrToStack { .. }) && !proven_zero(&state.dbm, reg) {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_STACK or NULL, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                return false;
            }
            true
        }

        BpfArgType::PtrToMemOrNull => {
            if state.types.get(reg).is_scalar() && proven_zero(&state.dbm, reg) {
                return true;
            }
            if state.types.get(reg).is_nullable() {
                // Pointer is NULL - check that paired size arg is also 0
                if let Some(size_arg_idx) = get_nullable_ptr_size_pair(helper, arg_index) {
                    let size_reg = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5][size_arg_idx];
                    if !proven_zero(&state.dbm, size_reg) {
                        env.fail(VerificationError::InvalidArgType { pc, reg: size_reg });
                        error!(
                            "[Verifier] pc {}: R{} must be 0 when R{} is NULL",
                            pc,
                            size_arg_idx + 1,
                            arg_index + 1
                        );
                        return false;
                    }
                }
                return validate_readable_mem(env, state, pc, reg, actual, None);
            }
            validate_readable_mem(env, state, pc, reg, actual, None)
        }

        BpfArgType::PtrToLong => {
            if let RegType::PtrToStack { frame_level } = actual {
                let offset = get_distance_fixed(&state.dbm, reg, Reg::R10);
                check_stack_access(
                    env,
                    state,
                    reg,
                    offset,
                    0,
                    8, // PtrToLong is 8-byte access
                    pc,
                    AccessKind::HelperPrimitive,
                    None,
                    frame_level,
                );
                !env.failed()
            } else {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: R{} expected PTR_TO_LONG, got {:?}",
                    pc,
                    arg_index + 1,
                    actual
                );
                false
            }
        }
    }
}

/// Validates that a register points to readable memory.
pub(crate) fn validate_readable_mem(
    env: &mut VerifierEnv,
    state: &State,
    pc: usize,
    reg: Reg,
    reg_type: RegType,
    size: Option<u32>,
) -> bool {
    match reg_type {
        RegType::PtrToStack { .. } => {
            if let Some(off) = get_distance_fixed(&state.dbm, reg, Reg::R10) {
                if let Some(sz) = size {
                    check_stack_arg_readable(
                        env,
                        state,
                        off,
                        sz as i64,
                        pc,
                        AccessKind::HelperBuffer,
                    );
                }
                true
            } else {
                // Variable stack offset — use bounds check
                if let Some(sz) = size {
                    let (lo, hi) = get_distance_interval(&state.dbm, reg, Reg::R10);
                    match (lo, hi) {
                        (Some(l), Some(h)) => {
                            // Check all possible offsets in the range
                            for off_candidate in l..=h {
                                check_stack_arg_readable(
                                    env,
                                    state,
                                    off_candidate,
                                    sz as i64,
                                    pc,
                                    AccessKind::HelperBuffer,
                                );
                                if env.failed() {
                                    return false;
                                }
                            }
                            true
                        }
                        _ => {
                            env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
                            false
                        }
                    }
                } else {
                    true
                }
            }
        }
        // Delegate the checking for these to access.rs
        RegType::PtrToMapValue { map_idx, .. } => {
            if let Some(size) = size {
                access::check_load(env, state, reg, size as i64, 0);
                if env.failed() {
                    return false;
                }
                true
            } else {
                check_map_rw(env, map_idx, pc, false);
                if env.failed() {
                    return false;
                }
                true
            }
        }
        RegType::PtrToPacket { .. } => {
            if let Some(size) = size {
                access::check_load(env, state, reg, size as i64, 0);
                if env.failed() {
                    return false;
                }
                true
            } else {
                true
            }
        }
        RegType::PtrToCtx => {
            // Context can be read
            true
        }
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!("[Verifier] pc {}: {:?} not a valid memory pointer", pc, reg);
            false
        }
    }
}

/// Validates that a register points to writable memory.
pub(crate) fn validate_writable_mem(
    env: &mut VerifierEnv,
    state: &State,
    _types: &TypeState,
    pc: usize,
    reg: Reg,
    reg_type: RegType,
    size: Option<u32>,
) -> bool {
    match reg_type {
        RegType::PtrToStack { frame_level } => {
            if let Some(off) = get_distance_fixed(&state.dbm, reg, Reg::R10) {
                if let Some(sz) = size {
                    check_stack_access(
                        env,
                        state,
                        reg,
                        Some(off),
                        0,
                        sz as i64,
                        pc,
                        AccessKind::HelperBuffer,
                        None,
                        frame_level,
                    );
                }
            }
            true
        }
        RegType::PtrToMapValue { map_idx, .. } => {
            let writable = env
                .ctx
                .map_defs
                .get(map_idx)
                .map(|md| md.map_flags != constants::BPF_F_RDONLY_PROG)
                .unwrap_or(false);
            if writable {
                true
            } else {
                env.fail(VerificationError::MapStoreForbidden { pc, map_idx });
                false
            }
        }
        RegType::PtrToPacket { .. } => {
            // Packet pointers are NOT valid for uninit_mem arguments
            // (helper would write to packet, which is not allowed this way)
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!(
                "[Verifier] pc {}: packet pointer not valid for output buffer",
                pc
            );
            false
        }
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!(
                "[Verifier] pc {}: {:?} not a valid writable memory pointer",
                pc, reg
            );
            false
        }
    }
}

/// Validates all pointer-size pairs for a helper call.
/// Returns true if all pairs are valid, false otherwise (error reported).
pub(crate) fn check_mem_size_pairs(
    env: &mut VerifierEnv,
    state: &State,
    helper: u32,
    pc: usize,
) -> bool {
    let pairs = get_mem_size_pairs(helper);

    for pair in pairs {
        if !check_single_mem_size_pair(env, helper, state, pair, pc) {
            return false;
        }
    }

    true
}

/// Validates a single pointer-size pair.
pub(crate) fn check_single_mem_size_pair(
    env: &mut VerifierEnv,
    helper: u32,
    state: &State,
    pair: &super::signatures::MemSizePair,
    pc: usize,
) -> bool {
    let ptr_type = state.types.get(pair.ptr_reg);

    // Handle NULL pointer case
    if proven_zero(&state.dbm, pair.ptr_reg) {
        if pair.allow_zero {
            // NULL ptr is OK, but size must also be 0
            if !proven_zero(&state.dbm, pair.size_reg) {
                env.fail(VerificationError::InvalidArgType {
                    pc,
                    reg: pair.size_reg,
                });
                error!(
                    "[Verifier] pc {}: {:?} must be 0 when {:?} is NULL",
                    pc, pair.size_reg, pair.ptr_reg
                );
                return false;
            }
            return true;
        } else {
            // NULL not allowed for this pair
            env.fail(VerificationError::InvalidArgType {
                pc,
                reg: pair.ptr_reg,
            });
            error!("[Verifier] pc {}: {:?} cannot be NULL", pc, pair.ptr_reg);
            return false;
        }
    }

    // Get size bounds from DBM
    let (_, Some(max_size)) = get_interval(&state.dbm, pair.size_reg) else {
        // Size is unbounded - reject
        env.fail(VerificationError::InvalidArgType {
            pc,
            reg: pair.size_reg,
        });
        error!(
            "[Verifier] pc {}: {:?} has unbounded size",
            pc, pair.size_reg
        );
        return false;
    };

    // Size must be non-negative
    if !proven_nonnegative(&state.dbm, pair.size_reg) {
        env.fail(VerificationError::InvalidArgType {
            pc,
            reg: pair.size_reg,
        });
        error!(
            "[Verifier] pc {}: {:?} must be non-negative",
            pc, pair.size_reg
        );
        return false;
    }

    // Check zero size
    if max_size == 0 {
        if pair.allow_zero {
            return true;
        } else {
            env.fail(VerificationError::InvalidArgType {
                pc,
                reg: pair.size_reg,
            });
            error!("[Verifier] pc {}: {:?} cannot be 0", pc, pair.size_reg);
            return false;
        }
    }
    // Validate pointer can accommodate the access
    let sig = get_helper_signature(helper).unwrap();
    let ptr_arg_type = sig.args.get(pair.ptr_reg.idx() - 2).unwrap();
    check_ptr_access_size(
        env,
        state,
        pair.ptr_reg,
        ptr_type,
        *ptr_arg_type,
        max_size as u32,
        pc,
    )
}

pub(crate) fn checked_by_mem_size_pairs(helper: u32, reg: Reg) -> bool {
    let pairs = get_mem_size_pairs(helper);

    for pair in pairs {
        if pair.ptr_reg == reg {
            return true;
        }
    }

    false
}

/// Checks that a pointer can safely access `size` bytes.
pub(crate) fn check_ptr_access_size(
    env: &mut VerifierEnv,
    state: &State,
    ptr_reg: Reg,
    ptr_type: RegType,
    ptr_arg_type: BpfArgType,
    size: u32,
    pc: usize,
) -> bool {
    match ptr_type {
        RegType::PtrToStack { .. } => {
            if let Some(off) = get_distance_fixed(&state.dbm, ptr_reg, Reg::R10) {
                // Stack: check [off, off + size) is within stack bounds
                // Stack grows down, so valid range is [-512, 0)
                let end_offset = off + size as i64;
                if off < -512 || end_offset > 0 {
                    env.fail(VerificationError::StackOutOfBounds {
                        pc,
                        off,
                        size: size.into(),
                    });
                    error!(
                        "[Verifier] pc {}: stack access [{}, {}) out of bounds",
                        pc, off, end_offset
                    );
                    return false;
                }
                // Also check stack slots are initialized for reads
                if !matches!(ptr_arg_type, BpfArgType::PtrToUninitMem) {
                    check_stack_arg_readable(
                        env,
                        state,
                        off,
                        size as i64,
                        pc,
                        AccessKind::HelperBuffer,
                    );
                }
                !env.failed()
            } else {
                // Variable offset — use bounds for range check
                let (lo, hi) = get_distance_interval(&state.dbm, ptr_reg, Reg::R10);
                match (lo, hi) {
                    (Some(l), Some(h)) => {
                        let end_offset = h + size as i64;
                        if l < -512 || end_offset > 0 {
                            env.fail(VerificationError::StackOutOfBounds {
                                pc,
                                off: l,
                                size: size.into(),
                            });
                            return false;
                        }
                        if !matches!(ptr_arg_type, BpfArgType::PtrToUninitMem) {
                            for off_candidate in l..=h {
                                check_stack_arg_readable(
                                    env,
                                    state,
                                    off_candidate,
                                    size as i64,
                                    pc,
                                    AccessKind::HelperBuffer,
                                );
                                if env.failed() {
                                    return false;
                                }
                            }
                        }
                        true
                    }
                    _ => {
                        env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
                        error!(
                            "[Verifier] pc {}: {:?} has unknown stack offset",
                            pc, ptr_reg
                        );
                        false
                    }
                }
            }
        }

        RegType::PtrToMapValue {
            map_idx,
            offset,
            id: _,
        } => {
            // Map value: check offset + size <= value_size
            let Some(map_def) = env.ctx.map_defs.get(map_idx) else {
                env.fail(VerificationError::MapNotFound { pc, map_idx });
                return false;
            };

            check_map_access(
                env,
                state,
                map_def.value_size as i64,
                offset,
                map_idx,
                ptr_reg,
                map_def,
                0,
                size as i64,
                pc,
            );
            !env.failed()
        }

        RegType::PtrToPacket { .. } => {
            // Packet: need to verify against packet bounds (data_end - data)
            // This requires range analysis between packet_data and packet_end
            // access::check_load(env, state, ptr_reg, size as i64, 0);
            check_packet_access(
                env,
                state,
                ptr_reg,
                0,
                size as i64,
                pc,
                AccessKind::HelperBuffer,
            );
            !env.failed()
        }

        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
            error!(
                "[Verifier] pc {}: {:?} ({:?}) not a valid memory pointer",
                pc, ptr_reg, ptr_type
            );
            false
        }
    }
}
