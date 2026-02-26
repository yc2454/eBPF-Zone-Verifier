// src/analysis/transfer/memory/access.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::common::constants;
use crate::common::ctx_model;
use crate::common::mem_region_model;
use crate::domains::domain::get_distance_fixed;
use RegType::*;
use log::error;

use super::map::check_map_access;
use super::packet::{check_packet_access, check_packet_meta_access};
use super::stack::check_stack_access;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessKind {
    Read,
    Write,
    HelperBuffer,
    HelperPrimitive,
}

/// Validates memory load safety.
pub fn check_load(env: &mut VerifierEnv, state: &State, base: Reg, size: i64, off: i16) {
    let ctx = env.ctx;
    let base_type = state.types.get(base);
    let pc = state.pc;

    match base_type {
        PtrToStack { frame_level } => {
            let offset = get_distance_fixed(state.dbm(), base, Reg::R10);
            check_stack_access(
                env,
                state,
                base,
                offset,
                off as i64,
                size,
                pc,
                AccessKind::Read,
                None,
                frame_level,
            );
        }
        PtrToPacket => {
            check_packet_access(env, state, base, off, size, pc, AccessKind::Read);
        }
        PtrToCtx => {
            if !ctx_model::is_valid_ctx_read(env, off, size) {
                error!(
                    "Unsafe ctx load at pc {}: offset {} is not readable",
                    pc, off
                );
                env.fail(VerificationError::UnsafeCtxAccess { pc, off, size });
            }
        }
        PtrToMapValue {
            id: _,
            offset: map_off_opt,
            map_idx,
        } => {
            if let Some(map_def) = ctx.map_defs.get(map_idx) {
                if map_def.map_flags == constants::BPF_F_WRONLY_PROG {
                    error!("Map load is forbidden!");
                    env.fail(VerificationError::MapLoadForbidden { pc, map_idx });
                }
                let map_limit = map_def.value_size as i64;
                check_map_access(
                    env,
                    state,
                    map_limit,
                    map_off_opt,
                    map_idx,
                    base,
                    map_def,
                    off,
                    size,
                    pc,
                );
            } else {
                error!("Map not found!");
                env.fail(VerificationError::MapNotFound { pc, map_idx })
            }
        }
        PtrToMapValueOrNull { map_idx, .. } => {
            let final_offset = off as i64;
            let access_end = final_offset + size;
            let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) {
                def.value_size as i64
            } else {
                constants::DEFAULT_MAP_VALUE_SIZE
            };

            if !(final_offset >= 0 && access_end <= map_limit) {
                error!(
                    "Unsafe nullable map load at pc {}: off {} limit {}",
                    pc, final_offset, map_limit
                );
                env.fail(VerificationError::UnsafeMapLoad {
                    pc,
                    off: final_offset,
                    size,
                    limit: map_limit,
                });
            }
        }
        PtrToTcpSock { .. } | PtrToSockCommon { .. } | PtrToSocket { .. } => {
            if !mem_region_model::is_valid_mem_region_read(state.types.get(base), off, size) {
                error!(
                    "Invalid socket access at pc {}: {:?} offset {} size {}",
                    pc, base_type, off, size
                );
                env.fail(VerificationError::UnsafeSocketAccess { pc, off, size });
            }
        }
        PtrToSocketOrNull { .. } | PtrToSockCommonOrNull { .. } | PtrToTcpSockOrNull { .. } => {
            error!(
                "Load from nullable socket at pc {}: base {:?}+{} requires null check",
                pc, base, off
            );
            env.fail(VerificationError::UnsafeGenericLoad {
                pc,
                base,
                off,
                base_type,
            });
        }
        PtrToPacketMeta => {
            check_packet_meta_access(env, state, base, off, size, pc);
        }
        PtrToBtfId { .. } | PtrToMapObject { .. } => {
            if !mem_region_model::is_valid_mem_region_read(state.types.get(base), off, size) {
                error!(
                    "Invalid socket access at pc {}: {:?} offset {} size {}",
                    pc, base_type, off, size
                );
                env.fail(VerificationError::UnsafeSocketAccess { pc, off, size });
            }
        }
        ScalarValue | NotInit => {
            error!(
                "Non-stack, non-ctx load at pc {} from base {:?}+{} (Type: {:?})",
                pc, base, off, base_type
            );
            env.fail(VerificationError::UnsafeGenericLoad {
                pc,
                base,
                off,
                base_type,
            });
        }
        _ => {
            error!(
                "Non-stack, non-ctx load at pc {} from base {:?}+{}",
                pc, base, off
            );
            env.fail(VerificationError::UnsafeGenericLoad {
                pc,
                base,
                off,
                base_type,
            });
        }
    }
}

/// Validates memory store safety.
pub fn check_store(
    env: &mut VerifierEnv,
    state: &State,
    base: Reg,
    size: i64,
    off: i16,
    src_type: RegType,
) {
    let ctx = env.ctx;
    let base_ty = state.types.get(base);
    let pc = state.pc;

    match base_ty {
        PtrToMapValue {
            id: _,
            offset: map_off,
            map_idx,
        } => {
            if let Some(map_def) = ctx.map_defs.get(map_idx) {
                if map_def.map_flags == constants::BPF_F_RDONLY_PROG {
                    error!("Map store is forbidden!");
                    env.fail(VerificationError::MapStoreForbidden { pc, map_idx });
                }
                let map_limit = map_def.value_size as i64;
                check_map_access(
                    env, state, map_limit, map_off, map_idx, base, map_def, off, size, pc,
                );
            } else {
                error!("Map not found!");
                env.fail(VerificationError::MapNotFound { pc, map_idx })
            }
        }
        PtrToStack { frame_level } => {
            let offset = get_distance_fixed(state.dbm(), base, Reg::R10);
            check_stack_access(
                env,
                state,
                base,
                offset,
                off as i64,
                size,
                pc,
                AccessKind::Write,
                Some(src_type),
                frame_level,
            );
        }
        PtrToPacket => {
            check_packet_access(env, state, base, off, size, pc, AccessKind::Write);
        }
        PtrToPacketMeta => {
            check_packet_meta_access(env, state, base, off, size, pc);
        }
        PtrToMapValueOrNull { map_idx, .. } => {
            error!("Unsafe nullable map store at pc {}", pc);
            env.fail(VerificationError::UnsafeMapStore {
                pc,
                off: off as i64,
                size,
                limit: env.ctx.map_defs.get(map_idx).unwrap().value_size as i64,
            });
        }
        PtrToCtx => {
            if !ctx_model::is_valid_ctx_write(env, off, size) {
                error!(
                    "Unsafe ctx store at pc {}: offset {} is not writable",
                    pc, off
                );
                env.fail(VerificationError::UnsafeCtxAccess { pc, off, size });
            }
        }
        PtrToSocket { .. } | PtrToSockCommon { .. } | PtrToTcpSock { .. } => {
            error!("Cannot write to socket struct at pc {}", pc);
            env.fail(VerificationError::UnsafeGenericStore {
                pc,
                base,
                off,
                base_type: base_ty,
            });
        }
        PtrToSocketOrNull { .. } | PtrToSockCommonOrNull { .. } | PtrToTcpSockOrNull { .. } => {
            error!("Cannot write to nullable socket at pc {}", pc);
            env.fail(VerificationError::UnsafeGenericStore {
                pc,
                base,
                off,
                base_type: base_ty,
            });
        }
        PtrToAllocMem { id: _, mem_size } => {
            let access_end = off as i64 + size;
            if access_end > mem_size as i64 {
                error!(
                    "Unsafe memory store at pc {}: base {:?}+{} size {} exceeds allocated memory size {}",
                    pc, base, off, size, mem_size
                );
                env.fail(VerificationError::UnsafeMemoryStore {
                    pc,
                    base,
                    off,
                    size,
                });
            }
        }
        _ => {
            error!(
                "Unsafe store at pc {}: base {:?}+{} has non-pointer type {:?}",
                pc, base, off, base_ty
            );
            env.fail(VerificationError::UnsafeGenericStore {
                pc,
                base,
                off,
                base_type: base_ty,
            });
        }
    }
}
