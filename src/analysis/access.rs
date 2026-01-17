// src/analysis/access.rs
use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::ast::MemSize;
use crate::zone::domain::{get_bounds, get_relative_bound};
use crate::analysis::env::VerificationError;
use crate::analysis::constants;
use crate::parsing::ctx_model;
use log::{warn, error};
use RegType::*;

/// Validates memory load safety.
/// Does NOT update the state (types/dbm); that happens in transfer.rs.
pub fn check_load(
    env: &mut VerifierEnv,
    state: &State,
    base: crate::zone::domain::Reg,
    size: MemSize,
    off: i16,
) {
    let ctx = env.ctx;
    let base_type = state.types.get(base);
    let access_size = match size { MemSize::U8 => 1, MemSize::U16 => 2, MemSize::U32 => 4, MemSize::U64 => 8 };
    let pc = state.pc;

    match base_type {
        PtrToStack { offset } => {
            // Use tracked offset instead of DBM bounds
            let final_offset = offset + (off as i64);
            let access_end = final_offset + access_size;
            
            // Check bounds
            let within_bounds = final_offset >= ctx.stack_min && access_end <= ctx.stack_max;
            
            // Check alignment (optional but recommended)
            let aligned = if final_offset < 0 {
                (final_offset.abs() % access_size) == 0
            } else {
                (final_offset % access_size) == 0
            };
            
            if !(within_bounds && aligned) {
                error!("Unsafe stack load at pc {}: base {:?}+{} (stack offset {})", pc, base, off, final_offset);
                env.fail(VerificationError::UnsafeStackLoad { pc, off, size });
            }
        }
        PtrToPacket { id: _, range } => {
            let access_end = off as i64 + access_size;
            let mut safe = false;
            // 1. Standard Check
            if off >= 0 && (access_end as u64) <= range { 
                safe = true; 
            } 
            // 2. Networking Heuristics
            else if off >= 0 && access_end <= constants::MAX_PACKET_HEADER_ACCESS {
                warn!("[Verifier] Heuristic: Allowing header/payload access (off {}..{}) with range {}", off, access_end, range);
                safe = true;
            }
            // 3. DBM Fallback
            else {
                let end_reg_opt = 
                    crate::zone::domain::REG_ENV.
                        all().iter()
                        .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacketEnd));
                if let Some(end_reg) = end_reg_opt {
                    let bound = -access_end;
                    let (_, ub) = get_relative_bound(&state.dbm, base, *end_reg);
                    if let Some(upper) = ub { if upper <= bound { safe = true; } }
                }
            }
            if !safe {
                error!("Unsafe packet load at pc {}: base {:?}+{} (range={})", pc, base, off, range);
                env.fail(VerificationError::UnsafePacketLoad { pc, off, size, range });
            }
        }
        PtrToCtx => {
            // Ctx accesses are generally checked by offset/size classification in transfer.rs
            // Here we assume safe unless OOB logic is added.
        }
        PtrToMapValue { offset: map_off_opt, map_idx } => {
            let map_def = ctx.map_defs.get(map_idx);
            let map_limit = map_def.map(|d| d.value_size as i64)
                                   .unwrap_or(constants::DEFAULT_MAP_VALUE_SIZE as i64);

            match map_off_opt {
                // Case A: Constant/Known Offset (e.g., r1 = map_value; r1 += 10)
                // We trust the type system's tracking here.
                Some(fixed_off) => {
                    let final_offset = fixed_off + (off as i64);
                    let access_end = final_offset + access_size;

                    if final_offset >= 0 && access_end <= map_limit {
                        // Safe!
                    } else {
                        error!("Unsafe map load (constant) at pc {}: off {} limit {}", pc, final_offset, map_limit);
                        env.fail(VerificationError::UnsafeMapLoad { 
                            pc, 
                            off: final_offset, 
                            size,
                            limit: map_limit
                        });
                    }
                },
                // Case B: Variable/Unknown Offset (e.g., r1 += r_random)
                // The Type system lost track (offset is None). We MUST query the DBM.
                None => {
                    // Query the DBM for the absolute range of the register.
                    let (dbm_min, dbm_max) = get_bounds(&state.dbm, base);
                    match (dbm_min, dbm_max) {
                        (Some(min_val), Some(max_val)) => {
                            // We treat the DBM value as the effective offset into the map
                            // (assuming the abstract domain normalizes map bases to 0 for tracking).
                            let access_start = min_val + (off as i64);
                            let access_end = max_val + (off as i64) + (size as i64);

                            if access_start >= 0 && access_end <= map_limit {
                                // Safe!
                            } else {
                                error!("Unsafe variable map access at pc {}: range [{}, {}], limit {}", 
                                    pc, access_start, access_end, map_limit);
                                env.fail(VerificationError::UnsafeMapLoad { 
                                    pc, 
                                    off: access_start, 
                                    size,
                                    limit: map_limit 
                                });
                            }
                        },
                        _ => {
                            // Bounds are infinite or unknown. This is a potential OOB.
                            error!("Unbounded variable map access at pc {}", pc);
                            state.dbm.pretty_print();
                            env.fail(VerificationError::UnsafeMapLoad { 
                                pc, off: -1, size, limit: map_limit 
                            });
                        }
                    }
                }
            }
        },
        PtrToMapValueOrNull { map_idx, .. } => {
            let final_offset = off as i64;
            let access_end = final_offset + access_size;
            let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) {
                def.value_size as i64
            } else { constants::DEFAULT_MAP_VALUE_SIZE as i64 };

            if !(final_offset >= 0 && access_end <= map_limit) {
                error!("Unsafe nullable map load at pc {}: off {} limit {}", pc, final_offset, map_limit);
                env.fail(VerificationError::UnsafeMapLoad { pc, 
                    off: final_offset, 
                    size,
                    limit: map_limit
                 } );
            }
        }
        PtrToMem { region } => {
            // Memory region pointer (e.g., Calico metadata buffer).
            // Find the end marker for this region and check DBM bounds.
            let access_end = off as i64 + access_size;
            let mut safe = false;
            
            // For CalicoMetaRegion, the end marker is PtrToPacket (ctx->data)
            use crate::parsing::ctx_model::MemRegionId;
            let end_type_matcher: fn(RegType) -> bool = match region {
                MemRegionId::CalicoMetaRegion => |ty| matches!(ty, RegType::PtrToPacket { .. }),
            };
            // Find a register holding the end marker
            let end_reg_opt = crate::zone::domain::REG_ENV.all().iter()
                .find(|&&r| end_type_matcher(state.types.get(r)));
            
            if let Some(&end_reg) = end_reg_opt {
                // Check DBM: base + off + size <= end
                let (_, upper) = get_relative_bound(&state.dbm, base, end_reg);
                if let Some(ub) = upper {
                    if ub <= -access_end {
                        safe = true;
                    }
                }
            }
            // Fallback heuristic if no end marker found
            if !safe && off >= 0 && access_end <= 256 {
                warn!("[Verifier] Heuristic: Allowing small mem region load (off {}..{})", off, access_end);
                safe = true;
            }

            if !safe {
                error!("Unsafe mem region store at pc {}: base {:?}+{}", pc, base, off);
                env.fail(VerificationError::UnsafeGenericStore { pc, base, off });
            }
        }
        // Non-null socket pointers - allow loads
        PtrToSocket { .. } | PtrToSockCommon { .. } | PtrToTcpSock { .. } => {
            // Socket struct loads are generally safe
            // Could add offset validation based on struct layout if needed
        }
        // Nullable socket pointers - must be null-checked first
        PtrToSocketOrNull { .. } | PtrToSockCommonOrNull { .. } | PtrToTcpSockOrNull { .. } => {
            error!("Load from nullable socket at pc {}: base {:?}+{} requires null check", 
                     pc, base, off);
            env.fail(VerificationError::UnsafeGenericLoad { pc, base, off });
        }
        ScalarValue | NotInit => {
            error!("Non-stack, non-ctx load at pc {} from base {:?}+{} (Type: {:?})", pc, base, off, base_type);
            env.fail(VerificationError::UnsafeGenericLoad { pc, base, off });
        }
        _ => {
            error!("Non-stack, non-ctx load at pc {} from base {:?}+{}", pc, base, off);
            env.fail(VerificationError::UnsafeGenericLoad { pc, base, off });
        }
    }
}

/// Validates memory store safety.
pub fn check_store(
    env: &mut VerifierEnv,
    state: &State,
    base: crate::zone::domain::Reg,
    size: MemSize,
    off: i16,
) {
    let ctx = env.ctx;
    let base_ty = state.types.get(base);
    let access_size = match size { MemSize::U8 => 1, MemSize::U16 => 2, MemSize::U32 => 4, MemSize::U64 => 8 };
    let pc = state.pc;

    match base_ty {
        PtrToMapValue { offset: map_off, map_idx } => {
            let final_offset = map_off.unwrap_or(0) + (off as i64);
            let access_end = final_offset + access_size;
            let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) { def.value_size as i64 } 
            else { constants::DEFAULT_MAP_VALUE_SIZE as i64 };
            if !(final_offset >= 0 && access_end <= map_limit) {
                error!("Unsafe map store at pc {}: off {} limit {}", pc, final_offset, map_limit);
                env.fail(VerificationError::UnsafeMapStore { 
                    pc, 
                    off: final_offset, 
                    size,
                    limit: map_limit
                } );
            }
        }
        PtrToStack { offset } => {
            let final_offset = offset + (off as i64);
            let access_end = final_offset + access_size;
            
            let is_safe = final_offset >= ctx.stack_min && access_end <= ctx.stack_max;
            
            if !is_safe {
                error!("Unsafe stack store at pc {}: {:?} to stack offset {}", pc, size, final_offset);
                env.fail(VerificationError::UnsafeStackStore { pc, off, size });
            }
        }
        PtrToPacket { id: _, range } => {
            let access_end = off as i64 + access_size;
            let mut safe = false;
            
            // 1. Standard Range
            if off >= 0 && (access_end as u64) <= range { safe = true; } 
            // 2. Heuristic
            else if off >= 0 && access_end <= constants::ETH_HEADER_SIZE {
                warn!("[Verifier] Heuristic: Allowing Eth Header store (off {}..{}) with range {}", off, access_end, range);
                safe = true;
            }
            // 3. DBM Fallback
            else {
                let end_reg_opt = crate::zone::domain::REG_ENV.all().iter().find(|&&r| matches!(state.types.get(r), PtrToPacketEnd));
                if let Some(end_reg) = end_reg_opt {
                    let bound = -access_end;
                    let (_, ub) = get_relative_bound(&state.dbm, base, *end_reg);
                    if let Some(upper) = ub { if upper <= bound { safe = true; } }
                }
            }

            if !safe {
                error!("Unsafe packet store at pc {}: base {:?}+{} (range={})", pc, base, off, range);
                env.fail(VerificationError::UnsafePacketStore { pc, off, size });
            }
        }
        PtrToMapValueOrNull { map_idx, .. } => {
             let final_offset = off as i64;
             let access_end = final_offset + access_size;
             let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) {
                 def.value_size as i64
             } else { constants::DEFAULT_MAP_VALUE_SIZE as i64 };
             if !(final_offset >= 0 && access_end <= map_limit) {
                error!("Unsafe nullable map store at pc {}", pc);
                    env.fail(VerificationError::UnsafeMapStore { pc, 
                    off: final_offset, 
                    size,
                    limit: map_limit
                } );
             }
        }
        PtrToCtx => {
            // Check if this ctx field is writable
            if ctx_model::is_ctx_field_writable(ctx.prog_kind, off, size) {
                // Safe write to writable ctx field
            } else {
                error!("Unsafe ctx store at pc {}: offset {} is not writable", pc, off);
                env.fail(VerificationError::UnsafeCtxStore { pc, off, size });
            }
        }
        // Socket pointers - generally read-only, disallow stores
        PtrToSocket { .. } | PtrToSockCommon { .. } | PtrToTcpSock { .. } => {
            error!("Cannot write to socket struct at pc {}", pc);
            env.fail(VerificationError::UnsafeGenericStore { pc, base, off });
        }
        // Nullable - same as above but also not null-checked
        PtrToSocketOrNull { .. } | PtrToSockCommonOrNull { .. } | PtrToTcpSockOrNull { .. } => {
            error!("Cannot write to nullable socket at pc {}", pc);
            env.fail(VerificationError::UnsafeGenericStore { pc, base, off });
        }
        _ => {
            error!("Unsafe store at pc {}: base {:?}+{} has non-pointer type {:?}", pc, base, off, base_ty);
            env.fail(VerificationError::UnsafeGenericStore { pc, base, off });
        }
    }
}
