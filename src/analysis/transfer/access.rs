// src/analysis/access.rs
use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::ast::MemSize;
use crate::zone::domain::{get_bounds, get_relative_bound};
use crate::analysis::env::VerificationError;
use crate::common::constants;
use crate::analysis::ctx_model;
use log::{error, info};
use RegType::*;
use crate::zone::domain::Reg;

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
            check_stack_access(env, state, base, offset, off as i64, access_size, pc, AccessKind::Read);
        }
        PtrToPacket { id: _, range, is_base: _, off: off_from_packet } => {
            // Total offset from base = off + instruction offset
            let total_off = off_from_packet + off as i64;
            let access_end = total_off + access_size;
            let mut safe = false;
            
            // 1. Negative offset is never allowed (can't go before packet start)
            if total_off < 0 {
                error!("Negative packet load at pc {}: base {:?}+{}", pc, base, total_off);
                env.fail(VerificationError::UnsafePacketLoad { pc, off: total_off as i16, size, range });
                return;
            }
            // 2. Standard Check: within pre-computed safe range
            else if (access_end as u64) <= range { 
                safe = true; 
            } 
            // 3. Direct DBM query (handles cases where range wasn't propagated)
            else {
                let end_reg_opt = 
                    crate::zone::domain::REG_ENV
                        .all().iter()
                        .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacketEnd));
                if let Some(end_reg) = end_reg_opt {
                    // Need: base + access_end <= data_end
                    // i.e.: base - data_end <= -access_end
                    let required_bound = -access_end;
                    let (_, ub) = get_relative_bound(&state.dbm, base, *end_reg);
                    if let Some(upper) = ub { 
                        if upper <= required_bound { 
                            safe = true; 
                        } 
                    }
                }
            }
            if !safe {
                error!("Unsafe packet load at pc {}: base {:?}+{} (range={})", pc, base, off, range);
                env.fail(VerificationError::UnsafePacketLoad { pc, off, size, range });
            }
        }
        PtrToCtx => {
            if !ctx_model::is_valid_ctx_read(ctx.prog_kind, off, size) {
                error!("Unsafe ctx load at pc {}: offset {} is not readable", pc, off);
                env.fail(VerificationError::UnsafeCtxAccess { pc, off, size });
            }
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
        PtrToMem { region, range } => {
            let access_end = off as i64 + access_size;
            let mut safe = false;
            
            if off < 0 {
                // Negative offset never allowed
            } 
            // Standard check using pre-computed range
            else if (access_end as u64) <= range {
                safe = true;
            }
            // Fallback: direct DBM query
            else {
                let end_type_matcher: fn(&RegType) -> bool = match region {
                    ctx_model::MemRegionId::CalicoMetaRegion => {
                        |ty| matches!(ty, RegType::PtrToPacket { is_base: true, .. })
                    }
                };
                
                let end_reg_opt = crate::zone::domain::REG_ENV.all().iter()
                    .find(|&&r| end_type_matcher(&state.types.get(r)));

                if let Some(&end_reg) = end_reg_opt {
                    let required_bound = -access_end;
                    let (_, upper) = get_relative_bound(&state.dbm, base, end_reg);
                    if let Some(ub) = upper {
                        if ub <= required_bound {
                            safe = true;
                        }
                    }
                }
            }
            
            if !safe {
                error!("Unsafe mem region load at pc {}: base {:?}+{} (range={})", pc, base, off, range);
                env.fail(VerificationError::UnsafeMemoryRegionLoad { pc, base, off });
            }
        }
        RegType::PtrToSocket {..} | RegType::PtrToSockCommon {..} | RegType::PtrToTcpSock {..} => {
            if !is_valid_socket_access(&base_type, off as i64, access_size) {
                error!(
                    "Invalid socket access at pc {}: {:?} offset {} size {}", 
                    pc, base_type, off, access_size
                );
                env.fail(VerificationError::UnsafeSocketAccess { pc, off, size });
            }
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
            let map_limit = 
                if let Some(def) = ctx.map_defs.get(map_idx) { def.value_size as i64 } 
                else { constants::DEFAULT_MAP_VALUE_SIZE as i64 };
            if let Some(fixed_off) = map_off {
                let final_offset = fixed_off + (off as i64);
                let access_end = final_offset + access_size;
                if !(final_offset >= 0 && access_end <= map_limit) {
                    error!("Unsafe map store (constant) at pc {}: off {} limit {}", pc, final_offset, map_limit);
                    env.fail(VerificationError::UnsafeMapStore { 
                        pc, 
                        off: final_offset, 
                        size,
                        limit: map_limit
                    } );
                }
            } else {
                // Variable/unknown offset - use DBM to check
                let (dbm_min, dbm_max) = get_bounds(&state.dbm, base);
                match (dbm_min, dbm_max) {
                    (Some(min_val), Some(max_val)) => {
                        let access_start = min_val + (off as i64);
                        let access_end = max_val + (off as i64) + (size as i64);
                        if !(access_start >= 0 && access_end <= map_limit) {
                            error!("Unsafe variable map store at pc {}: range [{}, {}], limit {}", 
                                pc, access_start, access_end, map_limit);
                            env.fail(VerificationError::UnsafeMapStore { 
                                pc, 
                                off: access_start, 
                                size,
                                limit: map_limit
                            } );
                        }
                    },
                    _ => {
                        error!("Unbounded variable map store at pc {}", pc);
                        state.dbm.pretty_print();
                        env.fail(VerificationError::UnsafeMapStore { 
                            pc, off: -1, size, limit: map_limit 
                        });
                    }
                }
            }
        }
        PtrToStack { offset } => {
            info!("Checking stack store");
            check_stack_access(env, state, base, offset, off as i64, access_size as i64, pc, AccessKind::Write);
        }
        PtrToPacket { id: _, range, is_base: _, off: off_from_packet } => {
            // Total offset from base = off + instruction offset
            let total_off = off_from_packet + off as i64;
            let access_end = total_off + access_size;
            let mut safe = false;
            
            if total_off < 0 {
                error!("Negative packet store at pc {}: base {:?}+{}", pc, base, total_off);
                env.fail(VerificationError::UnsafePacketStore { pc, off: total_off as i16, size });
                return;
            } else if (access_end as u64) <= range {
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
            if !ctx_model::is_valid_ctx_write(ctx.prog_kind, off, size) {
                error!("Unsafe ctx store at pc {}: offset {} is not writable", pc, off);
                env.fail(VerificationError::UnsafeCtxAccess { pc, off, size });
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

// ---------------------- Stack checking helper ------------------- //
pub enum AccessKind {
    Read,
    Write,
}

/// Check if a stack access at (base + off) of size bytes is safe.
/// For reads, also checks that the memory is initialized.
fn check_stack_access(
    env: &mut VerifierEnv,
    state: &State,
    base: Reg,
    ptr_type_offset: Option<i64>,
    instruction_offset: i64,
    size: i64,
    pc: usize,
    kind: AccessKind,
) {
    match ptr_type_offset {
        Some(base_off) => {
            let actual_offset = base_off + instruction_offset;
            let access_end = actual_offset + size;

            // Alignment check
            if actual_offset % size != 0 {
                env.fail(VerificationError::MisalignedAccess { pc, off: actual_offset });
                return;
            }
            
            // Bounds check
            if actual_offset < constants::BPF_STACK_MIN || access_end > constants::BPF_STACK_MAX {
                env.fail(VerificationError::StackOutOfBounds { pc, off: instruction_offset, size });
                return;
            }
            
            // Initialization and read size check (reads only)
            if matches!(kind, AccessKind::Read) {
                // For the access range
                for i in 0..size {
                    let slot = (actual_offset + i) as i16;
                    if !state.types.stack.contains_key(&slot) {
                        env.fail(VerificationError::UninitializedStackRead { pc, offset: actual_offset });
                        return;
                    }
                    // The read size for a pointer must be 64-bit
                    let slot_type = state.types.get_stack(actual_offset as i16);
                    if slot_type.is_pointer() {
                        if size != 8 {
                            env.fail(VerificationError::InvalidStackRead { pc, offset: actual_offset });
                        }
                    }
                }
            }
        }
        None => {
            // Unknown offset case - bounds check via DBM
            let (lo, hi) = get_relative_bound(&state.dbm, base, Reg::R10);
            
            let safe = match (lo, hi) {
                (Some(lower), Some(upper)) => {
                    let min_offset = lower + instruction_offset;
                    let max_access_end = upper + instruction_offset + size;
                    min_offset >= constants::BPF_STACK_MIN && max_access_end <= constants::BPF_STACK_MAX
                }
                _ => false,
            };
            
            if !safe {
                env.fail(VerificationError::StackOutOfBounds { pc, off: instruction_offset, size });
                return;
            }
            
            // Initialization check with unknown offset - must be conservative
            if matches!(kind, AccessKind::Read) {
                // Need ALL possible slots to be initialized
                match (lo, hi) {
                    (Some(lower), Some(upper)) => {
                        for off_candidate in lower..=upper {
                            for i in 0..size {
                                let slot = (off_candidate + instruction_offset + i) as i16;
                                if !state.types.stack.contains_key(&slot) {
                                    env.fail(VerificationError::UninitializedStackRead { pc, offset: instruction_offset });
                                    return;
                                }
                            }
                        }
                    }
                    _ => {
                        env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
                    }
                }
            }
        }
    }
}

/// Check that a stack region is readable (for helper arguments)
pub fn check_stack_arg_readable(
    env: &mut VerifierEnv,
    state: &State,
    stack_offset: i64,  // already resolved offset from R10
    size: i64,
    pc: usize,
) {
    // For helper args, offset is already known (R10 + some constant)
    check_stack_access(
        env, state, Reg::R10,
        Some(stack_offset),
        0,  // no additional instruction offset
        size,
        pc,
        AccessKind::Read,
    )
}

// ---------------------- Socket checking helper ------------------ //

/// A field in a BPF-visible socket struct
struct SocketField {
    offset: u32,
    size: u32,
}

/// struct bpf_sock fields (v5.15)
/// Full socket info, returned by bpf_sk_fullsock()
const BPF_SOCK_FIELDS: &[SocketField] = &[
    SocketField { offset: 0, size: 4 },   // bound_dev_if
    SocketField { offset: 4, size: 4 },   // family
    SocketField { offset: 8, size: 4 },   // type
    SocketField { offset: 12, size: 4 },  // protocol
    SocketField { offset: 16, size: 4 },  // mark
    SocketField { offset: 20, size: 4 },  // priority
    SocketField { offset: 24, size: 4 },  // src_ip4
    SocketField { offset: 28, size: 4 },  // src_ip6[0]
    SocketField { offset: 32, size: 4 },  // src_ip6[1]
    SocketField { offset: 36, size: 4 },  // src_ip6[2]
    SocketField { offset: 40, size: 4 },  // src_ip6[3]
    SocketField { offset: 44, size: 4 },  // src_port
    SocketField { offset: 48, size: 4 },  // dst_port
    SocketField { offset: 52, size: 4 },  // dst_ip4
    SocketField { offset: 56, size: 4 },  // dst_ip6[0]
    SocketField { offset: 60, size: 4 },  // dst_ip6[1]
    SocketField { offset: 64, size: 4 },  // dst_ip6[2]
    SocketField { offset: 68, size: 4 },  // dst_ip6[3]
    SocketField { offset: 72, size: 4 },  // state
    SocketField { offset: 76, size: 4 },  // rx_queue_mapping
];

/// struct bpf_tcp_sock fields (v5.15)
/// TCP-specific info, returned by bpf_tcp_sock()
const BPF_TCP_SOCK_FIELDS: &[SocketField] = &[
    SocketField { offset: 0, size: 4 },   // snd_cwnd
    SocketField { offset: 4, size: 4 },   // srtt_us
    SocketField { offset: 8, size: 4 },   // rtt_min
    SocketField { offset: 12, size: 4 },  // snd_ssthresh
    SocketField { offset: 16, size: 4 },  // rcv_nxt
    SocketField { offset: 20, size: 4 },  // snd_nxt
    SocketField { offset: 24, size: 4 },  // snd_una
    SocketField { offset: 28, size: 4 },  // mss_cache
    SocketField { offset: 32, size: 4 },  // ecn_flags
    SocketField { offset: 36, size: 4 },  // rate_delivered
    SocketField { offset: 40, size: 4 },  // rate_interval_us
    SocketField { offset: 44, size: 4 },  // packets_out
    SocketField { offset: 48, size: 4 },  // retrans_out
    SocketField { offset: 52, size: 4 },  // total_retrans
    SocketField { offset: 56, size: 4 },  // segs_in
    SocketField { offset: 60, size: 4 },  // data_segs_in
    SocketField { offset: 64, size: 4 },  // segs_out
    SocketField { offset: 68, size: 4 },  // data_segs_out
    SocketField { offset: 72, size: 4 },  // lost_out
    SocketField { offset: 76, size: 4 },  // sacked_out
    SocketField { offset: 80, size: 8 },  // bytes_received (u64)
    SocketField { offset: 88, size: 8 },  // bytes_acked (u64)
    SocketField { offset: 96, size: 4 },  // dsack_dups
    SocketField { offset: 100, size: 4 }, // delivered
    SocketField { offset: 104, size: 4 }, // delivered_ce
    SocketField { offset: 108, size: 4 }, // icsk_retransmits
];

/// struct bpf_sock_common fields (v5.15)
/// Limited socket info from skb->sk without full socket lock
const BPF_SOCK_COMMON_FIELDS: &[SocketField] = &[
    SocketField { offset: 0, size: 4 },   // family
    SocketField { offset: 4, size: 4 },   // src_ip4
    SocketField { offset: 8, size: 4 },   // src_ip6[0]
    SocketField { offset: 12, size: 4 },  // src_ip6[1]
    SocketField { offset: 16, size: 4 },  // src_ip6[2]
    SocketField { offset: 20, size: 4 },  // src_ip6[3]
    SocketField { offset: 24, size: 4 },  // src_port
];

/// Check if access [off, off+size) falls entirely within a valid field
fn access_within_fields(fields: &[SocketField], off: u32, size: u32) -> bool {
    fields.iter().any(|f| off >= f.offset && off + size <= f.offset + f.size)
}

/// Validates a memory access to a socket pointer.
/// Returns true if the access is valid for the given socket type.
pub fn is_valid_socket_access(ty: &RegType, off: i64, size: i64) -> bool {
    // Negative offsets never allowed
    if off < 0 || size <= 0 {
        return false;
    }
    
    let off = off as u32;
    let size = size as u32;
    
    // Check for overflow
    if off.checked_add(size).is_none() {
        return false;
    }
    
    match ty {
        RegType::PtrToSockCommon {..} => access_within_fields(BPF_SOCK_COMMON_FIELDS, off, size),
        RegType::PtrToSocket {..} => access_within_fields(BPF_SOCK_FIELDS, off, size),
        RegType::PtrToTcpSock {..} => access_within_fields(BPF_TCP_SOCK_FIELDS, off, size),
        _ => false,
    }
}
