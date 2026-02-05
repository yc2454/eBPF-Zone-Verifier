// src/analysis/access.rs
use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::RegType;
use crate::ast::{ProgramKind};
use crate::parsing::elf_loader::BpfMapDef;
use crate::zone::domain::{get_bounds, get_relative_bound};
use crate::analysis::machine::env::VerificationError;
use crate::common::constants;
use crate::common::ctx_model;
use log::{error};
use RegType::*;
use crate::zone::domain::{Reg, REG_ENV};

/// Validates memory load safety.
/// Does NOT update the state (types/dbm); that happens in transfer.rs.
pub fn check_load(
    env: &mut VerifierEnv,
    state: &State,
    base: crate::zone::domain::Reg,
    size: i64,
    off: i16,
) {
    let ctx = env.ctx;
    let base_type = state.types.get(base);
    let pc = state.pc;

    match base_type {
        PtrToStack { offset, frame_level } => {
            check_stack_access(env, state, base, offset, off as i64, size, pc, AccessKind::Read, frame_level);
        }
        PtrToPacket { id: _, is_base: _ } => {
            check_packet_access(env, state, base, off, size, pc, AccessKind::Read);
        }
        PtrToCtx => {
            if !ctx_model::is_valid_ctx_read(ctx.prog_kind, off, size) {
                error!("Unsafe ctx load at pc {}: offset {} is not readable", pc, off);
                env.fail(VerificationError::UnsafeCtxAccess { pc, off, size });
            }
        }
        PtrToMapValue { id: _, offset: map_off_opt, map_idx } => {
            if let Some(map_def) = ctx.map_defs.get(map_idx) {
                // If the map is write-only
                if map_def.map_flags == constants::BPF_F_WRONLY_PROG {
                    error!("Map load is forbidden!");
                    env.fail(VerificationError::MapLoadForbidden { pc, map_idx });
                }
                let map_limit = map_def.value_size as i64;
                check_map_access(env, state, map_limit, map_off_opt, map_idx, base, map_def, off, size, pc);
            } else {
                error!("Map not found!");
                env.fail(VerificationError::MapNotFound { pc, map_idx })
            }
        },
        PtrToMapValueOrNull { map_idx, .. } => {
            let final_offset = off as i64;
            let access_end = final_offset + size;
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
            let access_end = off as i64 + size;
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
            if !is_valid_socket_access(&base_type, off as i64, size) {
                error!(
                    "Invalid socket access at pc {}: {:?} offset {} size {}", 
                    pc, base_type, off, size
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
        PtrToPacketMeta => {
            // Find a register pointing to packet data (data pointer)
            let reg_pointing_to_packet_data = 
                REG_ENV
                    .all()
                    .iter()
                    .find(|&&r| 
                        matches!(state.types.get(r), RegType::PtrToPacket { is_base: true, .. }));
            
            if let Some(&data_reg) = reg_pointing_to_packet_data {
                // We need to prove: data_meta + off + size <= data
                // Equivalently: (data_meta - data) <= -(off + size)
                // So check: upper_bound(base - data_reg) + off + size <= 0
                
                let (_, ub_opt) = get_relative_bound(&state.dbm, base, data_reg);
                let access_end = off as i64 + size as i64;
                
                match ub_opt {
                    Some(ub) if ub + access_end <= 0 => {
                        // Safe: proven that access is within metadata region
                    }
                    Some(ub) => {
                        error!("Metadata access exceeds proven bounds (need {}, have {})", access_end, -ub);
                        env.fail(VerificationError::UnsafePacketLoad { pc, off, size });
                    }
                    None => {
                        error!("No bounds check performed between data_meta and data");
                        env.fail(VerificationError::UnsafePacketLoad { pc, off, size });
                    }
                }
            } else {
                error!("Packet data pointer not found");
                env.fail(VerificationError::InvalidRegisterTypeState { pc });
            }
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
    size: i64,
    off: i16,
) {
    let ctx = env.ctx;
    let base_ty = state.types.get(base);
    let pc = state.pc;

    match base_ty {
        PtrToMapValue { id: _, offset: map_off, map_idx } => {
            if let Some(map_def) = ctx.map_defs.get(map_idx) {
                // If the map is read-only
                if map_def.map_flags == constants::BPF_F_RDONLY_PROG {
                    error!("Map store is forbidden!");
                    env.fail(VerificationError::MapStoreForbidden { pc, map_idx });
                }
                let map_limit = map_def.value_size as i64;
                check_map_access(env, state, map_limit, map_off, map_idx, base, map_def, off, size, pc);
            } else {
                error!("Map not found!");
                env.fail(VerificationError::MapNotFound { pc, map_idx })
            }
        }
        PtrToStack { offset, frame_level } => {
            check_stack_access(env, state, base, offset, off as i64, size as i64, pc, AccessKind::Write, frame_level);
        }
        PtrToPacket { id: _, is_base: _ } => {
            check_packet_access(env, state, base, off, size, pc, AccessKind::Write);
        }
        PtrToMapValueOrNull { map_idx, .. } => {
            error!("Unsafe nullable map store at pc {}", pc);
            env.fail(VerificationError::UnsafeMapStore { pc, 
                off: off as i64, 
                size,
                limit: env.ctx.map_defs.get(map_idx).unwrap().value_size as i64
            });
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
#[derive(Debug, Clone, Copy)]
pub enum AccessKind {
    Read,
    Write,
    HelperOutput
}

/// Check if a stack access at (base + off) of size bytes is safe.
/// For reads, also checks that the memory is initialized.
pub fn check_stack_access(
    env: &mut VerifierEnv,
    state: &State,
    base: Reg,
    ptr_type_offset: Option<i64>,
    instruction_offset: i64,
    size: i64,
    pc: usize,
    kind: AccessKind,
    pointer_frame_lv: usize
) {
    if state.current_frame_level() > pointer_frame_lv {
        env.fail(VerificationError::SpillToCaller { pc });
        return;
    }
    // The frame depth is stored as a positive number (e.g., 300 means R10-300)
    let current_frame_depth = -(state.total_stack_depth() as i64);

    match ptr_type_offset {
        Some(base_off) => {
            let actual_offset = base_off + instruction_offset;
            let access_end = current_frame_depth + actual_offset + size;

            // Alignment check
            if actual_offset % size != 0 {
                env.fail(VerificationError::MisalignedAccess { pc, off: actual_offset });
                return;
            }
            
            // Bounds check
            if actual_offset < constants::BPF_STACK_MIN || access_end > constants::BPF_STACK_MAX {
                error!(target: "app", "Stack access out of bounds at pc {}: off {} size {} (Known offset)", pc, actual_offset, size);
                env.fail(VerificationError::StackOutOfBounds { pc, off: actual_offset, size });
                return;
            }
            
            // Initialization and read size check (reads only)
            check_stack_initialization(env, state, kind, actual_offset, size, pc);
        }
        None => {
            // Unknown offset case - bounds check via DBM
            let (lo, hi) = get_relative_bound(&state.dbm, base, Reg::R10);
            
            let safe = match (lo, hi) {
                (Some(lower), Some(upper)) => {
                    let min_offset = lower + instruction_offset;
                    let max_access_end = current_frame_depth as i64 + upper + instruction_offset + size;
                    min_offset >= constants::BPF_STACK_MIN && max_access_end <= constants::BPF_STACK_MAX
                }
                _ => false,
            };
            
            if !safe {
                error!(target: "app", "Stack access out of bounds at pc {}: off {} size {} (Unknown offset)", pc, instruction_offset, size);
                env.fail(VerificationError::StackOutOfBounds { pc, off: instruction_offset, size });
                return;
            }
            
            // Initialization check with unknown offset - must be conservative
            match (lo, hi) {
                (Some(lower), Some(upper)) => {
                    for off_candidate in lower..=upper {
                        let actual_offset = off_candidate + instruction_offset;
                        check_stack_initialization(env, state, kind, actual_offset, size, pc);
                    }
                }
                _ => {
                    env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
                }
            }
        }
    }
}

fn check_stack_initialization(
    env: &mut VerifierEnv,
    state: &State,
    kind: AccessKind,
    actual_offset: i64,
    size: i64,
    pc: usize,
) {
    // Initialization check (for reads and helper outputs)
    match kind {
        AccessKind::Read => {
            // ALL bytes must be initialized
            for i in 0..size {
                let slot = (actual_offset + i) as i16;
                if !state.stack.is_slot_initialized(slot) {
                    env.fail(VerificationError::UninitializedStackRead { pc, offset: actual_offset });
                    return;
                }
                // The read size for a pointer must be 64-bit
                let slot_type = state.stack.get_slot_type(slot);
                if slot_type.is_pointer() && size != 8 {
                    error!(target: "app", "Pointer read with invalid size at pc {}: off {} size {}", pc, actual_offset, size);
                    env.fail(VerificationError::InvalidStackRead { pc, offset: actual_offset });
                }
            }
        }
        AccessKind::HelperOutput => {
            // At least ONE byte must be initialized (stack slot was "claimed")
            let any_initialized = (0..size)
                .any(|i| state.stack.is_slot_initialized((actual_offset + i) as i16));
            
            if !any_initialized {
                env.fail(VerificationError::UninitializedStackRead { pc, offset: actual_offset });
                return;
            }
        }
        AccessKind::Write => {
            // No initialization check needed
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
        state.current_frame_level()
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

// ------------------- Packet Checking Helpers -------------------

/// Check if a packet access is properly aligned.
/// 
/// Packet data starts at 2-byte alignment (NET_IP_ALIGN).
/// Returns true if ALL possible offsets are properly aligned for the access size.
pub fn check_packet_alignment(
    state: &State,
    base: Reg,
    off: i16,
    size: i64,
) -> bool {
    // U8 is always aligned
    if size == 1 {
        return true;
    }
    
    // Get offset bounds relative to packet start
    let (min_off, max_off) = get_packet_offset_range(state, base, off);
    
    match (min_off, max_off) {
        (Some(lo), Some(hi)) => {
            // Packet base is 2-byte aligned
            const NET_IP_ALIGN: i64 = 2;
            
            // Check if all offsets in range have same alignment class
            // AND that alignment is correct for access size
            let lo_aligned = (NET_IP_ALIGN + lo) % size == 0;
            let hi_aligned = (NET_IP_ALIGN + hi) % size == 0;
            
            // If range spans different alignment classes, reject
            if lo % size != hi % size {
                return false;
            }
            
            lo_aligned && hi_aligned
        }
        _ => false, // Unbounded offset, can't verify alignment
    }
}

/// Get the range of possible offsets from packet start.
fn get_packet_offset_range(
    state: &State,
    base: Reg,
    insn_off: i16,
) -> (Option<i64>, Option<i64>) {
    let base_type = state.types.get(base);
    
    match base_type {
        RegType::PtrToPacket { .. } => {
            // Fixed offset tracked in type
            let insn_off = insn_off as i64;
            (Some(insn_off), Some(insn_off))
        }
        _ => {
            // Variable offset - query DBM for bounds relative to packet start
            // Find packet start register
            let pkt_start_reg = crate::zone::domain::REG_ENV
                .all()
                .iter()
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacket { is_base: true, .. }));
            
            if let Some(&start_reg) = pkt_start_reg {
                let (lo, hi) = get_relative_bound(&state.dbm, base, start_reg);
                (
                    lo.map(|l| l + insn_off as i64),
                    hi.map(|h| h + insn_off as i64),
                )
            } else {
                (None, None)
            }
        }
    }
}

fn prog_kind_support_direct_packet_write(prog_kind: ProgramKind) -> bool {
    match prog_kind {
        ProgramKind::LwtIn | ProgramKind::LwtOut => false,
        _ => true,
    }
}

fn check_packet_access(
    env: &mut VerifierEnv,
    state: &State,
    base: Reg,
    off: i16,
    size: i64,
    pc: usize,
    kind: AccessKind
) {
    // 0. Check if the program type allows direct packet writes
    if matches!(kind, AccessKind::Write) && !prog_kind_support_direct_packet_write(env.ctx.prog_kind) {
        error!("Direct packet store at pc {} is not supported for {:?} program", pc, env.ctx.prog_kind);
        env.fail(VerificationError::IllegalPacketStore { pc, off, size });
        return;
    }
    // 1. Locate the Packet Start and Packet End registers
    // (Ideally, 'base' should know which packet_id it belongs to, 
    // avoiding this global search)
    let start_reg_opt = REG_ENV.all().iter()
        .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacket { is_base: true, .. }));

    let end_reg_opt = REG_ENV.all().iter()
        .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacketEnd));

    // 2. Perform START Check (Underflow Protection)
    // Rule: Base + Off >= Start  -->  Base - Start >= -Off
    let mut start_safe = false;
    if let Some(start_reg) = start_reg_opt {
        // We need the Lower bound (Minimum distance) to be safe
        if let (Some(lower), _) = get_relative_bound(&state.dbm, base, *start_reg) {
            // Debug: println!("Start Check: {} >= {}", lower, -off);
            if lower >= -(off as i64) {
                start_safe = true;
            }
        }
    }

    // 3. Perform END Check (Overflow Protection)
    // Rule: Base + Off + Size <= End  -->  Base - End <= -(Off + Size)
    let mut end_safe = false;
    if let Some(end_reg) = end_reg_opt {
        // We need the Upper bound (Maximum distance) to be safe
        if let (_, Some(upper)) = get_relative_bound(&state.dbm, base, *end_reg) {
            let limit = -(off as i64 + size);
            // Debug: println!("End Check: {} <= {}", upper, limit);
            if upper <= limit {
                end_safe = true;
            }
        }
    }

    // 4. Final Verdict
    if !(start_safe && end_safe) {
        if matches!(kind, AccessKind::Read) {
            env.fail(VerificationError::UnsafePacketLoad { pc, off, size });
        } else {
            env.fail(VerificationError::UnsafePacketStore { pc, off, size });
        }
        return;
    }

    // 5. Alignment check
    if !env.ctx.has_flag(constants::F_NEEDS_EFFICIENT_UNALIGNED_ACCESS) 
       && !check_packet_alignment(state, base, off, size) 
    {
        env.fail(VerificationError::MisalignedPacketAccess { pc, off, size });
        return;
    }
}

// ------------------- Map Checking Helpers -------------------
fn check_btf_fields_access(
    env: &mut VerifierEnv,
    pc: usize,
    final_offset: i64,
    access_end: i64,
    size: i64,
    map_limit: i64,
    btf_id: u32,
) {
    let btf_fields = env.ctx.btf.find_special_fields(btf_id);
    for field in btf_fields {
        let field_end = field.offset + field.size;
        
        if final_offset < field_end.into() && access_end > field.offset.into() {
            error!("Cannot access BTF field");
            env.fail(VerificationError::UnsafeMapLoad { 
                pc, 
                off: final_offset, 
                size,
                limit: map_limit
            });
        }
    }
}

pub fn check_map_access(
    env: &mut VerifierEnv,
    state: &State,
    map_limit: i64,
    map_off_opt: Option<i64>,
    map_idx: usize,
    base: Reg,
    map_def: &BpfMapDef,
    insn_off: i16,
    size: i64,
    pc: usize,
) {
    match map_off_opt {
        // Case A: Constant/Known Offset (e.g., r1 = map_value; r1 += 10)
        // We trust the type system's tracking here.
        Some(fixed_off) => {
            let final_offset = fixed_off + (insn_off as i64);
            let access_end = final_offset + size;

            if let Some(btf_id) = map_def.btf_val_type_id {
                check_btf_fields_access(env, pc, final_offset, access_end, size, map_limit, btf_id);
                return;
            }

            if final_offset >= 0 && access_end <= map_limit {
                // Safe!
            } else {
                error!("Unsafe map access at pc {}: off {} limit {}", pc, final_offset, map_limit);
                env.fail(VerificationError::UnsafeMapAccess { 
                    pc, 
                    size,
                    map_idx
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
                    let access_start = min_val + (insn_off as i64);
                    let access_end = max_val + (insn_off as i64) + (size as i64);

                    if let Some(btf_id) = map_def.btf_val_type_id {
                        check_btf_fields_access(env, pc, insn_off.into(), access_end, size, map_limit, btf_id);
                        return;
                    }

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
}

pub fn check_map_rw(
    env: &mut VerifierEnv,
    map_idx: usize,
    pc: usize,
    is_write: bool
) {
    let flag_to_check = if is_write {
        constants::BPF_F_RDONLY_PROG
    } else {
        constants::BPF_F_WRONLY_PROG
    };
    let ctx = env.ctx;
    if let Some(map_def) = ctx.map_defs.get(map_idx) {
        // If the map is write-only
        if map_def.map_flags == flag_to_check {
            error!("Map read is forbidden!");
            env.fail(VerificationError::MapLoadForbidden { pc, map_idx });
        }
    } else {
        error!("Map not found!");
        env.fail(VerificationError::MapNotFound { pc, map_idx })
    }
}
