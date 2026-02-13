// src/analysis/access.rs
use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::stack_state::StackState;
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::RegType;
use crate::ast::{ProgramKind};
use crate::parsing::elf_loader::BpfMapDef;
use crate::zone::domain::{get_bounds, get_relative_bound, get_relative_constant, check_meta_access, check_packet_access_dbm};
use crate::analysis::machine::env::VerificationError;
use crate::common::constants;
use crate::common::ctx_model;
use crate::common::mem_region_model;
use log::{error, debug};
use RegType::*;
use crate::zone::domain::{Reg};

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
        PtrToStack { frame_level } => {
            let offset = get_relative_constant(&state.dbm, base, Reg::R10);
            check_stack_access(env, state, base, offset, off as i64, size, pc, AccessKind::Read, None, frame_level);
        }
        PtrToPacket => {
            check_packet_access(env, state, base, off, size, pc, AccessKind::Read);
        }
        PtrToCtx => {
            if !ctx_model::is_valid_ctx_read(env, off, size) {
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
        PtrToTcpSock {..} | PtrToSockCommon {..} | PtrToSocket {..} => {
            if !mem_region_model::is_valid_mem_region_read(state.types.get(base), off, size) {
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
        PtrToPacketMeta { .. } => {
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
    base: Reg,
    size: i64,
    off: i16,
    src_type: RegType
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
        PtrToStack { frame_level } => {
            let offset = get_relative_constant(&state.dbm, base, Reg::R10);
            check_stack_access(
                env, state, base, offset, off as i64,
                size as i64, pc, AccessKind::Write, Some(src_type), frame_level);
        }
        PtrToPacket { .. } => {
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
            if !ctx_model::is_valid_ctx_write(env, off, size) {
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
        PtrToAllocMem { id: _, mem_size } => {
            let access_end = off as i64 + size;
            if access_end > mem_size as i64 {
                error!("Unsafe memory store at pc {}: base {:?}+{} size {} exceeds allocated memory size {}", 
                    pc, base, off, size, mem_size);
                env.fail(VerificationError::UnsafeMemoryStore { pc, base, off, size });
            }
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
    HelperOutput,
    HelperArg
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
    src_type_op: Option<RegType>,
    pointer_frame_lv: FrameLevel
) {
    if state.current_frame_level() > pointer_frame_lv {
        if let AccessKind::Write = kind && src_type_op.is_some() {
            if let Some(ty) = src_type_op {
                // Callee stack pointers become dangling after return
                if matches!(ty, RegType::PtrToStack { .. }) {
                    env.fail(VerificationError::SpillToCaller { pc });
                    return;
                }
            }
        }
    }
    // The frame depth is stored as a positive number (e.g., 300 means R10-300)
    let current_frame_depth = -(state.total_stack_depth() as i64);
    let stack_being_accessed = state.stack_at(pointer_frame_lv);

    match ptr_type_offset {
        Some(base_off) => {
            let actual_offset = base_off + instruction_offset;
            let access_end = current_frame_depth + actual_offset + size;

            // Alignment check
            if !matches!(kind, AccessKind::HelperArg) && actual_offset % size != 0 {
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
            check_stack_initialization(env, stack_being_accessed, kind, actual_offset, size, pc);
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
                        check_stack_initialization(env, stack_being_accessed, kind, actual_offset, size, pc);
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
    stack: &StackState,
    kind: AccessKind,
    actual_offset: i64,
    size: i64,
    pc: usize,
) {
    // Kernel-compatible privileged relaxation:
    // A 32-bit load from the upper half of an aligned 8-byte stack slot
    // can be accepted when the lower half is initialized. The value is
    // treated as unknown scalar later (fill_at fails to preserve spill info).
    let allow_privileged_upper_half_read = |off: i64, sz: i64| -> bool {
        if !env.ctx.is_privileged() || sz != 4 {
            return false;
        }
        if off < i16::MIN as i64 || off > i16::MAX as i64 {
            return false;
        }
        let off = off as i16;
        if off.rem_euclid(8) != 4 {
            return false;
        }
        for i in 0..4 {
            if !stack.is_slot_initialized(off - 4 + i as i16) {
                return false;
            }
        }
        true
    };

    let allow_privileged_partial_u64_read = |off: i64, sz: i64| -> bool {
        if !env.ctx.is_privileged() || sz != 8 {
            return false;
        }
        if off < i16::MIN as i64 || off > i16::MAX as i64 {
            return false;
        }
        let off = off as i16;
        // Kernel-compatible relaxed behavior in privileged mode:
        // if the base byte is initialized, allow loading a full 64-bit value.
        // The value is conservatively treated as unknown by fill_at.
        stack.is_slot_initialized(off)
    };

    // Initialization check (for reads and helper outputs)
    match kind {
        AccessKind::Read => {
            // ALL bytes must be initialized
            let mut first_uninit: Option<i16> = None;
            for i in 0..size {
                let slot = (actual_offset + i) as i16;
                if !stack.is_slot_initialized(slot) {
                    first_uninit = Some(slot);
                    break;
                }
            }

            if first_uninit.is_some() {
                if allow_privileged_upper_half_read(actual_offset, size)
                    || allow_privileged_partial_u64_read(actual_offset, size)
                {
                    return;
                }
                env.fail(VerificationError::UninitializedStackRead { pc, offset: actual_offset });
                return;
            }

            for i in 0..size {
                let slot = (actual_offset + i) as i16;
                // The read size for a pointer must be 64-bit
                let slot_type = stack.get_slot_type(slot);
                if slot_type.is_pointer() && size != 8 {
                    error!(target: "app", "Pointer read with invalid size at pc {}: off {} size {}", pc, actual_offset, size);
                    env.fail(VerificationError::InvalidStackRead { pc, offset: actual_offset });
                }
            }
        }
        AccessKind::HelperOutput | AccessKind::HelperArg => {
            // At least ONE byte must be initialized (stack slot was "claimed")
            let any_initialized = (0..size)
                .any(|i| stack.is_slot_initialized((actual_offset + i) as i16));
            
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
    kind: AccessKind
) {
    // For helper args, offset is already known (R10 + some constant)
    check_stack_access(
        env, state, Reg::R10,
        Some(stack_offset),
        0,  // no additional instruction offset
        size,
        pc,
        kind,
        None,
        state.current_frame_level(),
    )
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
                .find(|&&r| matches!(state.types.get(r), RegType::PtrToPacket));
            
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

pub fn check_packet_access(
    env: &mut VerifierEnv,
    state: &State,
    base: Reg,
    off: i16,
    size: i64,
    pc: usize,
    kind: AccessKind
) {
    if matches!(kind, AccessKind::Write) && !prog_kind_support_direct_packet_write(env.ctx.prog_kind) {
        error!("Direct packet store at pc {} is not supported for {:?} program", pc, env.ctx.prog_kind);
        env.fail(VerificationError::IllegalPacketStore { pc, off, size });
        return;
    }

    let (start_ok, end_ok) = check_packet_access_dbm(&state.dbm, base, off as i64, size as i64);
    debug!("Packet access check at pc {}: base {} offset {} size {} => start_ok {}, end_ok {}", 
        pc, base.name(), off, size, start_ok, end_ok);
    if !start_ok || !end_ok {
        if matches!(kind, AccessKind::Read) {
            env.fail(VerificationError::UnsafePacketLoad { pc, off, size });
        } else {
            env.fail(VerificationError::UnsafePacketStore { pc, off, size });
        }
    }

    if env.ctx.has_flag(constants::F_LOAD_WITH_STRICT_ALIGNMENT) 
       && !matches!(kind, AccessKind::HelperOutput | AccessKind::HelperArg) 
       && !check_packet_alignment(state, base, off, size) 
    {
        env.fail(VerificationError::MisalignedPacketAccess { pc, off, size });
        return;
    }
}

pub fn check_packet_meta_access(
    env: &mut VerifierEnv,
    state: &State,
    base: Reg,
    off: i16,
    size: i64,
    pc: usize,
) {
    let (start_ok, end_ok) = check_meta_access(&state.dbm, base, off as i64, size as i64);
    if !start_ok || !end_ok {
        env.fail(VerificationError::UnsafePacketLoad { pc, off, size });
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
        // If DBM is not tracking the offset, try the offset stored in the pointer
        _ => {
            if map_off_opt.is_some() {
                let fixed_off = map_off_opt.unwrap();
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
            } else {
                // Bounds are infinite or unknown. This is a potential OOB.
                error!("Unbounded variable map access at pc {}", pc);
                state.dbm.pretty_print();
                env.fail(VerificationError::UnsafeMapLoad { 
                    pc, off: insn_off.into(), size, limit: map_limit 
                });
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
