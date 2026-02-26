// src/analysis/transfer/types.rs
//
// Type update logic for all instruction types

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState, new_ptr_id};
use crate::analysis::machine::stack_state::StackState;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, MapLoadKind, MemSize, Operand, Width};
use crate::common::constants;
use crate::common::ctx_model::{CtxFieldKind, validate_ctx_access};
use crate::domains::dbm::Dbm;
use crate::domains::domain::{self, get_distance_fixed, get_interval};

fn update_packet_ptr_type_after_alu(types: &mut TypeState, dbm: &Dbm, dst: Reg) {
    // Check offset from anchor: dst - @data
    let offset_from_data = dbm.get(dst, Reg::AnchorData);
    if offset_from_data <= constants::MAX_PACKET_OFF {
        types.set(dst, RegType::PtrToPacket);
    } else {
        types.set(dst, RegType::ScalarValue);
    }
}

/// Extracts a fixed i64 value from an operand (immediate or register with known value)
fn get_operand_fixed_value(dbm: &Dbm, src: &Operand) -> Option<i64> {
    match src {
        Operand::Imm(k) => Some(*k),
        Operand::Reg(r) => domain::get_fixed_value(dbm, *r),
    }
}

/// Updates PtrToMapValue offset by delta, returning new type
fn adjust_map_value_offset(ty: RegType, delta: Option<i64>) -> RegType {
    match ty {
        RegType::PtrToMapValue {
            id,
            offset,
            map_idx,
        } => {
            let new_offset = match (offset, delta) {
                (Some(o), Some(d)) => Some(o + d),
                _ => None, // Unknown if either is unknown
            };
            RegType::PtrToMapValue {
                id,
                offset: new_offset,
                map_idx,
            }
        }
        other => other,
    }
}

/// Unified handler for pointer arithmetic (Add/Sub) type updates
fn update_ptr_arithmetic_type(
    types: &mut TypeState,
    dbm: &Dbm,
    dst: Reg,
    dst_ty: RegType,
    src: &Operand,
    is_add: bool, // true = Add, false = Sub
) {
    let delta = get_operand_fixed_value(dbm, src);
    let signed_delta = if is_add { delta } else { delta.map(|d| -d) };

    match dst_ty {
        RegType::PtrToMapValue { .. } => {
            types.set(dst, adjust_map_value_offset(dst_ty, signed_delta));
        }
        RegType::PtrToMapObject { .. } => {
            // Only allow adding/subtracting 0
            if signed_delta != Some(0) {
                types.set(dst, RegType::ScalarValue);
            }
            // else: type unchanged (adding 0 is a no-op)
        }
        RegType::PtrToStack { frame_level } => {
            types.set(dst, RegType::PtrToStack { frame_level });
        }
        RegType::PtrToCtx => {
            if signed_delta == Some(0) {
                types.set(dst, RegType::PtrToCtx);
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
        RegType::PtrToPacket => {
            if is_add {
                // For Add: check if immediate exceeds max offset
                if let Some(d) = delta {
                    if d >= constants::MAX_PACKET_OFF {
                        types.set(dst, RegType::ScalarValue);
                    }
                    // else: type unchanged, still PtrToPacket
                }
                // For Add with register: check if known value exceeds max
                else if let Operand::Reg(_) = src {
                    // delta is None means unknown - keep type unchanged
                }
            } else {
                // For Sub: use anchor-based bounds check
                update_packet_ptr_type_after_alu(types, dbm, dst);
            }
        }
        RegType::PtrToPacketMeta => {
            let offset_from_meta = dbm.get(dst, Reg::AnchorDataMeta);
            if offset_from_meta <= constants::MAX_PACKET_OFF {
                types.set(dst, RegType::PtrToPacketMeta);
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
        _ => types.set(dst, RegType::ScalarValue),
    }
}

/// Handles scalar + pointer/scalar arithmetic type updates
fn handle_scalar_arithmetic_type(
    in_types: &TypeState,
    types: &mut TypeState,
    dst: Reg,
    src: &Operand,
    is_add: bool,
) {
    match src {
        Operand::Imm(_) => {
            types.set(dst, RegType::ScalarValue);
        }
        Operand::Reg(src_reg) => {
            let src_ty = in_types.get(*src_reg);
            if is_add {
                // scalar + pointer => pointer type (commutative)
                types.set(dst, src_ty);
            } else {
                // scalar - pointer => scalar (subtraction from scalar)
                types.set(dst, src_ty);
            }
        }
    }
}

/// Updates register types after an ALU operation.
pub(crate) fn update_alu_types(
    env: &VerifierEnv,
    in_types: &TypeState,
    types: &mut TypeState,
    dbm: &Dbm,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: &Operand,
    pc: usize,
) {
    if width == Width::W32 {
        types.set(dst, RegType::ScalarValue);
        return;
    }
    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    let src_ty = in_types.get(*r);
                    types.set(dst, src_ty);
                }
                Operand::Imm(_) => {
                    let reloc = env
                        .ctx
                        .pc_to_reloc
                        .get(&pc)
                        .or_else(|| env.ctx.pc_to_reloc.get(&(pc + 1)));

                    if let Some(info) = reloc {
                        if info.map_idx < env.ctx.map_defs.len() {
                            let map_name = &env.ctx.map_defs[info.map_idx].name;
                            // Data sections become PtrToMapValue
                            if map_name.starts_with(".rodata")
                                || map_name.starts_with(".data")
                                || map_name == ".bss"
                            {
                                types.set(
                                    dst,
                                    RegType::PtrToMapValue {
                                        id: new_ptr_id(),
                                        offset: Some(info.offset),
                                        map_idx: info.map_idx,
                                    },
                                );
                            } else {
                                types.set(dst, RegType::ScalarValue);
                            }
                        } else {
                            types.set(dst, RegType::ScalarValue);
                        }
                    } else {
                        types.set(dst, RegType::ScalarValue);
                    }
                }
            }
        }
        AluOp::Add | AluOp::Sub => {
            let dst_ty = in_types.get(dst);
            let is_add = op == AluOp::Add;

            if dst_ty.is_pointer() {
                update_ptr_arithmetic_type(types, dbm, dst, dst_ty, src, is_add);
            } else {
                handle_scalar_arithmetic_type(in_types, types, dst, src, is_add);
            }
        }
        _ => types.set(dst, RegType::ScalarValue),
    }
}

/// Updates register types after a Load operation.
pub(crate) fn update_load_types(
    env: &VerifierEnv,
    state: &mut State,
    size: usize,
    dst: Reg,
    base: Reg,
    off: i16,
) {
    let base_ty = state.types.get(base);
    match base_ty {
        RegType::PtrToCtx => {
            let kind = validate_ctx_access(env, off, size as i64);
            if let Some(info) = kind {
                match info.kind {
                    CtxFieldKind::PacketMeta => {
                        state.types.set(dst, RegType::PtrToPacketMeta);
                    }
                    CtxFieldKind::PacketStart => {
                        state.types.set(dst, RegType::PtrToPacket);
                    }
                    CtxFieldKind::PacketEnd => {
                        state.types.set(dst, RegType::PtrToPacketEnd);
                    }
                    CtxFieldKind::SockCommon => {
                        state
                            .types
                            .set(dst, RegType::PtrToSockCommonOrNull { ref_id: None });
                    }
                    CtxFieldKind::TrustedPtr {
                        type_name,
                        nullable,
                    } => {
                        if nullable {
                            state.types.set(
                                dst,
                                RegType::PtrToBtfIdOrNull {
                                    id: new_ptr_id(),
                                    type_name,
                                    trusted: true,
                                },
                            );
                        } else {
                            state.types.set(
                                dst,
                                RegType::PtrToBtfId {
                                    type_name,
                                    trusted: true,
                                },
                            );
                        }
                    }
                    _ => state.types.set(dst, RegType::ScalarValue),
                }
            } else {
                state.types.set(dst, RegType::ScalarValue);
            }
        }
        RegType::PtrToStack { .. } => {
            match get_distance_fixed(state.dbm(), base, Reg::R10) {
                Some(base_off) => {
                    let actual_slot = base_off + (off as i64);
                    if size == MemSize::U64.bytes() {
                        state
                            .types
                            .set(dst, state.stack().get_slot_type(actual_slot as i16));
                    } else {
                        state.types.set(dst, RegType::ScalarValue);
                    }
                }
                None => {
                    // Unknown stack offset - can't determine which slot we're reading
                    // Conservative: result is scalar (could be anything)
                    state.types.set(dst, RegType::ScalarValue);
                }
            }
        }
        _ => state.types.set(dst, RegType::ScalarValue),
    }
}

/// Updates stack types after a Store operation.
/// `resolved_stack_offset` is the already-resolved stack slot (base_offset + insn_off),
/// or None if the base is not a stack pointer or offset is unknown.
pub(crate) fn update_store_types(
    stack: &mut StackState,
    src_type: RegType,
    size: MemSize,
    resolved_stack_offset: Option<i64>,
) {
    let stack_slot = resolved_stack_offset;

    if let Some(slot) = stack_slot {
        let slot = slot as i16;
        let byte_count = size.bytes() as i16; // U8=1, U16=2, U32=4, U64=8

        if size == MemSize::U64 {
            // Full 8-byte store preserves type info at the base slot
            stack.set_slot_type(slot, src_type, None);
            // Mark remaining bytes as initialized (but no type info)
            for i in 1..byte_count {
                stack.set_slot_type(slot + i, RegType::ScalarValue, None);
            }
        } else {
            // Partial store: mark all bytes as initialized, but poison type info
            for i in 0..byte_count {
                stack.set_slot_type(slot + i, RegType::ScalarValue, None);
            }
        }
    }
}

/// Checks if a helper invalidates packet pointers.
pub(crate) fn helper_invalidates_packets(helper: u32) -> bool {
    matches!(
        helper,
        constants::BPF_XDP_ADJUST_HEAD
            | constants::BPF_XDP_ADJUST_META
            | constants::BPF_SKB_PULL_DATA
            | constants::BPF_SKB_CHANGE_HEAD
            | constants::BPF_SKB_CHANGE_TAIL
            | constants::BPF_SKB_CHANGE_PROTO
            | constants::BPF_SKB_ADJUST_ROOM
            | constants::BPF_SKB_STORE_BYTES
            | constants::BPF_SKB_VLAN_PUSH
            | constants::BPF_SKB_VLAN_POP
    )
}

/// Updates register types after a helper Call.
pub(crate) fn update_call_types(
    env: &mut VerifierEnv,
    in_types: &TypeState,
    state: &mut State,
    helper: u32,
) {
    // Default to scalar value
    state.types.set(Reg::R0, RegType::ScalarValue);

    // Release socket reference
    if helper == constants::BPF_SK_RELEASE
        && let Some(ref_id) = state.types.get(Reg::R1).get_ref_id()
    {
        state.release_ref(ref_id);
        state.invalidate_ref(ref_id);
    }

    // Set R0 based on helper return type
    match helper {
        constants::BPF_MAP_LOOKUP_ELEM | constants::BPF_GET_LOCAL_STORAGE => {
            let map_idx = match in_types.get(Reg::R1) {
                RegType::PtrToMapObject { map_idx } => map_idx,
                RegType::PtrToMapValue { map_idx, .. } => map_idx, // Handles map-in-map lookups
                _ => 0,
            };
            let map_def_opt = env.ctx.map_defs.get(map_idx);
            if let Some(map_def) = map_def_opt {
                match map_def.type_ {
                    constants::BPF_MAP_TYPE_SOCKMAP | constants::BPF_MAP_TYPE_SOCKHASH => {
                        let id = state.acquire_ref();
                        state
                            .types
                            .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: Some(id) });
                    }
                    _ => {
                        let id = new_ptr_id();
                        state
                            .types
                            .set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
                    }
                }
            } else {
                state.types.set(Reg::R0, RegType::ScalarValue);
            }
        }

        // Socket lookup helpers - return PTR_TO_SOCKET_OR_NULL
        constants::BPF_SK_LOOKUP_TCP | constants::BPF_SK_LOOKUP_UDP => {
            let id = state.acquire_ref();
            state
                .types
                .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: Some(id) });
        }

        // The socket reference from bpf_get_listener_sock doesn't need to be released
        constants::BPF_GET_LISTENER_SOCK => {
            state
                .types
                .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: None });
        }

        // Copies ref id from argument
        constants::BPF_SK_FULLSOCK => {
            let ref_id = state.types.get(Reg::R1).get_ref_id();
            state
                .types
                .set(Reg::R0, RegType::PtrToSocketOrNull { ref_id });
        }

        constants::BPF_TCP_SOCK => {
            let id = state.types.get(Reg::R1).get_ref_id();
            state.types.set(Reg::R0, RegType::PtrToTcpSockOrNull { id });
        }

        // SKC lookup - returns PTR_TO_SOCK_COMMON_OR_NULL
        constants::BPF_SKC_LOOKUP_TCP => {
            let id = state.acquire_ref();
            state
                .types
                .set(Reg::R0, RegType::PtrToSockCommonOrNull { ref_id: Some(id) });
        }

        constants::BPF_SK_RELEASE => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.release_ref(ref_id);
                state.invalidate_ref(ref_id);
            }
        }

        // SKC to TCP sock conversion - returns PTR_TO_TCP_SOCK_OR_NULL
        constants::BPF_SKC_TO_TCP_SOCK
        | constants::BPF_SKC_TO_TCP6_SOCK
        | constants::BPF_SKC_TO_TCP_TIMEWAIT_SOCK
        | constants::BPF_SKC_TO_TCP_REQUEST_SOCK => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state
                    .types
                    .set(Reg::R0, RegType::PtrToTcpSockOrNull { id: Some(ref_id) });
            }
        }

        // SKC to UDP/Unix - return SOCK_COMMON for now (simplified)
        constants::BPF_SKC_TO_UDP6_SOCK | constants::BPF_SKC_TO_UNIX_SOCK => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.types.set(
                    Reg::R0,
                    RegType::PtrToSockCommonOrNull {
                        ref_id: Some(ref_id),
                    },
                );
            }
        }

        constants::BPF_SK_STORAGE_GET => {
            let RegType::PtrToMapValueOrNull { id, map_idx } = in_types.get(Reg::R3) else {
                state.types.set(Reg::R0, RegType::ScalarValue);
                return;
            };
            state
                .types
                .set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
        }

        // tail_call: R0 is undefined on failure path
        constants::BPF_TAIL_CALL => {
            state.types.set(Reg::R0, RegType::ScalarValue);
        }

        constants::BPF_SKB_LOAD_BYTES => {
            let mem_ptr_ty = in_types.get(Reg::R3);
            if let RegType::PtrToStack { frame_level } = mem_ptr_ty
                && let Some(off) = get_distance_fixed(state.dbm(), Reg::R3, Reg::R10)
            {
                let (_, hi) = get_interval(state.dbm(), Reg::R4);
                let len = if hi <= 0xFFFF { hi as i16 } else { 0 };
                if len > 0 {
                    // Mark the stack range as initialized scalars
                    for i in 0..len {
                        state.stack_at_mut(frame_level).set_slot_type(
                            (off + i as i64) as i16,
                            RegType::ScalarValue,
                            None,
                        );
                    }
                }
            }
        }

        constants::BPF_RINGBUF_RESERVE => {
            let (_, hi) = get_interval(state.dbm(), Reg::R2);
            state.types.set(
                Reg::R0,
                RegType::PtrToAllocMemOrNull {
                    id: new_ptr_id(),
                    mem_size: hi as u64,
                },
            );
        }

        _ => {
            state.types.set(Reg::R0, RegType::ScalarValue);
        }
    }

    // Clobber caller-saved registers - they are NOT readable after the call
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        state.types.set(r, RegType::NotInit);
    }

    // 3. Invalidate packet pointers if needed
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            match state.types.get(r) {
                RegType::PtrToPacket | RegType::PtrToPacketEnd => {
                    state.types.set(r, RegType::ScalarValue);
                }
                _ => {}
            }
        }
        state.stack_mut().invalidate_packet_pointers();
        state
            .frames
            .invalidate_caller_reg_type(|ty| ty.is_packet_ptr(), RegType::NotInit);
    }
}

pub(crate) fn update_call_rel_types(state: &mut State) {
    state.types.set(Reg::R0, RegType::NotInit);
    state.types.set(
        Reg::R10,
        RegType::PtrToStack {
            frame_level: state.current_frame_level(),
        },
    );
}

pub(crate) fn update_packet_load_types(types: &mut TypeState) {
    // Clobber R1 - R5
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        types.set(r, RegType::NotInit);
    }

    // Set Result (R0)
    // The loaded data is placed in R0.
    types.set(Reg::R0, RegType::ScalarValue);
}

pub(crate) fn update_map_load_types(
    types: &mut TypeState,
    kind: MapLoadKind,
    map_fd: usize,
    dst: Reg,
) {
    let new_type = match kind {
        MapLoadKind::MapPtr => RegType::PtrToMapObject { map_idx: map_fd },
        MapLoadKind::MapValue => RegType::PtrToMapValue {
            id: new_ptr_id(),
            map_idx: map_fd,
            offset: Some(0),
        },
    };

    types.set(dst, new_type);
}
