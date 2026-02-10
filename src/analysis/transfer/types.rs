// src/analysis/transfer/types.rs
//
// Type update logic for all instruction types

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg_types::{RegType, TypeState, new_ptr_id};
use crate::analysis::machine::stack_state::StackState;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, MapLoadKind, MemSize, Operand, Width};
use crate::zone::domain::{self, Reg};
use crate::common::ctx_model::{
    CtxFieldKind, validate_ctx_access
};
use crate::common::constants;
use crate::zone::dbm::Dbm;

fn update_packet_ptr_type_after_add(
    types: &mut TypeState,
    in_types: &TypeState,
    dbm: &Dbm,
    dst: Reg,
    id: u32,
    range: i64,
    val: i64
) {
    if val > constants::MAX_PACKET_OFF as i64 || val < 0 {
        types.set(dst, RegType::ScalarValue);
    } else {
        let packet_start_reg_op = domain::REG_ENV.all().iter()
            .find(|&&r| matches!(in_types.get(r), RegType::PtrToPacket { id: _, is_base: true, range: _ }));
        if packet_start_reg_op.is_none() {
            types.set(dst, RegType::ScalarValue);
        } else {
            let packet_start_reg = packet_start_reg_op.unwrap();
            if let (Some(_), Some(packet_offset)) = domain::get_relative_bound(dbm, dst, *packet_start_reg) {
                if packet_offset <= constants::MAX_PACKET_OFF as i64 {
                    types.set(dst, RegType::PtrToPacket { id, is_base: false, range });
                } else {
                    types.set(dst, RegType::ScalarValue);
                }
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
    pc: usize
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
                    if src_ty.is_pointer() {
                        match src_ty {
                            RegType::PtrToPacket { id, is_base: true, range } => {
                                types.set(dst, RegType::PtrToPacket { id, is_base: false, range });
                            },
                            RegType::PtrToPacketMeta { is_base: true } => {
                                types.set(dst, RegType::PtrToPacketMeta { is_base: false });
                            },
                            _ => {}
                        }
                    }            
                }
                Operand::Imm(_) => {
                    let reloc = env.ctx.pc_to_reloc.get(&pc)
                        .or_else(|| env.ctx.pc_to_reloc.get(&(pc + 1)));
                    
                    if let Some(info) = reloc {
                        if info.map_idx < env.ctx.map_defs.len() {
                            let map_name = &env.ctx.map_defs[info.map_idx].name;
                            // Data sections become PtrToMapValue
                            if map_name.starts_with(".rodata") || 
                            map_name.starts_with(".data") || 
                            map_name == ".bss" 
                            {
                                types.set(dst, RegType::PtrToMapValue { 
                                    id: new_ptr_id(),
                                    offset: Some(info.offset), 
                                    map_idx: info.map_idx,
                                });
                            } else {
                                types.set(dst, RegType::PtrToMapObject { map_idx: info.map_idx });
                            }
                        } else {
                            types.set(dst, RegType::ScalarValue);
                        }
                    } else {
                        types.set(dst, RegType::ScalarValue);
                    }
                }
            }
        },
        AluOp::Add => {
            let dst_ty = in_types.get(dst);
            if dst_ty.is_pointer() {
                match (dst_ty, src) {
                    (RegType::PtrToMapValue { id, offset, map_idx }, Operand::Imm(k)) => {
                        let new_off = offset.map(|o| o + k);
                        types.set(dst, RegType::PtrToMapValue { id, offset: new_off, map_idx });
                    },
                    (RegType::PtrToMapValue { id, map_idx, offset }, Operand::Reg(src_reg)) => {
                        let src_reg_value = domain::get_constant_value(dbm, *src_reg);
                        if src_reg_value.is_some() {
                            let src_reg_value = src_reg_value.unwrap();
                            types.set(dst, RegType::PtrToMapValue { offset: offset.map(|o| o + src_reg_value), map_idx, id });
                        } else {
                            types.set(dst, RegType::PtrToMapValue { offset: None, map_idx, id });
                        }
                    },
                    (RegType::PtrToPacket { id, is_base: _, range }, Operand::Imm(k)) => {
                        update_packet_ptr_type_after_add(types, in_types, dbm, dst, id, range, *k);
                    },
                    (RegType::PtrToPacket { id, is_base: _, range }, Operand::Reg(r)) => {
                        let const_value_op = domain::get_constant_value(dbm, *r);
                        if const_value_op.is_some() {
                            let const_value = const_value_op.unwrap();
                            update_packet_ptr_type_after_add(types, in_types, dbm, dst, id, range, const_value);
                        }
                    }
                    (RegType::PtrToPacketMeta { .. }, Operand::Imm(k)) => {
                        if *k > constants::MAX_PACKET_OFF as i64 || *k < 0 {
                            types.set(dst, RegType::ScalarValue);
                        } else {
                            let packet_start_reg_op = domain::REG_ENV.all().iter()
                                .find(|&&r| matches!(in_types.get(r), RegType::PtrToPacketMeta { is_base: true }));
                            if packet_start_reg_op.is_none() {
                                types.set(dst, RegType::ScalarValue);
                            } else {
                                let packet_start_reg = packet_start_reg_op.unwrap();
                                let packet_offset = domain::get_diff(dbm, dst, *packet_start_reg);
                                if packet_offset <= constants::MAX_PACKET_OFF as i64 {
                                    types.set(dst, RegType::PtrToPacketMeta { is_base: false } );
                                } else {
                                    dbm.dump_matrix();
                                    types.set(dst, RegType::ScalarValue);
                                }
                            }
                        }
                    },
                    (RegType::PtrToStack { offset, frame_level }, Operand::Imm(k)) => {
                        types.set(dst, RegType::PtrToStack { offset: offset.map(|o| o + k), frame_level });
                    },
                    (RegType::PtrToStack { offset: _, frame_level }, Operand::Reg(_)) => {
                        types.set(dst, RegType::PtrToStack { offset: None, frame_level });
                    },
                    (RegType::PtrToCtx, Operand::Imm(0)) => {
                        types.set(dst, RegType::PtrToCtx);
                    },
                    (RegType::PtrToCtx, Operand::Imm(_)) => {
                        // PtrToCtx should not be altered. If it is, we invalidate the type
                        // by setting it to ScalarValue
                        types.set(dst, RegType::ScalarValue);
                    },
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else {
                match src {
                    Operand::Imm(_) => {
                        types.set(dst, RegType::ScalarValue);
                    }
                    Operand::Reg(src_reg) => {
                        let src_ty = in_types.get(*src_reg);
                        match src_ty {
                            RegType::PtrToPacket { id, is_base: true, range } => {
                                types.set(dst, RegType::PtrToPacket { id, is_base: false, range });
                            }
                            _ => {
                                types.set(dst, src_ty);
                            }
                        }
                    }
                }
            }
        },
        AluOp::Sub => {
            let dst_ty = in_types.get(dst);
            if dst_ty.is_pointer() {
                match (dst_ty, src) {
                    (RegType::PtrToMapValue { id, offset, map_idx }, Operand::Imm(k)) => {
                        let new_off = offset.map(|o| o - k);
                        types.set(dst, RegType::PtrToMapValue { id, offset: new_off, map_idx });
                    },
                    (RegType::PtrToMapValue { id, map_idx, offset }, Operand::Reg(src_reg)) => {
                        let src_reg_value = domain::get_constant_value(dbm, *src_reg);
                        if src_reg_value.is_some() {
                            let src_reg_value = src_reg_value.unwrap();
                            types.set(dst, RegType::PtrToMapValue { offset: offset.map(|o| o - src_reg_value), map_idx, id });
                        } else {
                            types.set(dst, RegType::PtrToMapValue { offset: None, map_idx, id });
                        }
                    },
                    (RegType::PtrToPacket { id, is_base: _, range }, Operand::Imm(k)) => {
                        update_packet_ptr_type_after_add(types, in_types, dbm, dst, id, range, *k);
                    },
                    (RegType::PtrToPacketMeta { .. }, Operand::Imm(k)) => {
                        if *k > constants::MAX_PACKET_OFF as i64 || *k < 0 {
                            types.set(dst, RegType::ScalarValue);
                        } else {
                            let packet_start_reg_op = domain::REG_ENV.all().iter()
                                .find(|&&r| matches!(in_types.get(r), RegType::PtrToPacketMeta { is_base: true }));
                            if packet_start_reg_op.is_none() {
                                types.set(dst, RegType::ScalarValue);
                            } else {
                                let packet_start_reg = packet_start_reg_op.unwrap();
                                let packet_offset = domain::get_diff(dbm, dst, *packet_start_reg);
                                if packet_offset <= constants::MAX_PACKET_OFF as i64 {
                                    types.set(dst, RegType::PtrToPacketMeta { is_base: false } );
                                } else {
                                    dbm.dump_matrix();
                                    types.set(dst, RegType::ScalarValue);
                                }
                            }
                        }
                    },
                    (RegType::PtrToStack { offset, frame_level }, Operand::Imm(k)) => {
                        types.set(dst, RegType::PtrToStack { offset: offset.map(|o| o - k), frame_level });
                    },
                    (RegType::PtrToStack { offset: _, frame_level }, Operand::Reg(_)) => {
                        types.set(dst, RegType::PtrToStack { offset: None, frame_level });
                    },
                    (RegType::PtrToCtx, Operand::Imm(0)) => {
                        types.set(dst, RegType::PtrToCtx);
                    },
                    (RegType::PtrToCtx, Operand::Imm(_)) => {
                        // PtrToCtx should not be altered. If it is, we invalidate the type
                        // by setting it to ScalarValue
                        types.set(dst, RegType::ScalarValue);
                    },
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else {
                match src {
                    Operand::Imm(_) => {
                        types.set(dst, RegType::ScalarValue);
                    }
                    Operand::Reg(src_reg) => {
                        let src_ty = in_types.get(*src_reg);
                        types.set(dst, src_ty);
                    }
                }
            }
        },
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
    off: i16
) {
    let base_ty = state.types.get(base);
    match base_ty {
        RegType::PtrToCtx => {
            let kind = validate_ctx_access(env.ctx.prog_kind, off, size as i64);
            if let Some(info) = kind {
                match info.kind {
                    CtxFieldKind::PacketStart => {
                        let new_id = new_ptr_id();
                        state.types.set(dst, RegType::PtrToPacket { id: new_id, is_base: true, range: 0 });
                    }
                    CtxFieldKind::PacketEnd => {
                        state.types.set(dst, RegType::PtrToPacketEnd);
                    }
                    CtxFieldKind::SockCommon => {
                        state.types.set(dst, RegType::PtrToSockCommonOrNull { ref_id: None });
                    }
                    CtxFieldKind::PacketMeta => {
                        state.types.set(dst, RegType::PtrToPacketMeta { is_base: true });
                    }
                    _ => state.types.set(dst, RegType::ScalarValue),
                }
            } else {
                state.types.set(dst, RegType::ScalarValue);
            }
        }
        RegType::PtrToStack { offset: base_offset, .. } => {
            match base_offset {
                Some(base) => {
                    let actual_slot = base + (off as i64);
                    if size == MemSize::U64.bytes() as usize { 
                        state.types.set(dst, state.stack().get_slot_type(actual_slot as i16)); 
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
pub(crate) fn update_store_types(
    stack: &mut StackState,
    src_type: RegType, 
    size: MemSize, 
    base_type: RegType, 
    off: i16
) {
    let stack_slot = match base_type {
        RegType::PtrToStack { offset, .. } => offset.map(|o| o + (off as i64)),
        _ => None,
    };
    
    if let Some(slot) = stack_slot {
        let slot = slot as i16;
        let byte_count = size.bytes() as i16;  // U8=1, U16=2, U32=4, U64=8
        
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
    matches!(helper,
        constants::BPF_XDP_ADJUST_HEAD |
        constants::BPF_XDP_ADJUST_META |
        constants::BPF_SKB_PULL_DATA |
        constants::BPF_SKB_CHANGE_HEAD |
        constants::BPF_SKB_CHANGE_TAIL |
        constants::BPF_SKB_CHANGE_PROTO |
        constants::BPF_SKB_ADJUST_ROOM
    )
}

/// Updates register types after a helper Call.
pub(crate) fn update_call_types(env: &mut VerifierEnv, in_types: &TypeState, state: &mut State, helper: u32) {
    // Release socket reference
    if helper == constants::BPF_SK_RELEASE {
        if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
            state.release_ref(ref_id);
            state.invalidate_ref(ref_id);
        }
    }
    
    // Set R0 based on helper return type
    match helper {
        constants::BPF_MAP_LOOKUP_ELEM => {
            let map_idx = match in_types.get(Reg::R1) {
                RegType::PtrToMapObject { map_idx } => map_idx,
                _ => 0,
            };
            let map_def_opt = env.ctx.map_defs.get(map_idx);
            if map_def_opt.is_none() {
                state.types.set(Reg::R0, RegType::ScalarValue);
            } else {
                let map_def = map_def_opt.unwrap();
                match map_def.type_ {
                    constants::BPF_MAP_TYPE_SOCKMAP | constants::BPF_MAP_TYPE_SOCKHASH => {
                        let id = state.acquire_ref();
                        state.types.set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: Some(id) });
                    }
                    _ => {
                        let id = new_ptr_id();
                        state.types.set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
                    }
                }
            }
        }
        
        // Socket lookup helpers - return PTR_TO_SOCKET_OR_NULL
        constants::BPF_SK_LOOKUP_TCP | constants::BPF_SK_LOOKUP_UDP => {
            let id = state.acquire_ref();
            state.types.set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: Some(id) });
        }
        
        // The socket reference from bpf_get_listener_sock doesn't need to be released
        constants::BPF_GET_LISTENER_SOCK => {
            state.types.set(Reg::R0, RegType::PtrToSocketOrNull { ref_id: None });
        }

        // Copies ref id from argument
        constants::BPF_SK_FULLSOCK => {
            let ref_id = state.types.get(Reg::R1).get_ref_id();
            state.types.set(Reg::R0, RegType::PtrToSocketOrNull { ref_id });
        }

        constants::BPF_TCP_SOCK => {
            let id = state.types.get(Reg::R1).get_ref_id();
            state.types.set(Reg::R0, RegType::PtrToTcpSockOrNull { id });
        }
        
        // SKC lookup - returns PTR_TO_SOCK_COMMON_OR_NULL
        constants::BPF_SKC_LOOKUP_TCP => {
            let id = state.acquire_ref();
            state.types.set(Reg::R0, RegType::PtrToSockCommonOrNull { ref_id: Some(id) });
        }

        constants::BPF_SK_RELEASE => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.release_ref(ref_id);
                state.invalidate_ref(ref_id);
            }
        }
        
        // SKC to TCP sock conversion - returns PTR_TO_TCP_SOCK_OR_NULL
        constants::BPF_SKC_TO_TCP_SOCK | 
        constants::BPF_SKC_TO_TCP6_SOCK |
        constants::BPF_SKC_TO_TCP_TIMEWAIT_SOCK |
        constants::BPF_SKC_TO_TCP_REQUEST_SOCK => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.types.set(Reg::R0, RegType::PtrToTcpSockOrNull { id: Some(ref_id) });
            }
        }
        
        // SKC to UDP/Unix - return SOCK_COMMON for now (simplified)
        constants::BPF_SKC_TO_UDP6_SOCK |
        constants::BPF_SKC_TO_UNIX_SOCK => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.types.set(Reg::R0, RegType::PtrToSockCommonOrNull { ref_id: Some(ref_id) });
            }
        }

        constants::BPF_SK_STORAGE_GET => {
            let RegType::PtrToMapValueOrNull { id, map_idx } = in_types.get(Reg::R3) else {
                state.types.set(Reg::R0, RegType::ScalarValue);
                return;
            };
            state.types.set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
        }
        
        // tail_call: R0 is undefined on failure path
        constants::BPF_TAIL_CALL => {
            state.types.set(Reg::R0, RegType::ScalarValue);
        }

        constants::BPF_SKB_LOAD_BYTES => {
            let mem_ptr_ty = in_types.get(Reg::R3);
            match mem_ptr_ty {
                RegType::PtrToStack { offset: Some(off), .. } => {
                    let slot = off as i16;
                    state.types.set(Reg::R3, RegType::ScalarValue);
                    state.spill(Reg::R3, slot);
                }
                _ => {} // Do nothing for the other cases for now
            }
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
                RegType::PtrToPacket { .. } | RegType::PtrToPacketEnd => {
                    state.types.set(r, RegType::ScalarValue);
                }
                _ => {}
            }
        }
        state.stack_mut().invalidate_packet_pointers();
    }
}

pub(crate) fn update_call_rel_types(state: &mut State) {
    state.types.set(Reg::R0, RegType::NotInit);
    state.types.set(Reg::R10, RegType::PtrToStack { offset: Some(0), frame_level: state.current_frame_level() });
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

pub(crate) fn update_map_load_types(types: &mut TypeState, kind: MapLoadKind, map_fd: usize, dst: Reg) {
    let new_type = match kind {
        MapLoadKind::MapPtr => RegType::PtrToMapObject { 
            map_idx: map_fd as usize
        },
        MapLoadKind::MapValue => RegType::PtrToMapValue { 
            id: new_ptr_id(),
            map_idx: map_fd as usize, 
            offset: Some(0) 
        },
    };

    types.set(dst, new_type);
}
