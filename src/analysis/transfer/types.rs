// src/analysis/transfer/types.rs
//
// Type update logic for all instruction types

use crate::analysis::env::VerifierEnv;
use crate::analysis::reg_types::{RegType, TypeState, new_packet_id};
use crate::analysis::state::State;
use crate::ast::{AluOp, AtomicOp, MapLoadKind, MemSize, Operand, Width};
use crate::zone::domain::Reg;
use crate::analysis::ctx_model::{
    CtxFieldKind, validate_ctx_access
};
use crate::common::constants;

/// Updates register types after an ALU operation.
pub(crate) fn update_alu_types(
    env: &VerifierEnv, 
    in_types: &TypeState, 
    types: &mut TypeState,
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
                    // Special case: R10 (frame pointer) becomes PtrToStack { offset: 0 }
                    if *r == Reg::R10 {
                        types.set(dst, RegType::PtrToStack { offset: Some(0) });
                    } else {
                        types.set(dst, src_ty); 
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
                    (RegType::PtrToMapValue { offset, map_idx }, Operand::Imm(k)) => {
                        let new_off = offset.map(|o| o + k);
                        types.set(dst, RegType::PtrToMapValue { offset: new_off, map_idx });
                    },
                    (RegType::PtrToMapValue { map_idx, .. }, Operand::Reg(_)) => {
                        types.set(dst, RegType::PtrToMapValue { offset: None, map_idx });
                    },
                    (RegType::PtrToPacket { id, is_base: _ }, Operand::Imm(k)) => {
                        if *k > constants::MAX_PACKET_OFF as i64 || *k < 0 {
                            types.set(dst, RegType::ScalarValue);
                        } else {
                            types.set(dst, RegType::PtrToPacket {
                                id,
                                is_base: false,
                            });
                        }
                    },
                    (RegType::PtrToPacketMeta, Operand::Imm(k)) => {
                        if *k > constants::MAX_PACKET_OFF as i64 || *k < 0 {
                            types.set(dst, RegType::ScalarValue);
                        }
                    },
                    (RegType::PtrToStack { offset }, Operand::Imm(k)) => {
                        types.set(dst, RegType::PtrToStack { offset: offset.map(|o| o + k) });
                    },
                    (RegType::PtrToStack { offset: _ }, Operand::Reg(_)) => {
                        types.set(dst, RegType::PtrToStack { offset: None });
                    },
                    (RegType::PtrToCtx, Operand::Imm(0)) => {
                        types.set(dst, RegType::PtrToCtx);
                    },
                    (RegType::PtrToCtx, Operand::Imm(_)) => {
                        // PtrToCtx should not be altered. If it is, we invalidate the type
                        // by setting it to ScalarValue
                        types.set(dst, RegType::ScalarValue);
                    },
                    (RegType::PtrToMem { region, range }, Operand::Imm(k)) => {
                        let new_range = if *k > 0 { 
                            range.saturating_sub(*k as u64) 
                        } else { 
                            range.saturating_add(k.wrapping_neg() as u64) 
                        };
                        types.set(dst, RegType::PtrToMem { region, range: new_range });
                    },
                    (RegType::PtrToMem { .. }, Operand::Reg(_)) => {
                        // Variable offset - lose precise tracking
                        types.set(dst, RegType::ScalarValue);
                    },
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        },
        AluOp::Sub => {
            let dst_ty = in_types.get(dst);
            if let (true, Operand::Imm(k)) = (dst_ty.is_pointer(), src) {
                match dst_ty {
                    RegType::PtrToMapValue { offset, map_idx } => {
                        let new_off = offset.map(|o| o - k);
                        types.set(dst, RegType::PtrToMapValue { offset: new_off, map_idx });
                    },
                    RegType::PtrToPacket { id, is_base: _ } => {
                        types.set(dst, RegType::PtrToPacket { id, is_base: false });
                    },
                    RegType::PtrToStack { offset } => {
                        types.set(dst, RegType::PtrToStack { offset: offset.map(|o| o - k) });
                    },
                    RegType::PtrToCtx => {
                        if *k == 0 {
                            types.set(dst, RegType::PtrToCtx);
                        } else {
                            types.set(dst, RegType::ScalarValue);
                        }
                    },
                    RegType::PtrToMem { region, range } => {
                        let new_range = if *k > 0 { 
                            range.saturating_add(*k as u64) 
                        } else { 
                            range.saturating_sub(k.wrapping_neg() as u64) 
                        };
                        types.set(dst, RegType::PtrToMem { region, range: new_range });
                    },
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        },
        _ => types.set(dst, RegType::ScalarValue),
    }
}

/// Updates register types after a Load operation.
pub(crate) fn update_load_types(
    env: &VerifierEnv, 
    types: &mut TypeState, 
    size: usize, 
    dst: Reg, 
    base: Reg, 
    off: i16
) {
    let base_ty = types.get(base);
    match base_ty {
        RegType::PtrToCtx => {
            let kind = validate_ctx_access(env.ctx.prog_kind, off, size as i64);
            if let Some(info) = kind {
                match info.kind {
                    CtxFieldKind::PacketStart => {
                        let new_id = new_packet_id();
                        types.set(dst, RegType::PtrToPacket { id: new_id, is_base: true });
                    }
                    CtxFieldKind::PacketEnd => {
                        types.set(dst, RegType::PtrToPacketEnd);
                    }
                    CtxFieldKind::PtrToMem { region } => {
                        types.set(dst, RegType::PtrToMem { region, range: 0 });
                    }
                    CtxFieldKind::PacketMeta => {
                        types.set(dst, RegType::PtrToPacketMeta);
                    }
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
        RegType::PtrToStack { offset: base_offset } => {
            match base_offset {
                Some(base) => {
                    let actual_slot = base + (off as i64);
                    if size == MemSize::U64.bytes() as usize { 
                        types.set(dst, types.get_stack(actual_slot as i16)); 
                    } else { 
                        types.set(dst, RegType::ScalarValue); 
                    }
                }
                None => {
                    // Unknown stack offset - can't determine which slot we're reading
                    // Conservative: result is scalar (could be anything)
                    types.set(dst, RegType::ScalarValue);
                }
            }
        }
        _ => types.set(dst, RegType::ScalarValue),
    }
}

/// Updates stack types after a Store operation.
pub(crate) fn update_store_types(
    types: &mut TypeState, 
    src_type: RegType, 
    size: MemSize, 
    base_type: RegType, 
    off: i16
) {
    let stack_slot = match base_type {
        RegType::PtrToStack { offset } => offset.map(|o| o + (off as i64)),
        _ => None,
    };
    
    if let Some(slot) = stack_slot {
        let slot = slot as i16;
        let byte_count = size.bytes() as i16;  // U8=1, U16=2, U32=4, U64=8
        
        if size == MemSize::U64 {
            // Full 8-byte store preserves type info at the base slot
            types.set_stack(slot, src_type);
            // Mark remaining bytes as initialized (but no type info)
            for i in 1..byte_count {
                types.set_stack(slot + i, RegType::ScalarValue);
            }
        } else {
            // Partial store: mark all bytes as initialized, but poison type info
            for i in 0..byte_count {
                types.set_stack(slot + i, RegType::ScalarValue);
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

/// Invalidates packet pointers on the stack.
pub(crate) fn invalidate_stack_packet_pointers(types: &mut TypeState) {
    let keys: Vec<i16> = types.stack.keys().cloned().collect();
    for k in keys {
        match types.get_stack(k) {
            RegType::PtrToPacket { .. } | RegType::PtrToPacketEnd => {
                types.set_stack(k, RegType::ScalarValue);
            }
            _ => {}
        }
    }
}

/// Updates register types after a helper Call.
pub(crate) fn update_call_types(env: &mut VerifierEnv, in_types: &TypeState, state: &mut State, helper: u32) {
    // 1. Clobber caller-saved registers - they are NOT readable after the call
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        state.types.set(r, RegType::NotInit);
    }
    
    // 2. Set R0 based on helper return type
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
                        state.types.set(Reg::R0, RegType::PtrToSocketOrNull { id });
                    }
                    _ => {
                        let id = new_packet_id();
                        state.types.set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
                    }
                }
            }
        }
        
        // Socket lookup helpers - return PTR_TO_SOCKET_OR_NULL
        constants::BPF_SK_LOOKUP_TCP | constants::BPF_SK_LOOKUP_UDP => {
            let id = state.acquire_ref();
            state.types.set(Reg::R0, RegType::PtrToSocketOrNull { id });
        }
        
        // SKC lookup - returns PTR_TO_SOCK_COMMON_OR_NULL
        constants::BPF_SKC_LOOKUP_TCP => {
            let id = state.acquire_ref();
            state.types.set(Reg::R0, RegType::PtrToSockCommonOrNull { id });
        }
        
        // SKC to TCP sock conversion - returns PTR_TO_TCP_SOCK_OR_NULL
        constants::BPF_SKC_TO_TCP_SOCK | 
        constants::BPF_SKC_TO_TCP6_SOCK |
        constants::BPF_SKC_TO_TCP_TIMEWAIT_SOCK |
        constants::BPF_SKC_TO_TCP_REQUEST_SOCK => {
            let id = state.acquire_ref();
            state.types.set(Reg::R0, RegType::PtrToTcpSockOrNull { id });
        }
        
        // SKC to UDP/Unix - return SOCK_COMMON for now (simplified)
        constants::BPF_SKC_TO_UDP6_SOCK |
        constants::BPF_SKC_TO_UNIX_SOCK => {
            let id = state.acquire_ref();
            state.types.set(Reg::R0, RegType::PtrToSockCommonOrNull { id });
        }

        // Release socket reference
        constants::BPF_SK_RELEASE => {
            if let Some(ref_id) = state.types.get(Reg::R1).get_ref_id() {
                state.release_ref(ref_id);
                state.invalidate_ref(ref_id);
            }
        }
        
        // tail_call: R0 is undefined on failure path
        constants::BPF_TAIL_CALL => {
            state.types.set(Reg::R0, RegType::ScalarValue);
        }

        constants::BPF_SKB_LOAD_BYTES => {
            let mem_ptr_ty = in_types.get(Reg::R3);
            match mem_ptr_ty {
                RegType::PtrToStack { offset: Some(off) } => {
                    let slot = off as i16;
                    state.types.set_stack(slot, RegType::ScalarValue);
                }
                _ => {} // Do nothing for the other cases for now
            }
        }
        
        _ => {
            state.types.set(Reg::R0, RegType::ScalarValue);
        }
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
        invalidate_stack_packet_pointers(&mut state.types);
    }
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
            map_idx: map_fd as usize, 
            offset: Some(0) 
        },
    };

    types.set(dst, new_type);
}

pub(crate) fn update_atomic_op_types(
    types: &mut TypeState,
    op: AtomicOp,
    src: Reg,
    fetch: bool
) {
    if op == AtomicOp::CmpXchg {
        // CmpXchg: If match, memory updated. If mismatch, old value loaded into R0.
        // In both cases, R0 is overwritten with the value from memory.
        types.set(Reg::R0, RegType::ScalarValue);
    } else if fetch {
        // Add, And, Or, Xor, Xchg with Fetch:
        // The 'src' register is overwritten with the OLD value from memory.
        types.set(src, RegType::ScalarValue);
    }
}
