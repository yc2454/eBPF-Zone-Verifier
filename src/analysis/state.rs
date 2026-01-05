// src/analysis/state.rs
use crate::ast::{AluOp, CmpOp, Instr, MemSize, Operand, Width};
use crate::domain::{RegType, TypeState, REG_ENV, Reg};
use crate::dbm::Dbm;
use crate::analysis::context::ExecContext;
use crate::ctx_model::{classify_tc_ctx_field, CtxFieldKind};

// --- BRANCH REFINEMENT LOGIC ---

pub fn refine_branch_types(
    instr: &Instr,
    succ_pc: usize,
    _succ_dbm: &Dbm,
    types: &mut TypeState,
) {
    match instr {
        Instr::If { op: CmpOp::Ne, left, right: Operand::Imm(0), target, .. } => {
            if succ_pc == *target {
                maybe_promote_map_val(types, *left);
            }
        },
        Instr::If { op: CmpOp::Eq, left, right: Operand::Imm(0), target, .. } => {
            if succ_pc != *target {
                maybe_promote_map_val(types, *left);
            }
        },
        Instr::If { op: CmpOp::UGt, left, right: Operand::Imm(0), target, .. } => {
            if succ_pc == *target {
                maybe_promote_map_val(types, *left);
            }
        },
        _ => {}
    }
}

fn maybe_promote_map_val(types: &mut TypeState, reg: Reg) {
    let (target_id, target_map_idx) = match types.get(reg) {
        RegType::PtrToMapValueOrNull { id, map_idx } => (id, map_idx),
        _ => return,
    };

    println!("[Refine] Promoting ID {} (Map {}) to safe PtrToMapValue", target_id, target_map_idx);

    for r in Reg::ALL {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = types.get(r) {
            if id == target_id {
                let final_map_idx = map_idx;
                types.set(r, RegType::PtrToMapValue { 
                    offset: 0, 
                    map_idx: final_map_idx 
                });
            }
        }
    }
}

// --- PACKET RANGE REFINEMENT ---

pub fn update_packet_ranges(
    dbm: &Dbm, 
    types: &mut TypeState, 
    packet_reg: Reg, 
    packet_end_reg: Reg
) {
    let target_id = match types.get(packet_reg) {
        RegType::PtrToPacket { id, .. } => id,
        _ => return, 
    };

    println!("[PacketRefine] Refining Packet ID {} (Triggered by {:?} <= {:?})", target_id, packet_reg, packet_end_reg);

    let mut max_new_range = 0;

    // 1. Update Registers
    for r in REG_ENV.all() {
        if let RegType::PtrToPacket { id, range } = types.get(*r) {
            if id == target_id {
                let (_, ub) = crate::domain::get_bounds(dbm, *r, packet_end_reg);
                
                if let Some(upper) = ub {
                    if upper <= 0 {
                        let safe_bytes = upper.abs() as u64;
                        if safe_bytes > range {
                            println!("[PacketRefine] SUCCESS! Updating Reg {:?} range {} -> {}", r, range, safe_bytes);
                            types.set(*r, RegType::PtrToPacket { id, range: safe_bytes });
                            if safe_bytes > max_new_range {
                                max_new_range = safe_bytes;
                            }
                        } else if range > max_new_range {
                            max_new_range = range;
                        }
                    }
                }
            }
        }
    }

    // 2. Update Stack Slots (Critical for spilled registers)
    if max_new_range > 0 {
        let stack_keys: Vec<i16> = types.stack.keys().cloned().collect();
        for k in stack_keys {
            if let RegType::PtrToPacket { id, range } = types.get_stack(k) {
                if id == target_id {
                    if max_new_range > range {
                        println!("[PacketRefine] Updating Stack[{}] range {} -> {}", k, range, max_new_range);
                        types.set_stack(k, RegType::PtrToPacket { id, range: max_new_range });
                    }
                }
            }
        }
    }
}

// --- TYPE UPDATES FOR INSTRUCTIONS ---

pub fn update_reg_types_for_instr(
    ctx: &ExecContext,
    instr: &Instr,
    types: &mut TypeState,
    pc: usize
) {
    match *instr {
        Instr::MovArg0 { dst } => { types.set(dst, RegType::PtrToCtx); }
        Instr::Alu { width, op, dst, src } => { update_alu_types(ctx, pc, types, width, op, dst, src); }
        Instr::Load { size, dst, base, off } => { update_load_types(types, size, dst, base, off); }
        Instr::Store { size, base, off, src } => { update_store_types(types, size, base, off, src); }
        Instr::Call { helper } => { update_call_types(types, helper); }
        _ => {}
    }
}

fn update_alu_types(
    ctx: &ExecContext,
    pc: usize,
    types: &mut TypeState,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: Operand,
) {
    if width == Width::W32 { types.set(dst, RegType::ScalarValue); return; }
    match op {
        AluOp::Mov => handle_mov(ctx, pc, types, dst, src),
        AluOp::Add => handle_add(types, dst, src),
        AluOp::Sub => handle_sub(types, dst, src),
        _ => types.set(dst, RegType::ScalarValue),
    }
}

fn handle_mov(ctx: &ExecContext, pc: usize, types: &mut TypeState, dst: Reg, src: Operand) {
    match src {
        Operand::Reg(r) => { types.set(dst, types.get(r)); }
        Operand::Imm(_) => {
            let mut map_idx_opt = ctx.pc_to_map_idx.get(&pc);
            if map_idx_opt.is_none() { map_idx_opt = ctx.pc_to_map_idx.get(&(pc + 1)); }
            if let Some(&map_idx) = map_idx_opt {
                if map_idx < ctx.map_defs.len() {
                    let def = &ctx.map_defs[map_idx];
                    println!("[Reloc] Raw PC {} -> Loaded Map '{}' (Idx {})", pc, def.name, map_idx);
                    types.set(dst, RegType::PtrToMapObject { map_idx });
                } else { types.set(dst, RegType::ScalarValue); }
            } else {
                let old_ty = types.get(dst);
                if !matches!(old_ty, RegType::PtrToMapObject{..}) {
                    types.set(dst, RegType::ScalarValue);
                }
            }
        }
    }
}

fn handle_add(types: &mut TypeState, dst: Reg, src: Operand) {
    let dst_ty = types.get(dst);
    if let (true, Operand::Imm(k)) = (dst_ty.is_pointer(), src) {
        match dst_ty {
            RegType::PtrToPacket { id, range } => {
                let new_range = if k > 0 { range.saturating_sub(k as u64) } else { range.saturating_add(k.wrapping_neg() as u64) };
                types.set(dst, RegType::PtrToPacket { id, range: new_range });
            }
            RegType::PtrToMapValue { offset, map_idx } => { types.set(dst, RegType::PtrToMapValue { offset: offset + k, map_idx }); }
            _ => types.set(dst, dst_ty),
        }
    } else { types.set(dst, RegType::ScalarValue); }
}

fn handle_sub(types: &mut TypeState, dst: Reg, src: Operand) {
    let dst_ty = types.get(dst);
    if let (true, Operand::Imm(k)) = (dst_ty.is_pointer(), src) {
        match dst_ty {
            RegType::PtrToPacket { id, range } => {
                let new_range = if k > 0 { range.saturating_add(k as u64) } else { range.saturating_sub(k.wrapping_neg() as u64) };
                types.set(dst, RegType::PtrToPacket { id, range: new_range });
            }
            RegType::PtrToMapValue { offset, map_idx } => { types.set(dst, RegType::PtrToMapValue { offset: offset - k, map_idx }); }
            _ => types.set(dst, dst_ty),
        }
    } else { types.set(dst, RegType::ScalarValue); }
}

fn update_load_types(types: &mut TypeState, size: MemSize, dst: Reg, base: Reg, off: i16) {
    let base_ty = types.get(base);
    match base_ty {
        RegType::PtrToCtx => {
            if size == MemSize::U32 {
                if off == 76 { let new_id = crate::domain::new_packet_id(); types.set(dst, RegType::PtrToPacket { id: new_id, range: 0 }); return; }
                if off == 80 { types.set(dst, RegType::PtrToPacketEnd); return; }
            }
            if let Some(kind) = classify_tc_ctx_field(off, size) {
                match kind {
                    CtxFieldKind::PacketStart => { let new_id = crate::domain::new_packet_id(); types.set(dst, RegType::PtrToPacket { id: new_id, range: 0 }); }
                    CtxFieldKind::PacketEnd => { types.set(dst, RegType::PtrToPacketEnd); }
                    CtxFieldKind::PtrToMem { region } => { types.set(dst, RegType::PtrToMem { region }); }
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else { types.set(dst, RegType::ScalarValue); }
        }
        RegType::PtrToStack => {
            if size == MemSize::U64 { types.set(dst, types.get_stack(off)); } else { types.set(dst, RegType::ScalarValue); }
        }
        _ => types.set(dst, RegType::ScalarValue),
    }
}

// *** POINTER WRITE PROTECTION IMPLEMENTED HERE ***
fn update_store_types(types: &mut TypeState, size: MemSize, base: Reg, off: i16, src: Reg) {
    if base == Reg::R10 {
        if size == MemSize::U64 { 
            let new_type = types.get(src);
            let current_type = types.get_stack(off);

            // FIX: If stack holds Pointer and we write Scalar (0), ignore it.
            if current_type.is_pointer() && !new_type.is_pointer() {
                println!("[Verifier] Ignoring Scalar overwrite of Pointer at Stack[{}] ({:?} <- {:?})", off, current_type, new_type);
                return;
            }
            types.set_stack(off, new_type); 
        } else { 
            // FIX: Protect Partial overwrites too
            let current_type = types.get_stack(off);
            if current_type.is_pointer() {
                 println!("[Verifier] Ignoring partial overwrite of Pointer at Stack[{}] (Size {:?})", off, size);
            } else {
                 types.stack.remove(&off); 
            }
        }
    }
}

fn update_call_types(types: &mut TypeState, helper: u32) {
    let r1_type = types.get(Reg::R1);
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] { types.set(r, RegType::ScalarValue); }
    match helper {
        1 => {
            let map_idx = if let RegType::PtrToMapObject { map_idx } = r1_type { map_idx } else { 0 };
            let new_id = crate::domain::new_packet_id();
            types.set(Reg::R0, RegType::PtrToMapValueOrNull { id: new_id, map_idx });
        }
        _ => { types.set(Reg::R0, RegType::ScalarValue); }
    }
}