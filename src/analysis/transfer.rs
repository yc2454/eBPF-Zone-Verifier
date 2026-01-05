// src/analysis/transfer.rs
use crate::ast::{AluOp, CmpOp, Instr, Operand, Width, EndianKind, MemSize};
use crate::domain::{RegType, TypeState, get_bounds, forget, Reg};
use crate::dbm::Dbm;
use crate::analysis::context::{ExecContext, proven_u32_range};
use crate::stats::AnalysisStats;
use crate::domain::{
    assign_eq, assign_zero, assign_add_imm, assign_add_reg,
    assign_and_mask, assign_mul_imm,
    assume_ge_const, assume_le_const, assume_less_than, assume_eq_const,
    assume_ge_var, assume_le_var, assume_gt_var, assume_le_var_plus_const,
};
use crate::analysis::access::{perform_memory_load, perform_memory_store};
use crate::analysis::state::update_packet_ranges;

fn transfer_mov_arg0(dbm_in: &Dbm, pc: usize, dst: Reg, reg_types: &TypeState) -> Vec<(usize, Dbm, TypeState)> {
    let mut dbm = dbm_in.clone();
    let mut next_types = reg_types.clone();
    forget(&mut dbm, dst);
    next_types.set(dst, RegType::PtrToCtx);
    vec![(pc + 1, dbm, next_types)]
}

fn transfer_alu(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: Operand,
    stats: &mut AnalysisStats,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    let mut dbm = dbm_in.clone();
    let mut next_types = reg_types.clone();

    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    if width == Width::W32 {
                        forget(&mut dbm, dst);
                        assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                        assume_le_const(&mut dbm, dst, ctx.zero, 0xffff_ffff);
                    } else {
                        if r == ctx.r10 { assign_zero(&mut dbm, dst, ctx.zero); } 
                        else { assign_eq(&mut dbm, dst, r); }
                    }
                }
                Operand::Imm(c) => {
                    let c = if width == Width::W32 { (c as u32) as i64 } else { c };
                    forget(&mut dbm, dst);
                    assume_le_const(&mut dbm, dst, ctx.zero, c);
                    assume_ge_const(&mut dbm, dst, ctx.zero, c);
                }
            }
        }
        AluOp::Add => {
            match src {
                Operand::Imm(c) => assign_add_imm(&mut dbm, dst, c),
                Operand::Reg(r) => assign_add_reg(&mut dbm, dst, r, ctx.zero),
            }
        }
        AluOp::Sub => {
            match src {
                Operand::Imm(c) => assign_add_imm(&mut dbm, dst, -c),
                Operand::Reg(_r) => forget(&mut dbm, dst),
            }
        }
        AluOp::And => {
            match src {
                Operand::Imm(mask) => {
                    let mask = if width == Width::W32 { (mask as u32) as i64 } else { mask };
                    assign_and_mask(&mut dbm, dst, mask, ctx.zero)
                }
                Operand::Reg(_r) => forget(&mut dbm, dst),
            }
        }
        AluOp::Or => { forget(&mut dbm, dst); }
        AluOp::Shl | AluOp::Arsh => forget(&mut dbm, dst),
        AluOp::Shr => {
             match src {
                Operand::Imm(k) => {
                    let bits = if width == Width::W32 { 32u32 } else { 64u32 };
                    let k = (k as u32).min(bits);
                    forget(&mut dbm, dst);
                    assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                    if k < bits {
                        let ub: i64 = ((1u128 << (bits - k)) - 1) as i64;
                        assume_le_const(&mut dbm, dst, ctx.zero, ub);
                    } else {
                        assume_eq_const(&mut dbm, dst, ctx.zero, 0);
                    }
                }
                Operand::Reg(_) => forget(&mut dbm, dst),
            }
        }
        AluOp::Mul => {
             match src {
                Operand::Imm(c) => assign_mul_imm(&mut dbm, dst, c, ctx.zero),
                Operand::Reg(_) => forget(&mut dbm, dst),
            }
        }
        AluOp::Mod => {
             match src {
                Operand::Imm(c) => {
                    if c > 0 {
                        forget(&mut dbm, dst);
                        assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                        assume_le_const(&mut dbm, dst, ctx.zero, c - 1);
                    } else { forget(&mut dbm, dst); }
                }
                Operand::Reg(_) => forget(&mut dbm, dst),
            }
        }
        AluOp::Xor => forget(&mut dbm, dst),
    }

    // Note: Type updates for ALU are handled in state::update_reg_types_for_instr
    // Here we just reset to Scalar if it's a basic ALU op.
    let is_32bit = width == Width::W32;
    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    if is_32bit { next_types.set(dst, RegType::ScalarValue); } 
                    else { next_types.set(dst, reg_types.get(r)); }
                }
                Operand::Imm(_) => { next_types.set(dst, RegType::ScalarValue); }
            }
        }
        // Arithmetic on Pointers is calculated in `update_reg_types_for_instr`
        // We set to Scalar here as a default, expecting it to be overwritten if it's a valid ptr arithmetic
        _ => { next_types.set(dst, RegType::ScalarValue); }
    }

    if dbm.is_inconsistent() {
        println!("ERROR: ALU transfer led to inconsistent state at pc {}", pc);
        stats.mark_dbm_inconsistent();
        vec![]
    } else {
        vec![(pc + 1, dbm, next_types)]
    }
}

fn transfer_endian(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    dst: Reg,
    kind: EndianKind,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    let mut dbm = dbm_in.clone();
    let mut next_types = reg_types.clone();

    forget(&mut dbm, dst);
    let (lo, hi) = match kind {
        EndianKind::Be16 => (0i64, 0x0000_ffff),
        EndianKind::Be32 => (0i64, 0xffff_ffff),
        EndianKind::Be64 => {
             next_types.set(dst, RegType::ScalarValue);
             return vec![(pc + 1, dbm, next_types)];
        }
    };
    assume_ge_const(&mut dbm, dst, ctx.zero, lo);
    assume_le_const(&mut dbm, dst, ctx.zero, hi);
    next_types.set(dst, RegType::ScalarValue);
    vec![(pc + 1, dbm, next_types)]
}

fn transfer_if(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: Operand,
    target: usize,
    reg_types_in: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    let mut out = Vec::new();
    let mut dbm_then = dbm_in.clone();
    let mut types_then = reg_types_in.clone();
    let mut dbm_else = dbm_in.clone();
    let mut types_else = reg_types_in.clone();

    // 1. Literal Checks (Eq, Ne)
    match (op, right) {
        (CmpOp::Ne, Operand::Imm(imm)) => {
            assume_eq_const(&mut dbm_else, left, ctx.zero, imm);
            let (lo, hi) = get_bounds(dbm_in, left, ctx.zero);
            if let (Some(l), Some(h)) = (lo, hi) {
                if l == imm && h == imm {
                    assume_less_than(&mut dbm_then, ctx.zero, ctx.zero, 0); 
                }
            }
        }
        (CmpOp::Eq, Operand::Imm(imm)) => {
             assume_eq_const(&mut dbm_then, left, ctx.zero, imm);
             let (lo, hi) = get_bounds(dbm_in, left, ctx.zero);
             if let (Some(l), Some(h)) = (lo, hi) {
                if l == imm && h == imm {
                    assume_less_than(&mut dbm_else, ctx.zero, ctx.zero, 0);
                }
             }
        }
        _ => {}
    }

    // 2. 32-bit Logic (Fallback)
    if width == Width::W32 {
        if let Operand::Imm(_c) = right {
            // For simple range checks on u32, if not proven safe, bail to both paths
            if matches!(op, CmpOp::Eq | CmpOp::Ne | CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt) && !proven_u32_range(dbm_in, left, ctx.zero) {
                out.push((pc + 1, dbm_in.clone(), reg_types_in.clone()));
                out.push((target, dbm_in.clone(), reg_types_in.clone()));
                return out;
            }
        } else {
            out.push((pc + 1, dbm_in.clone(), reg_types_in.clone()));
            out.push((target, dbm_in.clone(), reg_types_in.clone()));
            return out;
        }
    }

    // 3. Register Comparisons (The Critical Packet Logic)
    match (op, right) {
        (CmpOp::UGe, Operand::Imm(c)) => {
            assume_ge_const(&mut dbm_then, left, ctx.zero, c);
            assume_less_than(&mut dbm_else, left, ctx.zero, c);
        }
        (CmpOp::ULe, Operand::Imm(c)) => {
            assume_le_const(&mut dbm_then, left, ctx.zero, c);
            assume_ge_const(&mut dbm_else, left, ctx.zero, c + 1);
        }
        (CmpOp::UGt, Operand::Imm(c)) => {
            assume_ge_const(&mut dbm_then, left, ctx.zero, c + 1);
            assume_le_const(&mut dbm_else, left, ctx.zero, c);
        }
        (CmpOp::ULt, Operand::Imm(c)) => {
            assume_less_than(&mut dbm_then, left, ctx.zero, c);
            assume_ge_const(&mut dbm_else, left, ctx.zero, c);
        }

        // --- PACKET VS END COMPARISONS ---
        (cmp_op, Operand::Reg(r)) => {
            let right_reg = r;
            
            // Apply Constraints
            match cmp_op {
                CmpOp::UGe => { // Left >= Right
                    assume_ge_var(&mut dbm_then, left, right_reg);
                    assume_le_var_plus_const(&mut dbm_else, left, right_reg, -1);
                }
                CmpOp::ULe => { // Left <= Right
                    assume_le_var(&mut dbm_then, left, right_reg);
                    assume_gt_var(&mut dbm_else, left, right_reg);
                }
                CmpOp::UGt => { // Left > Right
                    assume_gt_var(&mut dbm_then, left, right_reg);
                    assume_le_var(&mut dbm_else, left, right_reg);
                }
                CmpOp::ULt => { // Left < Right
                    assume_le_var_plus_const(&mut dbm_then, left, right_reg, -1);
                    assume_ge_var(&mut dbm_else, left, right_reg);
                }
                _ => {}
            }

            // Check Refinement for Packet/PacketEnd
            let l_ty_then = types_then.get(left);
            let r_ty_then = types_then.get(right_reg);
            
            let l_ty_else = types_else.get(left);
            let r_ty_else = types_else.get(right_reg);

            // --- THEN Branch Refinement ---
            // If condition implies Packet <= End, refine
            match cmp_op {
                CmpOp::ULe | CmpOp::ULt => {
                    // Packet <= End
                    if matches!(l_ty_then, RegType::PtrToPacket{..}) && matches!(r_ty_then, RegType::PtrToPacketEnd) {
                        update_packet_ranges(&dbm_then, &mut types_then, left, right_reg);
                    }
                    // End >= Packet (Swapped operands)
                    if matches!(l_ty_then, RegType::PtrToPacketEnd) && matches!(r_ty_then, RegType::PtrToPacket{..}) {
                        update_packet_ranges(&dbm_then, &mut types_then, right_reg, left);
                    }
                }
                _ => {}
            }

            // --- ELSE Branch Refinement ---
            // If condition implies Packet > End is FALSE, then Packet <= End
            match cmp_op {
                CmpOp::UGt | CmpOp::UGe => {
                     // !(Packet > End) => Packet <= End
                     if matches!(l_ty_else, RegType::PtrToPacket{..}) && matches!(r_ty_else, RegType::PtrToPacketEnd) {
                         update_packet_ranges(&dbm_else, &mut types_else, left, right_reg);
                     }
                     // !(End >= Packet) => End < Packet (Unsafe) - No refinement here
                     // But if !(End < Packet) i.e. !(End < Packet) => End >= Packet => Packet <= End
                }
                CmpOp::ULt => { // Check if !(End < Packet)
                     // If test was End < Packet, then Else is End >= Packet (Safe)
                     if matches!(l_ty_else, RegType::PtrToPacketEnd) && matches!(r_ty_else, RegType::PtrToPacket{..}) {
                         update_packet_ranges(&dbm_else, &mut types_else, right_reg, left);
                     }
                }
                _ => {}
            }
        }
        _ => {}
    }

    if !dbm_then.is_inconsistent() { out.push((target, dbm_then, types_then)); }
    if !dbm_else.is_inconsistent() { out.push((pc + 1, dbm_else, types_else)); }
    out
}

fn transfer_call(
    _ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    helper: u32,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    let mut dbm = dbm_in.clone();
    let mut next_types = reg_types.clone();
    let r1_type = reg_types.get(Reg::R1);
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        forget(&mut dbm, r);
        next_types.set(r, RegType::ScalarValue);
    }
    forget(&mut dbm, Reg::R0);
    match helper {
        1 => { // bpf_map_lookup_elem
            let map_idx = if let RegType::PtrToMapObject { map_idx } = r1_type { map_idx } else { 0 };
            let new_id = crate::domain::new_packet_id();
            next_types.set(Reg::R0, RegType::PtrToMapValueOrNull { id: new_id, map_idx });
        }
        _ => { next_types.set(Reg::R0, RegType::ScalarValue); }
    }
    vec![(pc + 1, dbm, next_types)]
}

pub fn transfer_instr(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    instr: &Instr,
    stats: &mut AnalysisStats,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    match instr {
        Instr::MovArg0 { dst } => transfer_mov_arg0(dbm_in, pc, *dst, reg_types),
        Instr::Alu { width, op, dst, src } => transfer_alu(ctx, dbm_in, pc, *width, *op, *dst, *src, stats, reg_types),
        Instr::Endian { dst, kind } => transfer_endian(ctx, dbm_in, pc, *dst, *kind, reg_types),
        Instr::If { width, left, op, right, target } => transfer_if(ctx, dbm_in, pc, *width, *left, *op, *right, *target, reg_types),
        Instr::Load { size, dst, base, off } => {
                let base_ty = reg_types.get(*base);
                transfer_load(ctx, dbm_in, pc, *size, *dst, *base, base_ty, *off, stats, reg_types)
            },
        Instr::Store { size, base, off, src } => transfer_store(ctx, dbm_in, pc, *size, *base, *off, *src, stats, reg_types),
        Instr::Call { helper } => transfer_call(ctx, dbm_in, pc, *helper, reg_types),
        Instr::Jmp { target } => vec![(*target, dbm_in.clone(), reg_types.clone())],
        Instr::Exit => vec![],
    }
}

fn transfer_load(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    dst: Reg,
    base: Reg,
    base_type: RegType,
    off: i16,
    stats: &mut AnalysisStats,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    // Delegate to access logic
    perform_memory_load(ctx, dbm_in, pc, size, dst, base, base_type, off, stats, reg_types)
}

fn transfer_store(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    base: Reg,
    off: i16,
    src: Reg,
    stats: &mut AnalysisStats,
    reg_types: &TypeState,
) -> Vec<(usize, Dbm, TypeState)> {
    // Delegate to access logic
    perform_memory_store(ctx, dbm_in, pc, size, base, off, src, stats, reg_types)
}
