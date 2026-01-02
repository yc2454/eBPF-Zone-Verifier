// src/exec.rs
use std::collections::VecDeque;

use crate::ast::{AluOp, CmpOp, Instr, MemSize, Operand, Program, Width, EndianKind};
use crate::dbm::Dbm;
use crate::domain::{
    Reg, REG_ENV,
    // assignment / forget
    assign_eq, assign_zero,
    assign_add_imm, assign_add_reg,
    assign_and_mask, assign_mul_imm,
    forget,
    // assume / guards
    assume_ge_const, assume_le_const, assume_less_than, assume_eq_const,
    assume_ge_var, assume_le_var, assume_gt_var, assume_le_var_plus_const,
    // new: register types
    RegType, RegTypeState,
    get_bounds, BpfMapDef
};
use crate::utils::{dbm_equals};
use crate::stats::AnalysisStats;
use crate::ctx_model::{classify_tc_ctx_field, CtxFieldKind};
use std::collections::HashMap;

#[derive(Clone)]
pub struct ExecContext {
    pub zero: Reg,
    pub r10: Reg,
    pub stack_min: i64,
    pub stack_max: i64,
    pub map_defs: Vec<BpfMapDef>,
    pub pc_to_map_idx: HashMap<usize, usize>,
}

/// Is v provably in [0, 0xffffffff] as a 32-bit unsigned value?
fn proven_u32_range(dbm: &Dbm, v: Reg, zero: Reg) -> bool {
    // requires: (v - 0) <= 0xffff_ffff  AND  (0 - v) <= 0
    let vi = REG_ENV.index(v);
    let zi = REG_ENV.index(zero);
    let ub = dbm.raw(vi, zi); // v - 0
    let lb = dbm.raw(zi, vi); // 0 - v  (<= 0 means v >= 0)
    ub <= 0xffff_ffff && lb <= 0
}

fn refine_branch_types(
    instr: &Instr,
    succ_pc: usize,
    _succ_dbm: &Dbm,
    types: &mut RegTypeState,
) {
    match instr {
        // Pattern: if reg != 0 goto target
        Instr::If { op: CmpOp::Ne, left, right: Operand::Imm(0), target, .. } => {
            // If we are jumping to 'target', then 'reg != 0' is True.
            if succ_pc == *target {
                println!("[Refine] PC {}: Promoting {:?} (Ne 0) on branch to {}", succ_pc, left, target);
                maybe_promote_map_val(types, *left);
            }
        },

        // Pattern: if reg == 0 goto target
        Instr::If { op: CmpOp::Eq, left, right: Operand::Imm(0), target, .. } => {
            // If we are falling through (NOT jumping), then 'reg == 0' is False => 'reg != 0'.
            if succ_pc != *target {
                println!("[Refine] PC {}: Promoting {:?} (Eq 0 Fallthrough)", succ_pc, left);
                maybe_promote_map_val(types, *left);
            }
        },

        // Pattern: if reg > 0 goto target (Unsigned)
        // For pointers, x > 0 implies x != 0.
        Instr::If { op: CmpOp::UGt, left, right: Operand::Imm(0), target, .. } => {
            if succ_pc == *target {
                println!("[Refine] PC {}: Promoting {:?} (Gt 0) on branch to {}", succ_pc, left, target);
                maybe_promote_map_val(types, *left);
            }
        },

        _ => {}
    }
    
    // (Your existing Packet Range refinement logic can stay here too)
}

fn maybe_promote_map_val(types: &mut RegTypeState, reg: Reg) {
    // 1. Check if the register is actually a MapValueOrNull
    let target_id = match types.get(reg) {
        RegType::PtrToMapValueOrNull { id, map_idx: _ } => id,
        _ => return,
    };

    println!("[Refine] Promoting ID {} to safe PtrToMapValue", target_id);

    // 2. Find ALL registers with this ID and promote them
    for r in Reg::ALL {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = types.get(r) {
            if id == target_id {
                types.set(r, RegType::PtrToMapValue { offset: 0, map_idx });
            }
        }
    }
}

// Helper to mimic kernel's find_good_pkt_pointers
fn update_packet_ranges(
    dbm: &Dbm, 
    types: &mut RegTypeState, 
    packet_reg: Reg, 
    packet_end_reg: Reg
) {
    // We just verified: packet_reg <= packet_end_reg
    // We want to update ranges for ALL registers sharing packet_reg's ID.
    
    let target_id = match types.get(packet_reg) {
        RegType::PtrToPacket { id, .. } => id,
        _ => return, 
    };

    // Scan all registers
    for r in Reg::ALL {
        if let RegType::PtrToPacket { id, range } = types.get(r) {
            if id == target_id {
                // We want to check: Is r <= packet_end_reg - K?
                // In DBM terms: upper_bound(r - packet_end_reg) <= -K
                // This implies r + K <= packet_end_reg.
                
                // get_bounds(A, B) returns bounds for (A - B)
                let (_, ub) = crate::domain::get_bounds(dbm, r, packet_end_reg);
                
                if let Some(upper) = ub {
                    if upper <= 0 {
                        // 'upper' is negative (e.g. -4). 
                        // r - end <= -4  =>  r + 4 <= end.
                        // Safe range is at least abs(upper).
                        let proved_safe = upper.abs() as u64;
                        if proved_safe > range {
                            types.set(r, RegType::PtrToPacket { id, range: proved_safe });
                            // println!("Refined range for {} to {}", r.name(), proved_safe);
                        }
                    }
                }
            }
        }
    }
}

fn transfer_mov_arg0(dbm_in: &Dbm, pc: usize, dst: Reg) -> Vec<(usize, Dbm, RegTypeState)> {
    let mut dbm = dbm_in.clone();
    forget(&mut dbm, dst);
    vec![(pc + 1, dbm, RegTypeState::new_not_init())]
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
    reg_types: &RegTypeState, // NEW: Input types
) -> Vec<(usize, Dbm, RegTypeState)> { // NEW: Return updated types
    let mut dbm = dbm_in.clone();
    
    // Clone types to determine the state after this instruction
    let mut next_types = reg_types.clone();

    // --- 1. Update Numeric State (DBM) ---
    // (This block remains largely the same as your original code)
    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    if width == Width::W32 {
                        // mov32: Zero-extend, lost relation to original 64-bit value
                        forget(&mut dbm, dst);
                        assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                        assume_le_const(&mut dbm, dst, ctx.zero, 0xffff_ffff);
                    } else {
                        // mov64
                        if r == ctx.r10 {
                            assign_zero(&mut dbm, dst, ctx.zero);
                        } else {
                            assign_eq(&mut dbm, dst, r);
                        }
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

        AluOp::Or => {
            if width == Width::W32 {
                forget(&mut dbm, dst);
                assume_ge_const(&mut dbm, dst, ctx.zero, 0);
                assume_le_const(&mut dbm, dst, ctx.zero, 0xffff_ffff);
            } else {
                forget(&mut dbm, dst);
            }
        }

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
                    } else {
                        forget(&mut dbm, dst);
                    }
                }
                Operand::Reg(_) => forget(&mut dbm, dst),
            }
        }

        AluOp::Xor => forget(&mut dbm, dst),
    }

    // --- 2. Update Register Type State ---
    
    // If 32-bit ALU op, we generally truncate pointers -> Scalar.
    // Exception: logic below handles specific cases.
    let is_32bit = width == Width::W32;

    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    if is_32bit {
                        // Mov32 destroys pointer semantics
                        next_types.set(dst, RegType::ScalarValue);
                    } else {
                        // Mov64 preserves type (including ID and Range)
                        next_types.set(dst, reg_types.get(r));
                    }
                }
                Operand::Imm(_) => {
                    next_types.set(dst, RegType::ScalarValue);
                }
            }
        }

        AluOp::Add => {
            let dst_ty = reg_types.get(dst);
            
            // Only preserve pointer types if 64-bit operation
            if !is_32bit && dst_ty.is_pointer() {
                match src {
                    Operand::Imm(k) => {
                        // Ptr += Imm
                        match dst_ty {
                            RegType::PtrToPacket { id, range } => {
                                // Arithmetic on packet ptr slides the valid range window
                                let new_range = if k > 0 {
                                    range.saturating_sub(k as u64)
                                } else {
                                    range.saturating_add(k.wrapping_neg() as u64)
                                };
                                next_types.set(dst, RegType::PtrToPacket { id, range: new_range });
                            }
                            _ => {
                                // Other pointers (Stack, Ctx, Mem) preserve type on Add Imm
                                next_types.set(dst, dst_ty);
                            }
                        }
                    }
                    Operand::Reg(r) => {
                        // Ptr += Reg. 
                        // If Reg is Scalar, type is theoretically preserved (but range is lost/hard to track).
                        // If Reg is Ptr, result is invalid (Ptr + Ptr).
                        if reg_types.get(r) == RegType::ScalarValue {
                            // We treat variable offset pointer arithmetic as invalidating the specific type
                            // for Packet pointers (reset range/id) or just downgrading to scalar.
                            // For MVP, safe default is ScalarValue.
                            next_types.set(dst, RegType::ScalarValue);
                        } else {
                            next_types.set(dst, RegType::ScalarValue);
                        }
                    }
                }
            } else {
                // Scalar += ... or 32-bit ops -> Scalar
                next_types.set(dst, RegType::ScalarValue);
            }
        }

        AluOp::Sub => {
            let dst_ty = reg_types.get(dst);

            if !is_32bit && dst_ty.is_pointer() {
                 match src {
                    Operand::Imm(k) => {
                        // Ptr -= Imm
                         match dst_ty {
                            RegType::PtrToPacket { id, range } => {
                                // Ptr -= k  == Ptr += -k
                                let new_range = if k > 0 {
                                    range.saturating_add(k as u64)
                                } else {
                                    range.saturating_sub(k.wrapping_neg() as u64)
                                };
                                next_types.set(dst, RegType::PtrToPacket { id, range: new_range });
                            }
                            _ => next_types.set(dst, dst_ty),
                        }
                    }
                    Operand::Reg(_r) => {
                        // Ptr - Ptr (if same region) => Scalar (offset).
                        // Ptr - Scalar => Ptr (with unknown offset).
                        // For MVP, downgrade everything to Scalar.
                        next_types.set(dst, RegType::ScalarValue);
                    }
                 }
            } else {
                next_types.set(dst, RegType::ScalarValue);
            }
        }

        // Bitwise logic / Multiplies / Modulo on pointers is invalid -> Scalar
        _ => {
            next_types.set(dst, RegType::ScalarValue);
        }
    }

    if dbm.is_inconsistent() {
        println!("ERROR: ALU transfer led to inconsistent state at pc {}", pc);
        dbm.dump_matrix();
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
) -> Vec<(usize, Dbm, RegTypeState)> {
    let mut dbm = dbm_in.clone();
    let next_types = RegTypeState::new_not_init();

    // Endian ops are nonlinear bit permutations; we cannot track the relation
    // to the old value. MVP: forget, then approximate the guaranteed range.
    forget(&mut dbm, dst);

    let (lo, hi) = match kind {
        EndianKind::Be16 => (0i64, 0x0000_ffff),
        EndianKind::Be32 => (0i64, 0xffff_ffff),
        EndianKind::Be64 => {
            // Byteswap64 preserves full 64-bit domain; no useful bound.
            return vec![(pc + 1, dbm, next_types)];
        }
    };

    assume_ge_const(&mut dbm, dst, ctx.zero, lo);
    assume_le_const(&mut dbm, dst, ctx.zero, hi);

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
    reg_types_in: &RegTypeState, // Logic relies on input types
) -> Vec<(usize, Dbm, RegTypeState)> { // Returns updated types per branch
    let mut out = Vec::new();

    // THEN branch: condition holds
    let mut dbm_then = dbm_in.clone();
    let mut types_then = reg_types_in.clone(); // Clone types for THEN

    // ELSE branch: condition does not hold
    let mut dbm_else = dbm_in.clone();
    let types_else = reg_types_in.clone(); // Clone types for ELSE

    // For JMP32 Eq/Ne with imm, only refine if left is already known to be u32-range.
    if width == Width::W32 {
        if let Operand::Imm(_c) = right {
            if matches!(
                op,
                CmpOp::Eq
                    | CmpOp::Ne
                    | CmpOp::UGe
                    | CmpOp::ULe
                    | CmpOp::UGt
                    | CmpOp::ULt
            ) && !proven_u32_range(dbm_in, left, ctx.zero)
            {
                // Can't model low32 comparison safely -> fork without refinement.
                // Return original types
                out.push((pc + 1, dbm_in.clone(), reg_types_in.clone()));
                out.push((target, dbm_in.clone(), reg_types_in.clone()));
                return out;
            }
        } else {
            // Reg comparisons in JMP32: too tricky with low32 semantics, don't refine.
            out.push((pc + 1, dbm_in.clone(), reg_types_in.clone()));
            out.push((target, dbm_in.clone(), reg_types_in.clone()));
            return out;
        }
    }

    match (op, right) {
        // ---------- left >= imm ----------
        (CmpOp::UGe, Operand::Imm(c)) => {
            assume_ge_const(&mut dbm_then, left, ctx.zero, c);
            assume_less_than(&mut dbm_else, left, ctx.zero, c);
        }

        // ---------- left <= imm ----------
        (CmpOp::ULe, Operand::Imm(c)) => {
            assume_le_const(&mut dbm_then, left, ctx.zero, c);
            assume_ge_const(&mut dbm_else, left, ctx.zero, c + 1);
        }

        // ---------- left > imm ----------
        (CmpOp::UGt, Operand::Imm(c)) => {
            assume_ge_const(&mut dbm_then, left, ctx.zero, c + 1);
            assume_le_const(&mut dbm_else, left, ctx.zero, c);
        }

        // ---------- left < imm ----------
        (CmpOp::ULt, Operand::Imm(c)) => {
            assume_less_than(&mut dbm_then, left, ctx.zero, c);
            assume_ge_const(&mut dbm_else, left, ctx.zero, c);
        }

        (CmpOp::Ne, Operand::Imm(imm)) => {
            assume_eq_const(&mut dbm_else, left, ctx.zero, imm);
        }

        // ---------- left >= reg ----------
        (CmpOp::UGe, Operand::Reg(r)) => {
            assume_ge_var(&mut dbm_then, left, r);
            assume_le_var_plus_const(&mut dbm_else, left, r, -1);
        }

        // ---------- left <= reg ----------
        (CmpOp::ULe, Operand::Reg(r)) => {
            assume_le_var(&mut dbm_then, left, r);
            assume_gt_var(&mut dbm_else, left, r);

            // --- PACKET SAFETY: if Packet <= End ---
            let l_ty = types_then.get(left);
            let r_ty = types_then.get(r);
            if matches!(l_ty, RegType::PtrToPacket{..}) && matches!(r_ty, RegType::PtrToPacketEnd) {
                 update_packet_ranges(&dbm_then, &mut types_then, left, r);
            }
        }

        // ---------- left > reg ----------
        (CmpOp::UGt, Operand::Reg(r)) => {
            assume_gt_var(&mut dbm_then, left, r);
            assume_le_var(&mut dbm_else, left, r);
            
            // --- PACKET SAFETY: if End > Packet (same as Packet < End) ---
            let l_ty = types_then.get(left);
            let r_ty = types_then.get(r);
            // End > Packet implies Packet <= End - 1
            if matches!(l_ty, RegType::PtrToPacketEnd) && matches!(r_ty, RegType::PtrToPacket{..}) {
                 update_packet_ranges(&dbm_then, &mut types_then, r, left);
            }
        }

        // ---------- left < reg ----------
        (CmpOp::ULt, Operand::Reg(r)) => {
            assume_le_var_plus_const(&mut dbm_then, left, r, -1);
            assume_ge_var(&mut dbm_else, left, r);

            // --- PACKET SAFETY: if Packet < End ---
             let l_ty = types_then.get(left);
             let r_ty = types_then.get(r);
             if matches!(l_ty, RegType::PtrToPacket{..}) && matches!(r_ty, RegType::PtrToPacketEnd) {
                  update_packet_ranges(&dbm_then, &mut types_then, left, r);
             }
        }

        (CmpOp::Eq, _) | (CmpOp::Ne, _) => {
            // Conservative: no constraints; just fork
        }
    }

    if !dbm_then.is_inconsistent() {
        out.push((target, dbm_then, types_then));
    }
    if !dbm_else.is_inconsistent() {
        out.push((pc + 1, dbm_else, types_else));
    }
    out
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
    reg_types: &RegTypeState, // Needed to scan for PacketEnd reg
) -> Vec<(usize, Dbm, RegTypeState)> { // Returns updated types
    use RegType::*;

    let mut dbm = dbm_in.clone();
    // Clone types because we will update 'dst'
    let mut next_types = reg_types.clone();

    let access_size = match size {
        MemSize::U8 => 1, MemSize::U16 => 2, MemSize::U32 => 4, MemSize::U64 => 8,
    };

    match base_type {
        // --- STACK LOGIC ---
        PtrToStack => {
            let (lo, hi) = crate::domain::get_bounds(dbm_in, base, ctx.zero);
            let eff_lo = lo.map(|x| x + off as i64);
            let eff_hi = hi.map(|x| x + off as i64 + (access_size - 1));

            let stack_ok = match (eff_lo, eff_hi) {
                (Some(l), Some(h)) => match size {
                    MemSize::U8  => l >= ctx.stack_min && h <= ctx.stack_max,
                    MemSize::U16 => l >= ctx.stack_min && h + 0 <= ctx.stack_max, // Fixed logic
                    MemSize::U32 => l >= ctx.stack_min && h + 0 <= ctx.stack_max,
                    MemSize::U64 => l >= ctx.stack_min && h + 0 <= ctx.stack_max,
                },
                _ => false,
            };

            if !stack_ok {
                println!("Unsafe stack load at pc {}: base {:?}+{}", pc, base, off);
                stats.mark_unsafe_load();
            }
            
            // Stack load -> Scalar
            next_types.set(dst, RegType::ScalarValue);
            forget(&mut dbm, dst);
        }

        // --- PACKET LOGIC (NEW) ---
        PtrToPacket { id: _, range } => {
            let access_end = off as i64 + access_size;
            let mut safe = false;

            // Tier 1: Check Cached Range (Fast, robust to clobbering)
            // Access is safe if (off + size) <= range
            if off >= 0 && (access_end as u64) <= range {
                safe = true;
            } 
            // Tier 2: DBM Fallback (Slow, requires DataEnd to be alive)
            else {
                // Find register holding PacketEnd
                let end_reg_opt = crate::domain::REG_ENV.all().iter().find(|&&r| {
                     matches!(reg_types.get(r), RegType::PtrToPacketEnd)
                });

                if let Some(end_reg) = end_reg_opt {
                    // Check: base + off + size <= end_reg
                    // DBM: base - end_reg <= -(off + size)
                    let bound = -access_end;
                    let (_, ub) = crate::domain::get_bounds(&dbm, base, *end_reg);
                    if let Some(upper) = ub {
                        if upper <= bound {
                            safe = true;
                        }
                    }
                }
            }

            if !safe {
                println!("Unsafe packet load at pc {}: base {:?}+{} (range={})", pc, base, off, range);
                stats.mark_unsafe_load();
            }

            // Packet load -> Scalar
            next_types.set(dst, RegType::ScalarValue);
            forget(&mut dbm, dst);
        }

        // --- CONTEXT LOGIC (Updated to Mint IDs) ---
        PtrToCtx => {
            if let Some(kind) = classify_tc_ctx_field(off, size) {
                match kind {
                    CtxFieldKind::PacketStart => {
                        // MINT NEW ID
                        let new_id = crate::domain::new_packet_id();
                        next_types.set(dst, RegType::PtrToPacket { id: new_id, range: 0 });
                    },
                    CtxFieldKind::PacketEnd => {
                        next_types.set(dst, RegType::PtrToPacketEnd);
                    },
                    CtxFieldKind::PtrToMem { region } => {
                        next_types.set(dst, RegType::PtrToMem { region });
                    },
                    CtxFieldKind::MemEnd { region: _ } => {
                         // Or specific end type if you add one
                         next_types.set(dst, RegType::ScalarValue); 
                    },
                    CtxFieldKind::Scalar => {
                        next_types.set(dst, RegType::ScalarValue);
                    }
                }
            } else {
                next_types.set(dst, RegType::ScalarValue);
            }
            forget(&mut dbm, dst);
        }

        PtrToMem { region: _ } => {
            println!("Memory-region load at pc {}: dst {:?} = *(...)(base {:?}+{})", pc, dst, base, off);
            next_types.set(dst, RegType::ScalarValue);
            forget(&mut dbm, dst);
        }

        _ => {
            println!("Non-stack, non-ctx load at pc {} from base {:?}+{}", pc, base, off);
            stats.mark_unsafe_load();
            next_types.set(dst, RegType::ScalarValue);
            forget(&mut dbm, dst);
        }
    }
    
    vec![(pc + 1, dbm, next_types)]
}

fn transfer_store(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    size: MemSize,
    base: Reg,
    off: i16,
    _src: Reg,
    stats: &mut AnalysisStats,
    reg_types: &RegTypeState,
) -> Vec<(usize, Dbm, RegTypeState)> { // Updated return type
    use crate::domain::RegType;

    let base_ty = reg_types.get(base);
    // Stores do not modify register types (unless they clobber registers, which STX does not)
    let next_types = reg_types.clone();

    let access_size = match size {
        MemSize::U8  => 1,
        MemSize::U16 => 2,
        MemSize::U32 => 4,
        MemSize::U64 => 8,
    };

    match base_ty {
        RegType::PtrToMapValue { offset: map_off, map_idx } => {
             let final_offset = map_off + (off as i64);
             let access_end = final_offset + access_size;

             // 1. Retrieve Map Definition
             let map_limit = if let Some(def) = ctx.map_defs.get(map_idx) {
                 def.value_size as i64
             } else {
                 // Fallback: If map definition is missing, assume a large safe size 
                 // so we can debug the rest of the flow.
                 4096 
             };

             // 2. Bounds Check
             if final_offset >= 0 && access_end <= map_limit {
                 // Safe!
                 return vec![(pc + 1, dbm_in.clone(), next_types)];
             }
             
             // If we are here, it failed. 
             // Check if it failed because we guessed the limit 4096?
             println!("Unsafe map store at pc {}: off {} size {} limit {}", pc, final_offset, access_size, map_limit);
             stats.mark_unsafe_store();
             stats.abort = true;
             vec![]
        }

        RegType::PtrToStack => {
            let (lo, hi) = crate::domain::get_bounds(dbm_in, base, ctx.zero);
            let eff_lo = lo.map(|x| x + off as i64);
            let eff_hi = hi.map(|x| x + off as i64);

            let is_stack_store = match (eff_lo, eff_hi) {
                (Some(l), Some(h)) => {
                    let last = h + (access_size - 1);
                    l >= ctx.stack_min && last <= ctx.stack_max
                }
                _ => false,
            };

            if is_stack_store {
                // Verified stack store
                return vec![(pc + 1, dbm_in.clone(), next_types)];
            }

            println!(
                "Unsafe stack store at pc {}: {:?} to base {:?}+{} (bounds {:?}..{:?})",
                pc, size, base, off, eff_lo, eff_hi
            );
            stats.mark_unsafe_store();
            stats.abort = true;
            vec![]
        }

        // --- NEW: PACKET STORE LOGIC ---
        RegType::PtrToPacket { id: _, range } => {
            let access_end = off as i64 + access_size;
            let mut safe = false;

            // Tier 1: Check Cached Range (Fast)
            if off >= 0 && (access_end as u64) <= range {
                safe = true;
            } 
            // Tier 2: DBM Fallback (Slow)
            else {
                let end_reg_opt = crate::domain::REG_ENV.all().iter().find(|&&r| {
                     matches!(reg_types.get(r), RegType::PtrToPacketEnd)
                });

                if let Some(end_reg) = end_reg_opt {
                    let bound = -access_end;
                    let (_, ub) = get_bounds(dbm_in, base, *end_reg);
                    if let Some(upper) = ub {
                        if upper <= bound {
                            safe = true;
                        }
                    }
                }
            }

            if safe {
                return vec![(pc + 1, dbm_in.clone(), next_types)];
            }

            println!("Unsafe packet store at pc {}: base {:?}+{} (range={})", pc, base, off, range);
            stats.mark_unsafe_store();
            stats.abort = true;
            vec![]
        }

        RegType::PtrToCtx => {
            println!(
                "Ctx store at pc {}: {:?} to base {:?}+{} (ignored for stack cert)",
                pc, size, base, off
            );
            vec![(pc + 1, dbm_in.clone(), next_types)]
        }

        RegType::PtrToMem { .. } => {
            println!(
                "Non-stack pointer store at pc {}: {:?} to base {:?}+{}",
                pc, size, base, off
            );
            vec![(pc + 1, dbm_in.clone(), next_types)]
        }

        other => {
            println!(
                "Unsafe store at pc {}: base {:?}+{} has non-pointer type {:?}",
                pc, base, off, other
            );
            stats.mark_unsafe_store();
            stats.abort = true;
            vec![]
        }
    }
}

fn transfer_call(
    _ctx: &ExecContext,   // Add ctx if needed later
    dbm_in: &Dbm,
    pc: usize,
    helper: u32,
    reg_types: &RegTypeState, // INPUT types (read-only)
) -> Vec<(usize, Dbm, RegTypeState)> {
    let mut dbm = dbm_in.clone();
    let mut next_types = reg_types.clone();

    // 1. Read Arg1 (R1) type from INPUT state
    let r1_type = reg_types.get(Reg::R1);

    // 2. Clobber R1-R5
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        forget(&mut dbm, r);
        next_types.set(r, RegType::ScalarValue);
    }
    forget(&mut dbm, Reg::R0);

    // 3. Set Return Type
    match helper {
        1 => { // bpf_map_lookup_elem
            let map_idx = if let RegType::PtrToMapObject { map_idx } = r1_type {
                map_idx
            } else {
                usize::MAX // Sentinel for "Unknown Map"
            };

            // Return "MapValueOrNull" tagged with the specific Map ID
            let new_id = crate::domain::new_packet_id();
            next_types.set(Reg::R0, RegType::PtrToMapValueOrNull { id: new_id, map_idx });
        }
        _ => {
            next_types.set(Reg::R0, RegType::ScalarValue);
        }
    }

    vec![(pc + 1, dbm, next_types)]
}

/// Single-step semantic transfer: from (pc, dbm_in) to successors
pub fn transfer_instr(
    ctx: &ExecContext,
    dbm_in: &Dbm,
    pc: usize,
    instr: &Instr,
    stats: &mut AnalysisStats,
    reg_types: &RegTypeState,
) -> Vec<(usize, Dbm, RegTypeState)> {
    match instr {
        Instr::MovArg0 { dst } =>
            transfer_mov_arg0(dbm_in, pc, *dst),
        Instr::Alu { width, op, dst, src } =>
            transfer_alu(ctx, dbm_in, pc, *width, *op, *dst, *src, stats, reg_types),
        Instr::Endian { dst, kind } =>
            transfer_endian(ctx, dbm_in, pc, *dst, *kind),
        Instr::If { width, left, op, right, target } =>
            transfer_if(ctx, dbm_in, pc, *width, *left, *op, *right, *target, reg_types),
        Instr::Load { size, dst, base, off } =>
            {
                let base_ty = reg_types.get(*base);
                transfer_load(ctx, dbm_in, pc, *size, *dst, *base, base_ty, *off, stats, reg_types)
            },
        Instr::Store { size, base, off, src } =>
            {
                transfer_store(ctx, dbm_in, pc, *size, *base, *off, *src, stats, reg_types)
            },
        Instr::Call { helper } =>
            transfer_call(ctx, dbm_in, pc, *helper, reg_types),
        Instr::Jmp { target } =>
            vec![(*target, dbm_in.clone(), reg_types.clone())],
        Instr::Exit =>
            vec![],
    }
}

pub fn update_reg_types_for_instr(
    ctx: &ExecContext,
    instr: &Instr,
    types: &mut RegTypeState,
    pc: usize
) {
    match *instr {
        Instr::MovArg0 { dst } => {
            types.set(dst, RegType::PtrToCtx);
        }

        Instr::Alu { width, op, dst, src } => {
            update_alu_types(ctx, pc, types, width, op, dst, src);
        }

        Instr::Load { size, dst, base, off } => {
            update_load_types(types, size, dst, base, off);
        }

        Instr::Call { helper } => {
            update_call_types(types, helper);
        }

        // Stores, Jumps, Exits do not change register types
        Instr::Store { .. } | Instr::Jmp { .. } | Instr::If { .. } | Instr::Exit 
        | Instr::Endian { .. } => {}
    }
}

// -----------------------------------------------------------------------------
// Helper 1: ALU Operations
// -----------------------------------------------------------------------------

fn update_alu_types(
    ctx: &ExecContext,
    pc: usize,
    types: &mut RegTypeState,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: Operand,
) {
    // 32-bit operations (e.g., w1 = w2) generally destroy pointer semantics 
    // because they zero-extend the upper 32 bits.
    if width == Width::W32 {
        types.set(dst, RegType::ScalarValue);
        return;
    }

    match op {
        AluOp::Mov => handle_mov(ctx, pc, types, dst, src),
        AluOp::Add => handle_add(types, dst, src),
        AluOp::Sub => handle_sub(types, dst, src),
        // All other ops (Mul, And, Or, Shl, etc.) result in Scalars
        _ => types.set(dst, RegType::ScalarValue),
    }
}

fn handle_mov(
    ctx: &ExecContext,
    pc: usize,
    types: &mut RegTypeState,
    dst: Reg,
    src: Operand,
) {
    match src {
        Operand::Reg(r) => {
            // Copy type from register
            types.set(dst, types.get(r));
        }
        Operand::Imm(_) => {
            // CHECK FOR RELOCATION!
            // If this is `r1 = 0 ll` AND there is a map relocation at this PC:
            if let Some(&map_idx) = ctx.pc_to_map_idx.get(&pc) {
                // It is a Map Object (struct bpf_map *)
                types.set(dst, RegType::PtrToMapObject { map_idx });
            } else {
                // Otherwise it's just a number
                types.set(dst, RegType::ScalarValue);
            }
        }
    }
}

fn handle_add(types: &mut RegTypeState, dst: Reg, src: Operand) {
    let dst_ty = types.get(dst);
    
    // We only support pointer arithmetic with Immediates (Ptr + K)
    if let (true, Operand::Imm(k)) = (dst_ty.is_pointer(), src) {
        match dst_ty {
            // Packet: Ptr += K shrinks the safe window
            RegType::PtrToPacket { id, range } => {
                let new_range = if k > 0 {
                    range.saturating_sub(k as u64)
                } else {
                    range.saturating_add(k.wrapping_neg() as u64)
                };
                types.set(dst, RegType::PtrToPacket { id, range: new_range });
            }
            // Map: Ptr += K shifts the offset
            RegType::PtrToMapValue { offset, map_idx } => {
                types.set(dst, RegType::PtrToMapValue { offset: offset + k, map_idx });
            }
            // Others (Ctx, Stack): Preserve type, assume DBM tracks numeric bounds
            _ => types.set(dst, dst_ty),
        }
    } else {
        // Ptr + Reg or Scalar + ... results in Scalar
        types.set(dst, RegType::ScalarValue);
    }
}

fn handle_sub(types: &mut RegTypeState, dst: Reg, src: Operand) {
    let dst_ty = types.get(dst);

    if let (true, Operand::Imm(k)) = (dst_ty.is_pointer(), src) {
        match dst_ty {
            // Packet: Ptr -= K (moving backwards) grows the safe window
            RegType::PtrToPacket { id, range } => {
                let new_range = if k > 0 {
                    range.saturating_add(k as u64)
                } else {
                    range.saturating_sub(k.wrapping_neg() as u64)
                };
                types.set(dst, RegType::PtrToPacket { id, range: new_range });
            }
            // Map: Ptr -= K shifts offset backwards
            RegType::PtrToMapValue { offset, map_idx } => {
                types.set(dst, RegType::PtrToMapValue { offset: offset - k, map_idx });
            }
            _ => types.set(dst, dst_ty),
        }
    } else {
        types.set(dst, RegType::ScalarValue);
    }
}

// -----------------------------------------------------------------------------
// Helper 2: Load Operations (Context Classification)
// -----------------------------------------------------------------------------

fn update_load_types(
    types: &mut RegTypeState,
    size: MemSize,
    dst: Reg,
    base: Reg,
    off: i16,
) {
    let base_ty = types.get(base);

    match base_ty {
        RegType::PtrToCtx => {
            // Consult the model to see if we are loading a special pointer
            if let Some(kind) = classify_tc_ctx_field(off, size) {
                match kind {
                    CtxFieldKind::PacketStart => {
                        // Mint new ID for Packet pointers
                        let new_id = crate::domain::new_packet_id();
                        types.set(dst, RegType::PtrToPacket { id: new_id, range: 0 });
                    }
                    CtxFieldKind::PacketEnd => {
                        types.set(dst, RegType::PtrToPacketEnd);
                    }
                    CtxFieldKind::PtrToMem { region } => {
                        types.set(dst, RegType::PtrToMem { region });
                    }
                    // Everything else from context is scalar
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
        // Loading FROM Stack/Packet/Map results in data (Scalar)
        // (Unless we support spilling pointers to stack, which we don't yet)
        _ => types.set(dst, RegType::ScalarValue),
    }
}

// -----------------------------------------------------------------------------
// Helper 3: Call Operations (Helpers)
// -----------------------------------------------------------------------------

fn update_call_types(types: &mut RegTypeState, helper: u32) {
    // 1. Clobber Caller-Saved Registers (R1-R5)
    // The helper function uses these, so we lose whatever was in them.
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        types.set(r, RegType::ScalarValue);
    }

    // 2. Set Return Value (R0) type based on helper ID
    match helper {
        1 => { // bpf_map_lookup_elem
            // Returns a pointer that might be NULL. 
            // We assign a fresh ID to track the future NULL check.
            let new_id = crate::domain::new_packet_id();
            types.set(Reg::R0, RegType::PtrToMapValueOrNull { id: new_id, map_idx: 0 });
        }
        // Add other helpers here (e.g. bpf_get_smp_processor_id returns scalar)
        _ => {
            types.set(Reg::R0, RegType::ScalarValue);
        }
    }
}

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    stats: &mut AnalysisStats,
) -> Vec<Dbm> {
    let n = prog.instrs.len();

    // Numeric state per PC
    let mut states: Vec<Option<Dbm>> = vec![None; n];
    // Register-type state per PC
    let mut type_states: Vec<Option<RegTypeState>> = vec![None; n];

    // Entry register types, loosely mirroring kernel:
    let mut entry_types = RegTypeState::new_not_init();

    // R1 is PTR_TO_CTX at entry
    entry_types.set(Reg::R1, RegType::PtrToCtx);

    // R10 is frame pointer / stack base
    entry_types.set(ctx.r10, RegType::PtrToStack);

    // R0 as scalar return value placeholder
    entry_types.set(Reg::R0, RegType::ScalarValue);

    let mut worklist = VecDeque::new();

    states[0] = Some(entry_dbm);
    type_states[0] = Some(entry_types);
    worklist.push_back(0);

    while let Some(pc) = worklist.pop_front() {
        if stats.abort {
            println!("Analysis aborted due to previous errors.");
            break;
        }

        let instr = &prog.instrs[pc];
        let in_dbm = states[pc].as_ref().unwrap();
        let in_types = type_states[pc].expect("type state must exist when DBM state exists");

        println!("=== PC {} ===", pc);
        println!("Instr: {}", instr);

        // 1) Print *input* DBM state
        // println!("IN:");
        // in_dbm.dump_matrix();

        // 1b) Print *input* register types
        println!("RegTypes IN:");
        // for (r, ty) in in_types.iter_regs() {
        //     println!("  {:>3}: {:?}", r.name(), ty);
        // }
        // println!();

        // 2) Numeric transfer: note we pass &in_types into transfer_instr
        let succs = transfer_instr(ctx, in_dbm, pc, instr, stats, &in_types);

        if stats.abort {
            println!("Analysis aborted due to previous errors.");
            break;
        }

        // 3) Print *output* numeric states for each successor
        for (succ_pc, succ_dbm, _succ_types) in &succs {
            println!("OUT → PC {}:", succ_pc);
            // succ_dbm.dump_matrix();
        }

        // 4) Dataflow propagation: DBM + RegType
        for (succ_pc, succ_dbm, _succ_types) in succs {
            if succ_pc >= n {
                continue;
            }

            // 1. Update Types for Edge
            // Compute edge types after this instruction starting from in_types.
            let mut edge_types = in_types;
            update_reg_types_for_instr(ctx, instr, &mut edge_types, succ_pc);

            // 2. Refine Types (Flow-sensitive)
            refine_branch_types(instr, succ_pc, &succ_dbm, &mut edge_types);

            match (&mut states[succ_pc], &mut type_states[succ_pc]) {
                (slot_dbm @ None, slot_types @ None) => {
                    // First time reaching this pc
                    *slot_dbm = Some(succ_dbm);
                    *slot_types = Some(edge_types);
                    worklist.push_back(succ_pc);
                }
                (Some(existing_dbm), Some(existing_types)) => {
                    let joined_dbm = existing_dbm.join(&succ_dbm);
                    let dbm_changed = !dbm_equals(existing_dbm, &joined_dbm);
                    *existing_dbm = joined_dbm;

                    let types_changed = existing_types.join_in_place(&edge_types);

                    if dbm_changed || types_changed {
                        worklist.push_back(succ_pc);
                    }
                }
                _ => {
                    // Invariant: DBM and type state presence must match.
                    panic!(
                        "Inconsistent state: DBM and type state presence differ at pc {}",
                        succ_pc
                    );
                }
            }
        }
    }

    states
        .into_iter()
        .map(|opt| opt.unwrap_or_else(|| Dbm::new(REG_ENV.len())))
        .collect()
}


// pub fn analyze_program_for_file(
//     path: &std::path::Path,
// ) -> Result<AnalysisStats, Box<dyn std::error::Error>> {
//     let prog = load_program_from_elf(
//         path.to_str().ok_or("Invalid path")?,
//         ".text",
//     );

//     let mut stats = AnalysisStats::default();

//     let ctx = ExecContext {
//         zero: Reg::Zero,
//         r10: Reg::R10,
//         stack_min: -512,
//         stack_max: -1,
//     };

//     let mut entry = Dbm::new(REG_ENV.len());
//     crate::domain::assign_zero(&mut entry, ctx.r10, ctx.zero);

//     analyze_program(&ctx, &prog, entry, &mut stats);

//     Ok(stats)
// }
