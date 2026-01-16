// src/analysis/transfer.rs
use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::{RegType, TypeState, new_packet_id};
use crate::ast::{Instr, AluOp, CmpOp, Operand, Width, EndianKind, MemSize, ProgramKind};
use crate::zone::domain::{Reg, forget, get_bounds, 
    assign_add_imm, assign_add_reg, assign_eq, 
    assume_eq_const, assume_ge_const, assume_le_const, 
    assume_less_than, assume_ge_var, assume_le_var, 
    assume_gt_var, assume_le_var_plus_const, 
    assign_zero, assign_mul_imm, assign_and_mask,
    assign_div_imm, assign_div_reg,
    bit_and_const, assign_neg
};
use crate::analysis::access;
use crate::zone::domain::proven_u32_range;
use crate::parsing::ctx_model::{classify_tc_ctx_field, CtxFieldKind, classify_xdp_ctx_field};
use crate::analysis::env::VerificationError;
use crate::zone::dbm::Dbm;
use crate::analysis::constants;

pub fn transfer(
    env: &mut VerifierEnv,
    mut state: State,
    instr: &Instr,
) -> Vec<State> {
    
    // 1. Mark as Seen
    if state.pc < env.insn_aux_data.len() {
        env.insn_aux_data[state.pc].seen = true;
    }

    match instr {
        Instr::MovArg0 { dst } => transfer_mov_arg0(state, *dst),
        Instr::Alu { width, op, dst, src } => transfer_alu(env, state, *width, *op, *dst, src.clone()),
        Instr::Endian { dst, kind } => transfer_endian(env, state, *dst, *kind),
        Instr::If { width, left, op, right, target } => transfer_if(env, state, *width, *left, *op, right.clone(), *target),
        Instr::Load { size, dst, base, off } => {
            access::check_load(env, &state, *base, *size, *off);
            update_load_types(env, &mut state.types, *size, *dst, *base, *off);
            forget(&mut state.dbm, *dst);
            state.pc += 1;
            vec![state]
        },
        Instr::Store { size, base, off, src } => {
            access::check_store(env, &state, *base, *size, *off);
            let src_type = state.types.get(*src);
            let base_type = state.types.get(*base);
            update_store_types(&mut state.types, src_type, *size, base_type, *off);
            state.pc += 1;
            vec![state]
        },
        Instr::AtomicAdd { size, base, off, src: _ } => {
            // 1. Safety Check: Identical to Store
            // (Must be valid writable memory)
            access::check_store(env, &state, *base, *size, *off);
            if env.failed() { return vec![]; }
            // 2. State Update:
            // An Atomic Add results in a number (Scalar).
            // We treat this as "Storing a Scalar" to that location.
            // We reuse update_store_types, passing ScalarValue as the "source type".
            let base_type = state.types.get(*base);
            update_store_types(&mut state.types, RegType::ScalarValue, *size, base_type, *off);
            state.pc += 1;
            vec![state]
        },
        Instr::Call { helper } => transfer_call(env, state, *helper),
        Instr::Jmp { target } => {
            state.pc = *target;
            vec![state]
        },
        Instr::Exit => vec![],
    }
}

fn transfer_mov_arg0(mut state: State, dst: Reg) -> Vec<State> {
    forget(&mut state.dbm, dst);
    state.types.set(dst, RegType::PtrToCtx);
    state.pc += 1;
    vec![state]
}

fn transfer_alu(
    env: &mut VerifierEnv,
    mut state: State,
    width: Width,
    op: AluOp,
    dst: Reg,
    src: Operand,
) -> Vec<State> {
    let ctx = env.ctx;
    // Clone input types for logic that needs original values
    let in_types = state.types.clone();
    
    update_alu_types(env, &in_types, &mut state.types, width, op, dst, &src, state.pc);

    let dbm = &mut state.dbm;
    match op {
        AluOp::Mov => {
            match src {
                Operand::Reg(r) => {
                    if width == Width::W32 {
                        forget(dbm, dst);
                        assume_ge_const(dbm, dst, ctx.zero, 0);
                        assume_le_const(dbm, dst, ctx.zero, 0xffff_ffff);
                    } else {
                        if r == ctx.r10 { assign_zero(dbm, dst, ctx.zero); } 
                        else { assign_eq(dbm, dst, r); }
                    }
                }
                Operand::Imm(c) => {
                    let c = if width == Width::W32 { (c as u32) as i64 } else { c };
                    forget(dbm, dst);
                    assume_le_const(dbm, dst, ctx.zero, c);
                    assume_ge_const(dbm, dst, ctx.zero, c);
                }
            }
        }
        AluOp::Add => {
            match src {
                Operand::Imm(c) => assign_add_imm(dbm, dst, c),
                Operand::Reg(r) => assign_add_reg(dbm, dst, r, ctx.zero),
            }
        }
        AluOp::Sub => {
            match src {
                Operand::Imm(c) => assign_add_imm(dbm, dst, -c),
                Operand::Reg(_r) => forget(dbm, dst), 
            }
        }
        AluOp::And => {
            let (old_lo, old_hi) = get_bounds(dbm, dst, ctx.zero);
            forget(dbm, dst);
            if let Operand::Imm(mask) = src {
                let mask = if width == Width::W32 { (mask as u32) as i64 } else { mask };
                if mask >= 0 {
                    assign_and_mask(dbm, dst, mask, ctx.zero);
                } else if let (Some(l), Some(h)) = (old_lo, old_hi) {
                    if l >= 0 {
                        assume_ge_const(dbm, dst, ctx.zero, 0);
                        assume_le_const(dbm, dst, ctx.zero, h);
                    }
                }
            } else if let (Some(l), Some(h)) = (old_lo, old_hi) {
                 if l >= 0 {
                    assume_ge_const(dbm, dst, ctx.zero, 0);
                    assume_le_const(dbm, dst, ctx.zero, h);
                 }
            }
        }
        AluOp::Or | AluOp::Xor | AluOp::Shl | AluOp::Arsh => forget(dbm, dst),
        AluOp::Neg => {
            // 1. Apply Negate Logic (swaps bounds)
            assign_neg(&mut state.dbm, dst);

            // 2. Handle 32-bit Truncation/Extension
            // If this was NEG32 (w0 = -w0), the result must be zero-extended.
            // Example: -1 becomes 0xFFFFFFFF (4294967295)
            if width == Width::W32 {
                bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
            }
            
            // 3. Type Update
            state.types.set(dst, RegType::ScalarValue);
        },
        AluOp::Shr => {
             match src {
                Operand::Imm(k) => {
                    let bits = if width == Width::W32 { 32u32 } else { 64u32 };
                    let k = (k as u32).min(bits);
                    forget(dbm, dst);
                    assume_ge_const(dbm, dst, ctx.zero, 0);
                    if k < bits {
                        let ub: i64 = ((1u128 << (bits - k)) - 1) as i64;
                        assume_le_const(dbm, dst, ctx.zero, ub);
                    } else {
                        assume_eq_const(dbm, dst, ctx.zero, 0);
                    }
                }
                Operand::Reg(_) => forget(dbm, dst),
            }
        }
        AluOp::Mul => {
             match src {
                Operand::Imm(c) => assign_mul_imm(dbm, dst, c, ctx.zero),
                Operand::Reg(_) => forget(dbm, dst),
            }
        }
        AluOp::Mod => {
             match src {
                Operand::Imm(c) => {
                    if c > 0 {
                        forget(dbm, dst);
                        assume_ge_const(dbm, dst, ctx.zero, 0);
                        assume_le_const(dbm, dst, ctx.zero, c - 1);
                    } else { forget(dbm, dst); }
                }
                Operand::Reg(_) => forget(dbm, dst),
            }
        }
        AluOp::Div => {
            // 1. Check for Division by Zero
            let is_zero = match src {
                Operand::Imm(k) => k == 0,
                Operand::Reg(r) => {
                    // Check if register is strictly 0
                    let (lo, hi) = get_bounds(&state.dbm, r, env.ctx.zero);
                    match (lo, hi) {
                        (Some(0), Some(0)) => true, // Definitely zero
                        _ => false, // Could be non-zero (or unknown)
                    }
                }
            };

            if is_zero {
                env.fail(VerificationError::DivideByZero { pc: state.pc });
                return vec![];
            }

            // 2. Apply Domain Logic
            match src {
                Operand::Imm(imm) => {
                    assign_div_imm(&mut state.dbm, dst, imm);
                },
                Operand::Reg(r_src) => {
                    assign_div_reg(&mut state.dbm, dst, r_src);
                }
            }

            // 3. Handle 32-bit truncation
            // If this was a 32-bit div (w0 /= w1), the upper 32-bits are zeroed.
            if width == Width::W32 {
                bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
            }
            
            // 4. Update Type to Scalar
            // Pointers cannot be divided.
            state.types.set(dst, RegType::ScalarValue);
        },
    }

    if state.dbm.is_inconsistent() {
        env.fail(VerificationError::DbmInconsistent { pc: state.pc });
        println!("[Verifier] DBM became inconsistent at pc {}", state.pc);
        vec![]
    } else {
        state.pc += 1;
        vec![state]
    }
}

fn transfer_endian(
    env: &VerifierEnv,
    mut state: State,
    dst: Reg,
    kind: EndianKind,
) -> Vec<State> {
    forget(&mut state.dbm, dst);
    let (lo, hi) = match kind {
        EndianKind::Be16 => (0i64, 0x0000_ffff),
        EndianKind::Be32 => (0i64, 0xffff_ffff),
        EndianKind::Be64 => {
             state.types.set(dst, RegType::ScalarValue);
             state.pc += 1;
             return vec![state];
        }
    };
    assume_ge_const(&mut state.dbm, dst, env.ctx.zero, lo);
    assume_le_const(&mut state.dbm, dst, env.ctx.zero, hi);
    state.types.set(dst, RegType::ScalarValue);
    state.pc += 1;
    vec![state]
}

fn transfer_if(
    env: &VerifierEnv,
    state: State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: Operand,
    target: usize,
) -> Vec<State> {
    let ctx = env.ctx;
    let mut out = Vec::new();

    let mut state_then = state.clone();
    let mut state_else = state.clone();

    state_then.pc = target;
    state_else.pc = state.pc + 1;

    let dbm_in = &state.dbm;

    // 1. DBM Literal Optimization
    match (op, &right) {
        (CmpOp::Ne, Operand::Imm(imm)) => {
            assume_eq_const(&mut state_else.dbm, left, ctx.zero, *imm);
            let (lo, hi) = get_bounds(dbm_in, left, ctx.zero);
            if let (Some(l), Some(h)) = (lo, hi) {
                if l == *imm && h == *imm { assume_less_than(&mut state_then.dbm, ctx.zero, ctx.zero, 0); }
            }
            // Null check refinement: if Rx != 0 goto target
            // Then branch: Rx != 0, convert nullable to non-null
            // Else branch: Rx == 0, stays nullable
            if *imm == 0 {
                let left_ty = state.types.get(left);
                if let Some(non_null) = left_ty.to_non_null() {
                    state_then.types.set(left, non_null);
                }
            }
        }
        (CmpOp::Eq, Operand::Imm(imm)) => {
            assume_eq_const(&mut state_then.dbm, left, ctx.zero, *imm);
            let (lo, hi) = get_bounds(dbm_in, left, ctx.zero);
            if let (Some(l), Some(h)) = (lo, hi) {
                if l == *imm && h == *imm { assume_less_than(&mut state_else.dbm, ctx.zero, ctx.zero, 0); }
            }
            // Null check refinement: if Rx == 0 goto target
            // Then branch: Rx == 0, stays nullable
            // Else branch: Rx != 0, convert nullable to non-null
            if *imm == 0 {
                let left_ty = state.types.get(left);
                if let Some(non_null) = left_ty.to_non_null() {
                    state_else.types.set(left, non_null);
                }
            }
        }
        _ => {}
    }

    // 2. 32-bit Logic Fallback
    // Note: Eq/Ne with immediate 0 is safe regardless of bit width, and constraints
    // were already applied in section 1. We must NOT early-return for these cases,
    // otherwise we bypass the is_inconsistent() check at the end.
    if width == Width::W32 {
        if let Operand::Imm(c) = &right {
            let is_zero_check = (*c == 0) && matches!(op, CmpOp::Eq | CmpOp::Ne);
            if !is_zero_check
               && matches!(op, CmpOp::Eq | CmpOp::Ne | CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt) 
               && !proven_u32_range(dbm_in, left, ctx.zero) {
                return vec![state_else, state_then];
            }
        } else {
            return vec![state_else, state_then];
        }
    }

    // 3. Register Comparisons
    match (op, &right) {
        (CmpOp::UGe, Operand::Imm(c)) => {
            assume_ge_const(&mut state_then.dbm, left, ctx.zero, *c);
            assume_less_than(&mut state_else.dbm, left, ctx.zero, *c);
        }
        (CmpOp::ULe, Operand::Imm(c)) => {
            assume_le_const(&mut state_then.dbm, left, ctx.zero, *c);
            assume_ge_const(&mut state_else.dbm, left, ctx.zero, c + 1);
        }
        (CmpOp::UGt, Operand::Imm(c)) => {
            assume_ge_const(&mut state_then.dbm, left, ctx.zero, c + 1);
            assume_le_const(&mut state_else.dbm, left, ctx.zero, *c);
        }
        (CmpOp::ULt, Operand::Imm(c)) => {
            assume_less_than(&mut state_then.dbm, left, ctx.zero, *c);
            assume_ge_const(&mut state_else.dbm, left, ctx.zero, *c);
        }
        (cmp_op, Operand::Reg(r)) => {
            let right_reg = *r;
            match cmp_op {
                CmpOp::UGe => { 
                    assume_ge_var(&mut state_then.dbm, left, right_reg);
                    assume_le_var_plus_const(&mut state_else.dbm, left, right_reg, -1);
                }
                CmpOp::ULe => { 
                    assume_le_var(&mut state_then.dbm, left, right_reg);
                    assume_gt_var(&mut state_else.dbm, left, right_reg);
                }
                CmpOp::UGt => { 
                    assume_gt_var(&mut state_then.dbm, left, right_reg);
                    assume_le_var(&mut state_else.dbm, left, right_reg);
                }
                CmpOp::ULt => { 
                    assume_le_var_plus_const(&mut state_then.dbm, left, right_reg, -1);
                    assume_ge_var(&mut state_else.dbm, left, right_reg);
                }
                _ => {}
            }
            // Packet Refinement
             match cmp_op {
                CmpOp::ULe | CmpOp::ULt => {
                    refine_packet_ranges(&state_then.dbm, &mut state_then.types, left, right_reg);
                    refine_packet_ranges(&state_then.dbm, &mut state_then.types, right_reg, left);
                }
                _ => {}
            }
            match cmp_op {
                CmpOp::UGt | CmpOp::UGe => {
                    refine_packet_ranges(&state_else.dbm, &mut state_else.types, left, right_reg);
                }
                CmpOp::ULt => {
                    refine_packet_ranges(&state_else.dbm, &mut state_else.types, right_reg, left);
                }
                _ => {}
            }
        }
        _ => {}
    }

    // 4. Branch Type Refinement
    refine_branch(&mut state_then.types, &state_then.dbm, &Instr::If { width, left, op, right: right.clone(), target }, true);
    refine_branch(&mut state_else.types, &state_else.dbm, &Instr::If { width, left, op, right: right.clone(), target }, false);

    if !state_else.dbm.is_inconsistent() { out.push(state_else); }
    if !state_then.dbm.is_inconsistent() { out.push(state_then); }
    out
}

fn transfer_call(
    env: &VerifierEnv,
    mut state: State,
    helper: u32,
) -> Vec<State> {
    let in_types = state.types.clone();
    let ctx = env.ctx;
    let pc = state.pc;
    
    // ========================================================================
    // SPECIAL CASE: bpf_tail_call
    // 
    // Semantics:
    //   - SUCCESS: Jump to target program, NEVER RETURNS (like exit)
    //   - FAILURE: Falls through to next instruction
    //
    // We only model the FAILURE path. Success means execution went elsewhere.
    // ========================================================================
    if helper == constants::BPF_TAIL_CALL {
        // Validate arguments (optional warnings)
        if !matches!(in_types.get(Reg::R1), RegType::PtrToCtx) {
            println!("[Verifier] Warning: tail_call R1 should be PTR_TO_CTX at pc {}", pc);
        }
        if !matches!(in_types.get(Reg::R2), RegType::PtrToMapObject { .. }) {
            println!("[Verifier] Warning: tail_call R2 should be PTR_TO_MAP at pc {}", pc);
        }
        
        // Update types (clobber caller-saved, R0 = scalar)
        update_call_types(&in_types, &mut state.types, helper);
        
        // Forget caller-saved in DBM
        for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            forget(&mut state.dbm, r);
        }
        
        // Return only the failure path (fall through)
        state.pc += 1;
        return vec![state];
    }
    
    // ========================================================================
    // Normal helper handling
    // ========================================================================

    // 1. Update types
    update_call_types(&in_types, &mut state.types, helper);
    
    // 2. Update DBM - forget caller-saved registers
    for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        forget(&mut state.dbm, r);
    }
    
    // 3. Apply return value bounds for specific helpers
    match helper {
        constants::BPF_REDIRECT => {
            // Returns TC_ACT_* (0-7)
            assume_ge_const(&mut state.dbm, Reg::R0, ctx.zero, 0);
            assume_le_const(&mut state.dbm, Reg::R0, ctx.zero, 7);
        }
        constants::BPF_FIB_LOOKUP => {
            // Returns BPF_FIB_LKUP_RET_* (0-8)
            assume_ge_const(&mut state.dbm, Reg::R0, ctx.zero, 0);
            assume_le_const(&mut state.dbm, Reg::R0, ctx.zero, 8);
        }
        constants::BPF_MAP_UPDATE_ELEM | 
        constants::BPF_MAP_DELETE_ELEM |
        constants::BPF_SKB_STORE_BYTES |
        constants::BPF_XDP_ADJUST_HEAD => {
            // Returns 0 on success, negative on error
            // Could add bounds but being conservative for now
        }
        _ => {}
    }
    
    // 4. Forget packet pointer DBM entries if they were invalidated
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            if r != Reg::R10 {
                match in_types.get(r) {
                    RegType::PtrToPacket { .. } | RegType::PtrToPacketEnd => {
                        forget(&mut state.dbm, r);
                    }
                    _ => {}
                }
            }
        }
    }
    
    // 5. Advance PC and return
    state.pc += 1;
    vec![state]
}

// --- Helper Functions for Type Updates ---

fn update_alu_types(
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
                    if *r == env.ctx.r10 {
                        types.set(dst, RegType::PtrToStack { offset: 0 });
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
                    (RegType::PtrToPacket { id, range }, Operand::Imm(k)) => {
                        let new_range = if *k > 0 { range.saturating_sub(*k as u64) } else { range.saturating_add(k.wrapping_neg() as u64) };
                        types.set(dst, RegType::PtrToPacket { id, range: new_range });
                    },
                    (RegType::PtrToStack { offset }, Operand::Imm(k)) => {
                        types.set(dst, RegType::PtrToStack { offset: offset + k });
                    },
                    (RegType::PtrToStack { .. }, Operand::Reg(_)) => {
                        // Variable offset - we lose precise tracking
                        types.set(dst, RegType::ScalarValue);
                    },
                    (RegType::PtrToCtx, Operand::Imm(_)) => {
                        types.set(dst, RegType::PtrToCtx);
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
                    RegType::PtrToPacket { id, range } => {
                        let new_range = if *k > 0 { range.saturating_add(*k as u64) } else { range.saturating_sub(k.wrapping_neg() as u64) };
                        types.set(dst, RegType::PtrToPacket { id, range: new_range });
                    },
                    RegType::PtrToStack { offset } => {
                        types.set(dst, RegType::PtrToStack { offset: offset - k });
                    },
                    RegType::PtrToCtx => {
                        types.set(dst, RegType::PtrToCtx);
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

fn update_load_types(env: &VerifierEnv, types: &mut TypeState, size: MemSize, dst: Reg, base: Reg, off: i16) {
    let base_ty = types.get(base);
    match base_ty {
        RegType::PtrToCtx => {
            let kind = match env.ctx.prog_kind {
                ProgramKind::Xdp => classify_xdp_ctx_field(off, size),
                ProgramKind::Tc => classify_tc_ctx_field(off, size)
            };
            if let Some(kind) = kind {
                match kind {
                    CtxFieldKind::PacketStart => {
                        let new_id = new_packet_id();
                        types.set(dst, RegType::PtrToPacket { id: new_id, range: 0 });
                    }
                    CtxFieldKind::PacketEnd => {
                        types.set(dst, RegType::PtrToPacketEnd);
                    }
                    CtxFieldKind::PtrToMem { region } => {
                        types.set(dst, RegType::PtrToMem { region });
                    }
                    _ => types.set(dst, RegType::ScalarValue),
                }
            } else {
                types.set(dst, RegType::ScalarValue);
            }
        }
        RegType::PtrToStack { offset: base_offset } => {
            let actual_slot = base_offset + (off as i64);
            if size == MemSize::U64 { 
                types.set(dst, types.get_stack(actual_slot as i16)); 
            } else { 
                types.set(dst, RegType::ScalarValue); 
            }
        }
        _ => types.set(dst, RegType::ScalarValue),
    }
}

fn update_store_types(types: &mut TypeState, src_type: RegType, size: MemSize, base_type: RegType, off: i16) {
    let stack_slot = match base_type {
        RegType::PtrToStack { offset } => Some(offset + (off as i64)),
        _ => None,
    };
    
    if let Some(slot) = stack_slot {
        if size == MemSize::U64 {
            types.set_stack(slot as i16, src_type);
        } else {
            types.stack.remove(&(slot as i16));
        }
    }
}

/// Checks if a helper invalidates packet pointers.
fn helper_invalidates_packets(helper: u32) -> bool {
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
fn invalidate_stack_packet_pointers(types: &mut TypeState) {
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

// ============================================================================
// Type Update Logic (separate function, matching existing pattern)
// ============================================================================

fn update_call_types(in_types: &TypeState, types: &mut TypeState, helper: u32) {
    // 1. Clobber caller-saved registers
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        types.set(r, RegType::ScalarValue);
    }
    
    // 2. Set R0 based on helper return type
    match helper {
        constants::BPF_MAP_LOOKUP_ELEM => {
            let map_idx = match in_types.get(Reg::R1) {
                RegType::PtrToMapObject { map_idx } => map_idx,
                _ => 0,
            };
            let id = new_packet_id();
            types.set(Reg::R0, RegType::PtrToMapValueOrNull { id, map_idx });
        }
        
        // Socket lookup helpers - return PTR_TO_SOCKET_OR_NULL
        constants::BPF_SK_LOOKUP_TCP | constants::BPF_SK_LOOKUP_UDP => {
            let id = new_packet_id();
            types.set(Reg::R0, RegType::PtrToSocketOrNull { id });
        }
        
        // SKC lookup - returns PTR_TO_SOCK_COMMON_OR_NULL
        constants::BPF_SKC_LOOKUP_TCP => {
            let id = new_packet_id();
            types.set(Reg::R0, RegType::PtrToSockCommonOrNull { id });
        }
        
        // SKC to TCP sock conversion - returns PTR_TO_TCP_SOCK_OR_NULL
        constants::BPF_SKC_TO_TCP_SOCK | 
        constants::BPF_SKC_TO_TCP6_SOCK |
        constants::BPF_SKC_TO_TCP_TIMEWAIT_SOCK |
        constants::BPF_SKC_TO_TCP_REQUEST_SOCK => {
            let id = new_packet_id();
            types.set(Reg::R0, RegType::PtrToTcpSockOrNull { id });
        }
        
        // SKC to UDP/Unix - return SOCK_COMMON for now (simplified)
        constants::BPF_SKC_TO_UDP6_SOCK |
        constants::BPF_SKC_TO_UNIX_SOCK => {
            let id = new_packet_id();
            types.set(Reg::R0, RegType::PtrToSockCommonOrNull { id });
        }
        
        // tail_call: R0 is undefined on failure path
        constants::BPF_TAIL_CALL => {
            types.set(Reg::R0, RegType::ScalarValue);
        }
        
        _ => {
            types.set(Reg::R0, RegType::ScalarValue);
        }
    }
    
    // 3. Invalidate packet pointers if needed
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            match types.get(r) {
                RegType::PtrToPacket { .. } | RegType::PtrToPacketEnd => {
                    types.set(r, RegType::ScalarValue);
                }
                _ => {}
            }
        }
        invalidate_stack_packet_pointers(types);
    }
}

// --- Type Refinement Logic ---

/// Refines the safe access range of packet pointers based on numerical constraints.
///
/// This function bridges the Numerical Domain (DBM) and the Type System. It queries
/// the DBM to determine the distance between a packet pointer and the packet end register.
/// If the DBM proves that `pointer <= end - K`, then `K` bytes are safe to access.
///
/// This function handles aliasing: if multiple registers or stack slots point to the
/// same packet ID, they are all updated with the newly discovered safe range.
///
/// # Arguments
///
/// * `dbm` - The Difference Bound Matrix containing numerical constraints (e.g., `r1 < r2`).
/// * `types` - The mutable type state to update with new ranges.
/// * `packet_reg` - The register holding the packet pointer being compared.
/// * `end_reg` - The register holding the pointer to the end of the packet (`PtrToPacketEnd`).
fn refine_packet_ranges(dbm: &Dbm, types: &mut TypeState, packet_reg: Reg, end_reg: Reg) {
    let target_id = match types.get(packet_reg) {
        RegType::PtrToPacket { id, .. } => id,
        _ => return, 
    };
    let mut max_new_range = 0;
    for r in crate::zone::domain::Reg::ALL {
        if let RegType::PtrToPacket { id, range } = types.get(r) {
            if id == target_id {
                let dist = dbm.get(r, end_reg);
                if dist < crate::zone::dbm::INF {
                    if dist <= 0 {
                        let safe_bytes = dist.checked_abs().unwrap_or(0) as u64;
                        if safe_bytes > range {
                            types.set(r, RegType::PtrToPacket { id, range: safe_bytes });
                            if safe_bytes > max_new_range { max_new_range = safe_bytes; }
                        } else if range > max_new_range { max_new_range = range; }
                    }
                }
            }
        }
    }
    if max_new_range > 0 {
        let stack_keys: Vec<i16> = types.stack.keys().cloned().collect();
        for k in stack_keys {
            if let RegType::PtrToPacket { id, range } = types.get_stack(k) {
                if id == target_id && max_new_range > range {
                    types.set_stack(k, RegType::PtrToPacket { id, range: max_new_range });
                }
            }
        }
    }
}

/// Refines register types based on the outcome of a conditional branch.
///
/// This function analyzes the branch condition to promote types from "Unsafe" or "Nullable"
/// to "Safe". Specifically, it handles NULL checks for map values.
///
/// For example, given `if r0 != 0 goto Label`:
/// * In the **Taken** path (`branch_taken = true`), `r0` is known to be non-zero, so it is promoted to a safe pointer.
/// * In the **Fallthrough** path, `r0` is zero (NULL).
///
/// Conversely, given `if r0 == 0 goto Label`:
/// * In the **Fallthrough** path (`branch_taken = false`), `r0` is known to be non-zero.
///
/// # Arguments
///
/// * `types` - The mutable type state to update.
/// * `_dbm` - The DBM (currently unused, reserved for future range-based refinements).
/// * `instr` - The `If` instruction causing the branch.
/// * `branch_taken` - `true` if analyzing the path where the jump occurs; `false` if analyzing the fallthrough.
fn refine_branch(
    types: &mut TypeState, 
    _dbm: &Dbm, 
    instr: &Instr, 
    branch_taken: bool // True if we are analyzing the branch-taken path, False if fallthrough
) {
    match instr {
        Instr::If { op, left, right: Operand::Imm(0), .. } => {
            match op {
                CmpOp::Ne => {
                    // if (reg != 0) goto Target;
                    // Taken (True) -> reg != 0 -> SAFE
                    if branch_taken { maybe_promote_map_val(types, *left); }
                },
                CmpOp::Eq => {
                    // if (reg == 0) goto Target;
                    // Fallthrough (False) -> reg != 0 -> SAFE
                    if !branch_taken { maybe_promote_map_val(types, *left); }
                },
                _ => {}
            }
        },
        _ => {}
    }
}

/// Promotes a Nullable Map Pointer to a Safe Map Pointer.
///
/// This helper function is called when a register is proven to be non-zero (non-NULL).
/// It transitions a register from `RegType::PtrToMapValueOrNull` to `RegType::PtrToMapValue`.
///
/// # Aliasing
/// This function scans **all** registers and **all** stack slots. Any location holding
/// a pointer with the same unique ID as `reg` is also promoted. This ensures that verifying
/// one alias (e.g., `if r1 != 0`) validates all copies of that pointer (e.g., `r2 = r1`).
///
/// # Arguments
///
/// * `types` - The mutable type state to update.
/// * `reg` - The register that was validated as non-null.
fn maybe_promote_map_val(types: &mut TypeState, reg: Reg) {
    let (target_id, _target_map_idx) = match types.get(reg) {
        RegType::PtrToMapValueOrNull { id, map_idx } => (id, map_idx),
        _ => return,
    };
    for r in crate::zone::domain::Reg::ALL {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = types.get(r) {
            if id == target_id {
                types.set(r, RegType::PtrToMapValue { offset: Some(0), map_idx });
            }
        }
    }
    let stack_keys: Vec<i16> = types.stack.keys().cloned().collect();
    for k in stack_keys {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = types.get_stack(k) {
            if id == target_id {
                types.set_stack(k, RegType::PtrToMapValue { offset: Some(0), map_idx });
            }
        }
    }
}
