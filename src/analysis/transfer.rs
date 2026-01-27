// src/analysis/transfer.rs
use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::{RegType, TypeState, new_packet_id};
use crate::ast::{Instr, AluOp, CmpOp, Operand, Width, EndianOp, MemSize, ProgramKind};
use crate::zone::domain::{Reg, forget, get_bounds, 
    assign_add_imm, assign_add_reg, assign_eq, 
    assume_eq_const, assume_ge_const, assume_le_const, 
    assume_less_than, assume_ge_var, assume_le_var, 
    assume_gt_var, assume_le_var_plus_const, 
    assign_zero, assign_mul_imm, assign_and_mask,
    assign_div_imm, assign_div_reg,
    bit_and_const, assign_neg, assign_sub_reg,
    is_zero
};
use crate::analysis::access;
use crate::zone::domain::proven_u32_range;
use crate::zone::tnum::Tnum;
use crate::parsing::ctx_model::{
    classify_sk_buff_field, CtxFieldKind, classify_xdp_md_field,
    MemRegionId
};
use crate::analysis::env::VerificationError;
use crate::zone::dbm::Dbm;
use crate::analysis::constants;
use log::{error, warn};

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
        Instr::Alu { width, op, dst, src } => 
            transfer_alu(env, state, *width, *op, *dst, src.clone()),
        Instr::Endian { dst, op, size, width } => 
            transfer_endian(env, state, *dst, *op, *size, *width),
        Instr::If { width, left, op, right, target } => 
            transfer_if(env, state, *width, *left, *op, right.clone(), *target),
        Instr::Load { size, dst, base, off } => {
            access::check_load(env, &state, *base, *size, *off);
            // Try to resolve concrete value from .rodata
            // If successful, this sets the register to an exact constant (e.g., 0 or 1)
            // and we return early. This enables pruning dead configuration paths.
            if try_load_from_rodata(env, &mut state, *dst, *base, *off, *size) {
                state.pc += 1;
                return vec![state];
            }
            update_load_types(env, &mut state.types, *size, *dst, *base, *off);
            forget(&mut state.dbm, *dst);
            // Apply implicit bounds based on Load Size (Zero Extension)
            // All BPF loads (u8, u16, u32, u64) are treated as unsigned integers.
            // Therefore, they are always >= 0.
            assume_ge_const(&mut state.dbm, *dst, 0);
            // Apply upper bounds for sub-64-bit loads
            match size {
                MemSize::U8  => assume_le_const(&mut state.dbm, *dst, 0xFF),
                MemSize::U16 => assume_le_const(&mut state.dbm, *dst, 0xFFFF),
                MemSize::U32 => assume_le_const(&mut state.dbm, *dst, 0xFFFFFFFF),
                MemSize::U64 => {
                    // For U64, we theoretically don't have an upper bound in i64 signed domain
                    // (values > i64::MAX appear negative). 
                    // BPF "Unsigned" loads of U64 don't guarantee they fit in positive i64.
                    // So we only assert >= 0 if we are sure it's not a "large" u64.
                    // Safest is to do nothing for U64 upper bound, or assume it's scalar.
                }
            }

            // Update tnum
            state.set_tnum(*dst, Tnum::unknown());

            state.pc += 1;
            vec![state]
        },
        Instr::Store { size, base, off, src } => {
            access::check_store(env, &state, *base, *size, *off);
            let src_type = {
                match src {
                    Operand::Reg(r) => state.types.get(*r),
                    Operand::Imm(_) => RegType::ScalarValue,
                }
            };
            let base_type = state.types.get(*base);
            update_store_types(&mut state.types, src_type, *size, base_type, *off);
            state.pc += 1;
            vec![state]
        },
        Instr::AtomicAdd { size, base, off, src: _ } => {
            let base_ty = state.types.get(*base);
            // Atomic add to ctx pointer is not allowed
            if matches!(base_ty, RegType::PtrToCtx) {
                env.fail(VerificationError::InvalidArgType { pc: state.pc, reg: *base });
                state.pc += 1;
                return vec![]
            }
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
        Instr::CallRel { target } => transfer_call_rel(env, state, *target),
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
    let in_types = state.types.clone();

    // Early check for division by zero
    if op == AluOp::Div && is_div_by_zero(&state.dbm, &src) {
        env.fail(VerificationError::DivideByZero { pc: state.pc });
        return vec![];
    }

    update_alu_types(env, &in_types, &mut state.types, width, op, dst, &src, state.pc);

    match op {
        AluOp::Add => handle_add(env, &mut state, &in_types, width, dst, &src),
        AluOp::Sub => handle_sub(env, &mut state, &in_types, width, dst, &src),
        AluOp::Mov => handle_mov(&mut state, width, dst, &src),
        AluOp::And => handle_and(&mut state, width, dst, &src),
        AluOp::Or => handle_or(&mut state, width, dst, &src),
        AluOp::Neg => handle_neg(&mut state, width, dst),
        AluOp::Shr => handle_shr(&mut state, width, dst, &src),
        AluOp::Shl => handle_shl(&mut state, width, dst, &src),
        AluOp::Mul => handle_mul(&mut state, width, dst, &src),
        AluOp::Mod => handle_mod(&mut state, width, dst, &src),
        AluOp::Div => handle_div(&mut state, width, dst, &src),
        AluOp::Xor | AluOp::Arsh => forget(&mut state.dbm, dst),
    }

    if state.dbm.is_inconsistent() {
        env.fail(VerificationError::DbmInconsistent { pc: state.pc });
        error!("[Verifier] DBM became inconsistent at pc {}", state.pc);
        state.dbm.dump_matrix();
        vec![]
    } else {
        state.pc += 1;
        vec![state]
    }
}

fn transfer_endian(
    _env: &VerifierEnv,
    mut state: State,
    dst: Reg,
    op: EndianOp,
    size: u32,
    width: Width
) -> Vec<State> {
    // 1. Types: Endian ops destroy pointers -> Scalar
    state.types.set(dst, RegType::ScalarValue);

    match op {
        EndianOp::ToLe => {
            match size {
                64 => { /* Identity for LE host; Keep constraints if Width::W64 */ },
                32 => assign_and_mask(&mut state.dbm, dst, 0xFFFF_FFFF),
                16 => assign_and_mask(&mut state.dbm, dst, 0xFFFF),
                _  => forget(&mut state.dbm, dst),
            }
        },
        EndianOp::ToBe => {
            // Big Endian always swaps on LE host -> Value changes non-linearly
            // We must forget the old value.
            // However, we know the new max value based on the swap size.
            match size {
                16 => assign_and_mask(&mut state.dbm, dst, 0xFFFF),
                32 => assign_and_mask(&mut state.dbm, dst, 0xFFFF_FFFF),
                // 64-bit BE swap: Result is u64 (if Width::W64) or u32 (if Width::W32)
                64 => forget(&mut state.dbm, dst),
                _  => forget(&mut state.dbm, dst),
            }
        }
    }

    // 3. Handle Implicit 32-bit Zero Extension
    // If this was 0xdc (Width::W32), the upper 32 bits are ALWAYS cleared.
    // This provides a tighter bound [0, U32_MAX] even if the operation was "Unknown".
    if width == Width::W32 {
        // Safe intersection: intersect current bounds with [0, 0xFFFFFFFF]
        // domain::assign_and_mask effectively does 'forget + bound', 
        // but since we might have just set tighter bounds (like 0xFFFF) above,
        // we use 'bit_and_const' or manual bounds to preserve them.
        
        // Simplest Sound Approach: Just enforce the mask. 
        // If we already did mask 0xFFFF above, 0xFFFF & 0xFFFFFFFF == 0xFFFF (Safe).
        bit_and_const(&mut state.dbm, dst, 0xFFFF_FFFF);
    }

    state.pc += 1;
    vec![state]
}

fn transfer_if(
    _env: &VerifierEnv,
    state: State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: Operand,
    target: usize,
) -> Vec<State> {

    // --- STEP 0: Static Branch Evaluation (Interval-Based) ---
    // If we can prove the condition is Always True or Always False based on bounds,
    // we return ONLY that path. This is critical for pruning dead error paths.
    if let Some(next_pcs) = eval_static_branch(&state, width, left, op, &right, target) {
        return next_pcs;
    }

    // --- STEP 1: Abstract Interpretation (Constraint Refinement) ---
    let mut out = Vec::new();
    let mut state_then = state.clone();
    let mut state_else = state.clone();

    state_then.pc = target;
    state_else.pc = state.pc + 1;

    // Apply constraints to refine the DBM in the destination states
    match &right {
        Operand::Imm(imm) => apply_imm_constraints(&mut state_then, &mut state_else, left, op, width, *imm),
        Operand::Reg(r) => apply_reg_constraints(&mut state_then, &mut state_else, left, op, width, *r),
    }

    // Branch Type Refinement (Packet/Map bounds)
    let instr = Instr::If { width, left, op, right: right.clone(), target };
    refine_branch(&mut state_then, &instr, true);
    refine_branch(&mut state_else, &instr, false);

    // Return only consistent states
    if !state_else.dbm.is_inconsistent() { out.push(state_else); }
    if !state_then.dbm.is_inconsistent() { out.push(state_then); }
    out
}

fn transfer_call(
    env: &mut VerifierEnv,
    mut state: State,
    helper: u32,
) -> Vec<State> {
    let in_types = state.types.clone();
    let pc = state.pc;

    // ========================================================================
    // Validate helper arguments BEFORE executing
    // ========================================================================
    validate_helper_args(env, &state, helper, &in_types, pc);
    
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
            warn!("[Verifier] tail_call R1 should be PTR_TO_CTX at pc {}", pc);
        }
        if !matches!(in_types.get(Reg::R2), RegType::PtrToMapObject { .. }) {
            warn!("[Verifier] tail_call R2 should be PTR_TO_MAP at pc {}", pc);
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
            assume_ge_const(&mut state.dbm, Reg::R0, 0);
            assume_le_const(&mut state.dbm, Reg::R0, 7);
        }
        constants::BPF_FIB_LOOKUP => {
            // Returns BPF_FIB_LKUP_RET_* (0-8)
            assume_ge_const(&mut state.dbm, Reg::R0, 0);
            assume_le_const(&mut state.dbm, Reg::R0, 8);
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

pub fn transfer_call_rel(
    _env: &mut VerifierEnv,
    state: State,
    target: usize,
) -> Vec<State> {
    // Branch 1: Enter the subprogram
    // We pass the state exactly as-is (registers R1-R5 hold arguments).
    // Note: Without stack frame isolation (R10 shift), this analysis conservatively 
    // assumes the callee shares the SAME stack frame. This works but is restrictive 
    // (callee overwriting fp[-8] will overwrite caller's fp[-8]).
    let mut enter_state = state.clone();
    enter_state.pc = target;

    // Branch 2: The "Return" (Fallthrough) path
    // We assume the function executes and returns.
    // Since we don't know what happened, we must havoc caller-saved registers.
    let mut return_state = state;
    return_state.pc += 1;

    // 1. Clobber R1-R5 (Arguments/Scratch)
    // The callee is free to destroy these.
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        forget(&mut return_state.dbm, r);
        return_state.types.set(r, RegType::NotInit);
    }

    // 2. Define R0 (Return Value)
    // We don't know what the function returned, so it's an Unknown Scalar.
    forget(&mut return_state.dbm, Reg::R0);
    return_state.types.set(Reg::R0, RegType::ScalarValue);

    // 3. Stack Clobbering?
    // Conservatively, we should strictly havoc the stack too if we passed pointers.
    // However, standard BPF convention is that callees use their own stack frame.
    // Since we aren't modeling frame pointers yet, leaving the stack 'as-is' 
    // is the pragmatic choice (assuming the callee didn't corrupt it via pointers).

    vec![enter_state, return_state]
}

// --- Helper Functions for If Branch Refinement ---

// Static Branch Checking
fn eval_static_branch(
    state: &State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: &Operand,
    target: usize
) -> Option<Vec<State>> {
    // --- Check tnum first for Eq/Ne with immediate ---
    if let Operand::Imm(imm) = right {
        let t = state.get_tnum(left);
        let imm_u64 = *imm as u64;
        
        match op {
            CmpOp::Eq => {
                // if left == imm
                if t.is_const() {
                    let is_equal = t.const_value() == Some(imm_u64);
                    let mut s = state.clone();
                    s.pc = if is_equal { target } else { state.pc + 1 };
                    return Some(vec![s]);
                }
                if !t.could_equal(imm_u64) {
                    // Can't be equal -> always fallthrough
                    let mut s = state.clone();
                    s.pc = state.pc + 1;
                    return Some(vec![s]);
                }
            }
            CmpOp::Ne => {
                // if left != imm
                if t.is_const() {
                    let is_equal = t.const_value() == Some(imm_u64);
                    let mut s = state.clone();
                    s.pc = if is_equal { state.pc + 1 } else { target };
                    return Some(vec![s]);
                }
                if !t.could_equal(imm_u64) {
                    // Can't be equal -> always taken (not-equal is true)
                    let mut s = state.clone();
                    s.pc = target;
                    return Some(vec![s]);
                }
                // Special case: if tnum proves definitely non-zero and imm == 0
                if *imm == 0 && t.is_definitely_nonzero() {
                    let mut s = state.clone();
                    s.pc = target;
                    return Some(vec![s]);
                }
            }
            _ => {} // Other ops handled below
        }
    }

    // --- Existing interval-based logic ---
    let (l_min, l_max) = get_bounds(&state.dbm, left);
    let l_min = l_min?; 
    let l_max = l_max?;

    let r_val = match right {
        Operand::Imm(i) => *i,
        Operand::Reg(r) => {
            let (rmin, rmax) = get_bounds(&state.dbm, *r);
            if rmin? == rmax? { rmin? } else { return None; }
        }
    };

    let condition_result = match width {
        Width::W64 => check_interval_64(op, l_min, l_max, r_val),
        Width::W32 => check_interval_32(op, l_min, l_max, r_val),
    };

    match condition_result {
        Some(true) => {
            let mut s = state.clone();
            s.pc = target;
            Some(vec![s])
        },
        Some(false) => {
            let mut s = state.clone();
            s.pc = state.pc + 1;
            Some(vec![s])
        },
        None => None,
    }
}

// --- Helper: Interval Logic ---

fn check_interval_64(op: CmpOp, min: i64, max: i64, r: i64) -> Option<bool> {
    // Basic interval logic for 64-bit
    match op {
        // Unsigned logic (cast to u64)
        CmpOp::UGt => if (min as u64) > (r as u64) { Some(true) } else if (max as u64) <= (r as u64) { Some(false) } else { None },
        CmpOp::ULt => if (max as u64) < (r as u64) { Some(true) } else if (min as u64) >= (r as u64) { Some(false) } else { None },
        CmpOp::UGe => if (min as u64) >= (r as u64) { Some(true) } else if (max as u64) < (r as u64) { Some(false) } else { None },
        CmpOp::ULe => if (max as u64) <= (r as u64) { Some(true) } else if (min as u64) > (r as u64) { Some(false) } else { None },
        
        // Signed logic (use i64 directly)
        CmpOp::SLt => if max < r { Some(true) } else if min >= r { Some(false) } else { None },
        CmpOp::SGt => if min > r { Some(true) } else if max <= r { Some(false) } else { None },
        CmpOp::SGe => if min >= r { Some(true) } else if max < r { Some(false) } else { None },
        CmpOp::SLe => if max <= r { Some(true) } else if min > r { Some(false) } else { None },

        // Equality
        CmpOp::Eq => if min == max && min == r { Some(true) } else if min > r || max < r { Some(false) } else { None },
        CmpOp::Ne => if min == max && min != r { Some(true) } else if min > r || max < r { Some(false) } else { None },

        // Test
        CmpOp::Test => {
            // x & r != 0
            if (min & r) != 0 && (max & r) != 0 { Some(true) }
            else if (min & r) == 0 && (max & r) == 0 { Some(false) }
            else { None }
        }
    }
}

fn check_interval_32(op: CmpOp, min: i64, max: i64, r: i64) -> Option<bool> {
    // 1. Check for 32-bit Wrap-around
    // If the upper 32-bits are different, the u32 range is not contiguous/monotonic
    // relative to the u64 range, making simple min/max checks invalid.
    if (min as u64 >> 32) != (max as u64 >> 32) {
        return None; 
    }

    let min_u32 = min as u32;
    let max_u32 = max as u32;
    let r_u32 = r as u32;

    match op {
        // Signed 32-bit Less Than (Fixes the crash!)
        CmpOp::SLt => {
            let min_i32 = min_u32 as i32;
            let max_i32 = max_u32 as i32;
            let r_i32 = r_u32 as i32;
            
            if max_i32 < r_i32 { Some(true) }       // Entire range < R
            else if min_i32 >= r_i32 { Some(false) } // Entire range >= R
            else { None }
        },
        // Signed 32-bit Greater Than
        CmpOp::SGt => {
            let min_i32 = min_u32 as i32;
            let max_i32 = max_u32 as i32;
            let r_i32 = r_u32 as i32;

            if min_i32 > r_i32 { Some(true) }
            else if max_i32 <= r_i32 { Some(false) }
            else { None }
        },
        // Signed 32-bit Greater or Equal
        CmpOp::SGe => {
            let min_i32 = min_u32 as i32;
            let max_i32 = max_u32 as i32;
            let r_i32 = r_u32 as i32;
            if min_i32 >= r_i32 { Some(true) }
            else if max_i32 < r_i32 { Some(false) }
            else { None }
        },
        // Signed 32-bit Less or Equal
        CmpOp::SLe => {
            let min_i32 = min_u32 as i32;
            let max_i32 = max_u32 as i32;
            let r_i32 = r_u32 as i32;
            if max_i32 <= r_i32 { Some(true) }
            else if min_i32 > r_i32 { Some(false) }
            else { None }
        },
        // Unsigned 32-bit checks
        CmpOp::UGt => if max_u32 > r_u32 { Some(true) } else if min_u32 <= r_u32 { Some(false) } else { None },
        CmpOp::ULt => if max_u32 < r_u32 { Some(true) } else if min_u32 >= r_u32 { Some(false) } else { None },
        CmpOp::UGe => if min_u32 >= r_u32 { Some(true) } else if max_u32 < r_u32 { Some(false) } else { None },
        CmpOp::ULe => if max_u32 <= r_u32 { Some(true) } else if min_u32 > r_u32 { Some(false) } else { None },
        
        // Unsigned checks
        CmpOp::Eq => if min_u32 == max_u32 && min_u32 == r_u32 { Some(true) } else if min_u32 > r_u32 || max_u32 < r_u32 { Some(false) } else { None },
        CmpOp::Ne => if min_u32 == max_u32 && min_u32 != r_u32 { Some(true) } else if min_u32 > r_u32 || max_u32 < r_u32 { Some(false) } else { None },

        // Test
        CmpOp::Test => {
            // x & r != 0
            if (min_u32 & r_u32) != 0 && (max_u32 & r_u32) != 0 { Some(true) }
            else if (min_u32 & r_u32) == 0 && (max_u32 & r_u32) == 0 { Some(false) }
            else { None }
        }
    }
}

/// Check if we can safely apply signed constraints for 32-bit comparisons.
/// This is true when the 64-bit value fits in i32 range, so 32-bit and 64-bit
/// signed interpretations are the same.
fn fits_in_i32_range(dbm: &Dbm, reg: Reg) -> bool {
    let (lo, hi) = get_bounds(dbm, reg);
    match (lo, hi) {
        (Some(l), Some(h)) => l >= i32::MIN as i64 && h <= i32::MAX as i64,
        _ => false,
    }
}

/// Check if value is known to be in u32 range [0, 0xFFFFFFFF]
fn fits_in_u32_range(dbm: &Dbm, reg: Reg) -> bool {
    let (lo, hi) = get_bounds(dbm, reg);
    match (lo, hi) {
        (Some(l), Some(h)) => l >= 0 && h <= 0xFFFFFFFF,
        _ => false,
    }
}

fn apply_imm_constraints(
    then_s: &mut State, 
    else_s: &mut State, 
    left: Reg, 
    op: CmpOp,
    width: Width,
    imm: i64,
) {
    let imm_u64 = imm as u64;
    
    // Handle 32-bit signed comparisons specially
    if width == Width::W32 {
        match op {
            // Special case: 32-bit signed comparison against 0
            // This is common (checking if value is negative)
            CmpOp::SLt if imm == 0 => {
                if fits_in_u32_range(&then_s.dbm, left) {
                    // 32-bit signed < 0 means bit 31 is set: value in [0x80000000, 0xFFFFFFFF]
                    assume_ge_const(&mut then_s.dbm, left, 0x80000000);
                    // 32-bit signed >= 0 means bit 31 is clear: value in [0, 0x7FFFFFFF]
                    assume_le_const(&mut else_s.dbm, left, 0x7FFFFFFF);
                }
                return;
            }
            CmpOp::SGe if imm == 0 => {
                if fits_in_u32_range(&then_s.dbm, left) {
                    // 32-bit signed >= 0 means value in [0, 0x7FFFFFFF]
                    assume_le_const(&mut then_s.dbm, left, 0x7FFFFFFF);
                    // 32-bit signed < 0 means value in [0x80000000, 0xFFFFFFFF]
                    assume_ge_const(&mut else_s.dbm, left, 0x80000000);
                }
                return;
            }
            CmpOp::SLe if imm == -1 => {
                // x <=s32 -1 is same as x <s32 0
                if fits_in_u32_range(&then_s.dbm, left) {
                    assume_ge_const(&mut then_s.dbm, left, 0x80000000);
                    assume_le_const(&mut else_s.dbm, left, 0x7FFFFFFF);
                }
                return;
            }
            CmpOp::SGt if imm == -1 => {
                // x >s32 -1 is same as x >=s32 0
                if fits_in_u32_range(&then_s.dbm, left) {
                    assume_le_const(&mut then_s.dbm, left, 0x7FFFFFFF);
                    assume_ge_const(&mut else_s.dbm, left, 0x80000000);
                }
                return;
            }
            
            // For other signed comparisons, only constrain if value fits in i32
            CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe => {
                if !fits_in_i32_range(&then_s.dbm, left) {
                    return;  // Can't safely add constraints
                }
                // Fall through to standard constraint logic
            }

            CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt => {
                // Unsigned comparisons can always be applied safely in 32-bit
            }

            CmpOp::Eq | CmpOp::Ne => {
                // Equality checks can always be applied safely
            }

            CmpOp::Test => {
                // Test against immediate in 32-bit
                // We can only safely apply constraints if the value fits in u32
                if !fits_in_u32_range(&then_s.dbm, left) {
                    return; // Can't safely add constraints
                }
                // Fall through to standard constraint logic
            }
        }
    }

    let is_unsigned_cmp = matches!(op, CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt);
    
    if is_unsigned_cmp {
        // If imm is negative (when interpreted as signed), it represents a 
        // large unsigned value (>= 2^63). Our signed DBM can't handle this correctly.
        if imm < 0 {
            // Conservative: don't apply any constraints
            // The type refinement (packet ranges, etc.) will still happen
            return;
        }
        
        // Also check if register might have values >= 2^63
        // If so, signed and unsigned comparisons differ
        let (lo, hi) = get_bounds(&then_s.dbm, left);
        if let (Some(l), Some(_h)) = (lo, hi) {
            if l < 0 {
                // Register might be negative (signed) = large (unsigned)
                // Can't safely apply unsigned constraints
                return;
            }
        } else {
            // Unknown bounds, be conservative
            return;
        }
    }
    
    // Standard constraint logic (64-bit or safe 32-bit cases)
    match op {
        CmpOp::Ne => {
            assume_eq_const(&mut else_s.dbm, left, imm);
            else_s.set_tnum(left, Tnum::constant(imm_u64));
            if imm == 0 {
                if let Some(non_null) = then_s.types.get(left).to_non_null() {
                    then_s.types.set(left, non_null);
                    if let Some(offset) = non_null.get_offset() {
                        assume_eq_const(&mut then_s.dbm, left, offset);
                    }
                }
            }
        }
        CmpOp::Eq => {
            assume_eq_const(&mut then_s.dbm, left, imm);
            then_s.set_tnum(left, Tnum::constant(imm_u64));
            if imm == 0 {
                if let Some(non_null) = else_s.types.get(left).to_non_null() {
                    else_s.types.set(left, non_null);
                    if let Some(offset) = non_null.get_offset() {
                        assume_eq_const(&mut else_s.dbm, left, offset);
                    }
                }
            }
        }
        CmpOp::UGe | CmpOp::SGe => {
            assume_ge_const(&mut then_s.dbm, left, imm);
            assume_less_than(&mut else_s.dbm, left, imm);
        }
        CmpOp::ULe | CmpOp::SLe => {
            assume_le_const(&mut then_s.dbm, left, imm);
            assume_ge_const(&mut else_s.dbm, left, imm + 1);
        }
        CmpOp::UGt | CmpOp::SGt => {
            assume_ge_const(&mut then_s.dbm, left, imm + 1);
            assume_le_const(&mut else_s.dbm, left, imm);
        }
        CmpOp::ULt | CmpOp::SLt => {
            assume_less_than(&mut then_s.dbm, left, imm);
            assume_ge_const(&mut else_s.dbm, left, imm);
        }
        CmpOp::Test => {
            // x & imm != 0
            // Skip for now
        }
    }
}

fn apply_reg_constraints(
    then_s: &mut State, 
    else_s: &mut State, 
    left: Reg, 
    op: CmpOp,
    width: Width,
    right: Reg
) {
    // For 32-bit signed reg-reg comparisons, only constrain if both fit in i32
    if width == Width::W32 {
        match op {
            CmpOp::SLt | CmpOp::SLe | CmpOp::SGt | CmpOp::SGe => {
                if !fits_in_i32_range(&then_s.dbm, left) || !fits_in_i32_range(&then_s.dbm, right) {
                    // Can't safely add constraints, but still refine pointer ranges
                    for state in [&mut *then_s, &mut *else_s] {
                        refine_packet_ranges(&state.dbm, &mut state.types, left, right);
                        refine_packet_ranges(&state.dbm, &mut state.types, right, left);
                        refine_mem_ranges(&state.dbm, &mut state.types, left, right);
                        refine_mem_ranges(&state.dbm, &mut state.types, right, left);
                    }
                    return;
                }
            }
            | CmpOp::Eq | CmpOp::Ne | CmpOp::UGe | CmpOp::ULe | CmpOp::UGt | CmpOp::ULt | CmpOp::Test => { /* Other ops are safe */}
        }
    }
    
    // Standard constraint logic
    match op {
        CmpOp::UGe | CmpOp::SGe => { 
            assume_ge_var(&mut then_s.dbm, left, right);
            assume_le_var_plus_const(&mut else_s.dbm, left, right, -1);
        }
        CmpOp::ULe | CmpOp::SLe => { 
            assume_le_var(&mut then_s.dbm, left, right);
            assume_gt_var(&mut else_s.dbm, left, right);
        }
        CmpOp::UGt | CmpOp::SGt => { 
            assume_gt_var(&mut then_s.dbm, left, right);
            assume_le_var(&mut else_s.dbm, left, right);
        }
        CmpOp::ULt | CmpOp::SLt => { 
            assume_le_var_plus_const(&mut then_s.dbm, left, right, -1);
            assume_ge_var(&mut else_s.dbm, left, right);
        }
        CmpOp::Eq => {
            assign_eq(&mut then_s.dbm, left, right);
            // For else branch, we can't express 'not equal' directly.
            // So we over-approximate by not adding any constraint.
        }
        CmpOp::Ne => {
            assign_eq(&mut else_s.dbm, left, right);
            // For then branch, we can't express 'not equal' directly.
            // So we over-approximate by not adding any constraint. 
        }
        CmpOp::Test => {
            // x & y != 0
            // No direct way to express in DBM, so skip
        }
    }
    
    // Refine pointer ranges on both states
    for state in [&mut *then_s, &mut *else_s] {
        refine_packet_ranges(&state.dbm, &mut state.types, left, right);
        refine_packet_ranges(&state.dbm, &mut state.types, right, left);
        refine_mem_ranges(&state.dbm, &mut state.types, left, right);
        refine_mem_ranges(&state.dbm, &mut state.types, right, left);
    }
}

// --- Helper Functions for Load from .rodata ---
fn try_load_from_rodata(
    env: &VerifierEnv,
    state: &mut State,
    dst: Reg,
    base: Reg,
    insn_off: i16,
    size: MemSize,
) -> bool {
    // 1. Check if we are loading from a Map Pointer
    if let RegType::PtrToMapValue { map_idx, offset: base_offset } = state.types.get(base) {
        // We can only read if the pointer offset is known (not variable)
        if let Some(ptr_val) = base_offset {
            let map = &env.ctx.map_defs[map_idx];

            // 2. Check if this map has static content (.rodata)
            if let Some(data) = &map.initial_data {
                // Calculate absolute byte offset
                // abs_off = (pointer's internal offset) + (instruction's load offset)
                let abs_off = ptr_val + insn_off as i64;

                if abs_off >= 0 {
                    let start = abs_off as usize;
                    let len = size.bytes();

                    // 3. Bounds Check against the static data
                    if start + len <= data.len() {
                        // 4. Read the Bytes
                        let bytes = &data[start .. start + len];

                        // Convert bytes to u64 (Little Endian, standard for BPF)
                        let mut val: u64 = 0;
                        for (i, &b) in bytes.iter().enumerate() {
                            val |= (b as u64) << (i * 8);
                        }

                        // 5. Update State
                        // Reset the register to remove old constraints
                        forget(&mut state.dbm, dst);
                        
                        // Assign the EXACT constant value
                        assume_eq_const(&mut state.dbm, dst, val as i64);
                        
                        // Set type to Scalar (constants are just numbers)
                        state.types.set(dst, RegType::ScalarValue);

                        return true; // Successfully handled
                    }
                }
            }
        }
    }
    false
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
                    (RegType::PtrToPacket { id, range, is_base: _, off }, Operand::Imm(k)) => {
                        let new_off = off.saturating_add(*k);
                        types.set(dst, RegType::PtrToPacket { id, range, is_base: false, off: new_off });
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
                    RegType::PtrToPacket { id, range, is_base: _, off } => {
                        let new_off =  off.saturating_sub(*k as i64);
                        types.set(dst, RegType::PtrToPacket { id, range, is_base: false, off: new_off });
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

fn update_load_types(env: &VerifierEnv, types: &mut TypeState, size: MemSize, dst: Reg, base: Reg, off: i16) {
    let base_ty = types.get(base);
    match base_ty {
        RegType::PtrToCtx => {
            let kind = match env.ctx.prog_kind {
                ProgramKind::Xdp => classify_xdp_md_field(off, size),
                ProgramKind::SchedCls | ProgramKind::SocketFilter => classify_sk_buff_field(off, size),
                _ => None,
            };
            if let Some(kind) = kind {
                match kind {
                    CtxFieldKind::PacketStart => {
                        let new_id = new_packet_id();
                        types.set(dst, RegType::PtrToPacket { id: new_id, range: 0, is_base: true, off: 0 });
                    }
                    CtxFieldKind::PacketEnd => {
                        types.set(dst, RegType::PtrToPacketEnd);
                    }
                    CtxFieldKind::PtrToMem { region } => {
                        types.set(dst, RegType::PtrToMem { region, range: 0 });
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
                    if size == MemSize::U64 { 
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

fn update_store_types(types: &mut TypeState, src_type: RegType, size: MemSize, base_type: RegType, off: i16) {
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

// ===============================================
// ALU Handlers
// ===============================================

fn handle_add(
    env: &mut VerifierEnv,
    state: &mut State,
    in_types: &TypeState,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            assign_add_imm(&mut state.dbm, dst, *c);
        }
        Operand::Reg(r) => {
            if is_clean_ptr(in_types, dst) {
                // Special Case: Ptr(Offset 0) += Scalar.
                // NewOffset = 0 + Scalar = Scalar.
                assign_eq(&mut state.dbm, dst, *r);
            } else {
                // Standard Case: Ptr(Offset X) += Scalar OR Scalar += Scalar
                assign_add_reg(&mut state.dbm, dst, *r);
            }
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    check_ptr_bounds(env, state, dst);
}

fn handle_sub(
    env: &mut VerifierEnv,
    state: &mut State,
    in_types: &TypeState,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            assign_add_imm(&mut state.dbm, dst, -c);
        }
        Operand::Reg(r) => {
            if is_clean_ptr(in_types, dst) {
                // dst = 0 - r => dst = -r
                assign_eq(&mut state.dbm, dst, *r);
                assign_neg(&mut state.dbm, dst);
            } else {
                // Standard Case: Interval Subtraction
                assign_sub_reg(&mut state.dbm, dst, *r);
            }
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }

    check_ptr_bounds(env, state, dst);
}

fn handle_mov(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    // Tnum update
    match src {
        Operand::Imm(c) => {
            state.set_tnum(dst, Tnum::constant(*c as u64));
        }
        Operand::Reg(r) => {
            let t = state.get_tnum(*r);
            state.set_tnum(dst, t);
        }
    }
    
    // DBM update
    match src {
        Operand::Reg(r) => {
            if width == Width::W32 {
                forget(&mut state.dbm, dst);
                if proven_u32_range(&mut state.dbm, *r, Reg::Zero) {
                    assign_eq(&mut state.dbm, dst, *r);
                } else {
                    assume_ge_const(&mut state.dbm, dst, 0);
                    assume_le_const(&mut state.dbm, dst, 0xFFFFFFFF);
                }
            } else {
                if *r == Reg::R10 {
                    assign_zero(&mut state.dbm, dst);
                } else {
                    assign_eq(&mut state.dbm, dst, *r);
                }
            }
        }
        Operand::Imm(c) => {
            // Handle zero-extension for W32
            let c = if width == Width::W32 { (*c as u32) as i64 } else { *c };
            
            forget(&mut state.dbm, dst);
            assume_le_const(&mut state.dbm, dst, c);
            assume_ge_const(&mut state.dbm, dst, c);
        }
    }
}

fn handle_and(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    let (min_op, max_op) = get_bounds(&state.dbm, dst);
    let input_nonnegative = min_op.map_or(false, |m| m >= 0);

    forget(&mut state.dbm, dst);

    if let Operand::Imm(mask) = src {
        let mask = if width == Width::W32 { (*mask as u32) as i64 } else { *mask };
        if mask >= 0 {
            assign_and_mask(&mut state.dbm, dst, mask);
        } else if input_nonnegative {
            // Negative mask with non-negative input:
            // Safe approximation: [0, input_max]
            assume_ge_const(&mut state.dbm, dst, 0);
            if let Some(max) = max_op {
                assume_le_const(&mut state.dbm, dst, max);
            }
        }
    } else if let Operand::Reg(_) = src {
        // AND with register - result is non-negative if both operands are
        assume_ge_const(&mut state.dbm, dst, 0);
    }
    
    // Tnum update
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(mask) => {
            let mask = if width == Width::W32 { (*mask as u32) as u64 } else { *mask as u64 };
            t.and_imm(mask)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.and(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);
    
    // Cross-validate: if tnum knows the exact value, tell DBM
    if let Some(c) = new_t.const_value() {
        assume_eq_const(&mut state.dbm, dst, c as i64);
    }
}

fn handle_or(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    forget(&mut state.dbm, dst);
    
    // Tnum update
    let t = state.get_tnum(dst);
    let new_t = match src {
        Operand::Imm(c) => {
            let c = if width == Width::W32 { (*c as u32) as u64 } else { *c as u64 };
            t.or_imm(c)
        }
        Operand::Reg(r) => {
            let r_tnum = state.get_tnum(*r);
            t.or(r_tnum)
        }
    };
    state.set_tnum(dst, new_t);
    
    // If tnum proves non-zero, inform DBM
    if new_t.is_definitely_nonzero() {
        assume_ge_const(&mut state.dbm, dst, 1);
    }
}

fn handle_neg(
    state: &mut State,
    width: Width,
    dst: Reg,
) {
    // Apply Negate Logic (swaps bounds)
    assign_neg(&mut state.dbm, dst);

    // Handle 32-bit Truncation/Extension
    if width == Width::W32 {
        bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
    }
    
    // Type Update
    state.types.set(dst, RegType::ScalarValue);
}

fn handle_shr(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(k) => {
            let bits = if width == Width::W32 { 32u32 } else { 64u32 };
            let k = (*k as u32).min(bits);
            forget(&mut state.dbm, dst);
            assume_ge_const(&mut state.dbm, dst, 0);
            if k < bits {
                let ub: i64 = ((1u128 << (bits - k)) - 1) as i64;
                assume_le_const(&mut state.dbm, dst, ub);
            } else {
                assume_eq_const(&mut state.dbm, dst, 0);
            }
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
        }
    }
}

fn handle_shl(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(k) => {
            let k = *k as u32;
            
            // For W32, only lower 5 bits matter; for W64, lower 6 bits
            let shift_amount = if width == Width::W32 { k & 0x1F } else { k & 0x3F };
            
            let (old_lo, old_hi) = get_bounds(&state.dbm, dst);
            forget(&mut state.dbm, dst);
            
            if let (Some(lo), Some(hi)) = (old_lo, old_hi) {
                if lo >= 0 && shift_amount < 63 {
                    let max_safe: i64 = i64::MAX >> shift_amount;
                    
                    if hi <= max_safe {
                        assume_ge_const(&mut state.dbm, dst, lo << shift_amount);
                        assume_le_const(&mut state.dbm, dst, hi << shift_amount);
                    }
                }
            }
            
            if width == Width::W32 {
                apply_w32_truncation(&mut state.dbm, dst);
            }
            
            // Tnum update for immediate shift
            let t = state.get_tnum(dst);
            let new_t = t.shl_imm(shift_amount as u64);
            state.set_tnum(dst, new_t);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
            
            // Tnum: shift by register = result is unknown
            // For W32: result is in [0, 0xFFFFFFFF]
            // For W64: result is in [0, u64::MAX]
            let new_t = if width == Width::W32 {
                assume_ge_const(&mut state.dbm, dst, 0);
                assume_le_const(&mut state.dbm, dst, u32::MAX as i64);
                Tnum::u32_unknown()
            } else {
                Tnum::unknown()
            };
            state.set_tnum(dst, new_t);
        }
    }
}

fn handle_mul(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            assign_mul_imm(&mut state.dbm, dst, *c);
        }
        Operand::Reg(_) => {
            forget(&mut state.dbm, dst);
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }
}

fn handle_mod(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    match src {
        Operand::Imm(c) => {
            if *c > 0 {
                forget(&mut state.dbm, dst);
                assume_ge_const(&mut state.dbm, dst, 0);
                assume_le_const(&mut state.dbm, dst, c - 1);
            } else {
                forget(&mut state.dbm, dst);
            }
        }
        Operand::Reg(r) => {
            let (r_lo, r_hi) = get_bounds(&state.dbm, *r);
            forget(&mut state.dbm, dst);
            
            match (r_lo, r_hi) {
                (Some(lo), Some(hi)) if lo > 0 => {
                    // Divisor is strictly positive, result is in [0, hi-1]
                    assume_ge_const(&mut state.dbm, dst, 0);
                    assume_le_const(&mut state.dbm, dst, hi - 1);
                }
                (Some(lo), _) if lo > 0 => {
                    // Divisor is positive but unbounded above
                    assume_ge_const(&mut state.dbm, dst, 0);
                }
                _ => {}
            }
        }
    }
    
    if width == Width::W32 {
        apply_w32_truncation(&mut state.dbm, dst);
    }
}

fn handle_div(
    state: &mut State,
    width: Width,
    dst: Reg,
    src: &Operand,
) {
    // Division by zero already checked
    match src {
        Operand::Imm(imm) => assign_div_imm(&mut state.dbm, dst, *imm),
        Operand::Reg(r_src) => assign_div_reg(&mut state.dbm, dst, *r_src),
    }

    if width == Width::W32 {
        bit_and_const(&mut state.dbm, dst, 0xFFFFFFFF);
    }
    
    state.types.set(dst, RegType::ScalarValue);
}

/// Apply W32 truncation to a register's bounds.
/// If the current bounds exceed [0, 0xFFFFFFFF], widen to that range.
fn apply_w32_truncation(dbm: &mut Dbm, dst: Reg) {
    let (lo, hi) = get_bounds(dbm, dst);
    
    let safe = match (lo, hi) {
        (Some(l), Some(h)) => l >= 0 && h <= 0xFFFFFFFF,
        _ => false,
    };
    
    if !safe {
        forget(dbm, dst);
        assume_ge_const(dbm, dst, 0);
        assume_le_const(dbm, dst, 0xFFFFFFFF);
    }
}

/// Check if a register holds a "clean" pointer (offset == 0)
fn is_clean_ptr(types: &TypeState, reg: Reg) -> bool {
    match types.get(reg) {
        RegType::PtrToMapValue { offset: Some(0), .. } |
        RegType::PtrToStack { offset: Some(0) } |
        RegType::PtrToPacket { off: 0, .. } => true,
        _ => false,
    }
}

fn is_div_by_zero(dbm: &Dbm, src: &Operand) -> bool {
    match src {
        Operand::Imm(k) => *k == 0,
        Operand::Reg(r) => {
            let (lo, hi) = get_bounds(dbm, *r);
            matches!((lo, hi), (Some(0), Some(0)))
        }
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
    
    if !matches!(types.get(end_reg), RegType::PtrToPacketEnd) {
        return;
    }
    
    let mut max_base_range: u64 = 0;
    
    for r in crate::zone::domain::Reg::ALL {
        if let RegType::PtrToPacket { id, range, off, is_base: _ } = types.get(r) {
            if id == target_id {
                let dist = dbm.get(r, end_reg);
                if dist < crate::zone::dbm::INF && dist <= 0 {
                    let safe_from_r = dist.unsigned_abs();
                    
                    // Only compute base range for non-negative offsets
                    if off >= 0 {
                        let base_range = (off as u64).saturating_add(safe_from_r);
                        if base_range > max_base_range {
                            max_base_range = base_range;
                        }
                    }
                }
                // Keep existing valid range if larger
                if range > max_base_range {
                    max_base_range = range;
                }
            }
        }
    }
    
    // Propagate to all pointers with this ID
    if max_base_range > 0 {
        for r in crate::zone::domain::Reg::ALL {
            if let RegType::PtrToPacket { id, off, is_base, .. } = types.get(r) {
                if id == target_id {
                    types.set(r, RegType::PtrToPacket { id, range: max_base_range, off, is_base });
                }
            }
        }
        
        let stack_keys: Vec<i16> = types.stack.keys().cloned().collect();
        for k in stack_keys {
            if let RegType::PtrToPacket { id, off, is_base, .. } = types.get_stack(k) {
                if id == target_id {
                    types.set_stack(k, RegType::PtrToPacket { id, range: max_base_range, off, is_base });
                }
            }
        }
    }
}

/// Refines the safe access range of memory region pointers based on DBM constraints.
/// Similar to refine_packet_ranges but for PtrToMem.
fn refine_mem_ranges(dbm: &Dbm, types: &mut TypeState, mem_reg: Reg, end_reg: Reg) {
    let target_region = match types.get(mem_reg) {
        RegType::PtrToMem { region, .. } => region,
        _ => return,
    };
    
    // Validate end_reg is the correct end marker for this region
    let is_valid_end = match target_region {
        MemRegionId::CalicoMetaRegion => {
            matches!(types.get(end_reg), RegType::PtrToPacket { is_base: true, .. })
        }
    };
    if !is_valid_end {
        return;
    }
    
    // Update all PtrToMem registers with matching region
    for r in crate::zone::domain::Reg::ALL {
        if let RegType::PtrToMem { region, range } = types.get(r) {
            if region == target_region {
                let dist = dbm.get(r, end_reg);
                if dist < crate::zone::dbm::INF && dist <= 0 {
                    let safe_bytes = dist.unsigned_abs();
                    if safe_bytes > range {
                        types.set(r, RegType::PtrToMem { region, range: safe_bytes });
                    }
                }
            }
        }
    }
    
    // Also update stack slots with matching region
    let stack_keys: Vec<i16> = types.stack.keys().cloned().collect();
    for k in stack_keys {
        if let RegType::PtrToMem { region, range } = types.get_stack(k) {
            if region == target_region {
                let max_range = Reg::ALL.iter()
                    .filter_map(|&r| match types.get(r) {
                        RegType::PtrToMem { region: rg, range } if rg == target_region => Some(range),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0);
                if max_range > range {
                    types.set_stack(k, RegType::PtrToMem { region, range: max_range });
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
    state: &mut State,
    instr: &Instr, 
    branch_taken: bool // True if we are analyzing the branch-taken path, False if fallthrough
) {
    match instr {
        Instr::If { op, left, right: Operand::Imm(0), .. } => {
            match op {
                CmpOp::Ne => {
                    // if (reg != 0) goto Target;
                    // Taken (True) -> reg != 0 -> SAFE
                    if branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::Eq => {
                    // if (reg == 0) goto Target;
                    // Fallthrough (False) -> reg != 0 -> SAFE
                    if !branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::SGe | CmpOp::UGe | CmpOp::SGt | CmpOp::UGt => {
                    // if (reg >= 0) goto Target;  or  if (reg > 0) goto Target;
                    // Taken (True) -> reg >= 1 -> SAFE
                    if branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::SLe | CmpOp::ULe | CmpOp::SLt | CmpOp::ULt => {
                    // if (reg <= 0) goto Target;  or  if (reg < 0) goto Target;
                    // Fallthrough (False) -> reg >= 1 -> SAFE
                    if !branch_taken { maybe_promote_map_val(state, *left); }
                },
                CmpOp::Test => {
                    // if (reg & 0xFF != 0) goto Target;
                    // Taken (True) -> reg != 0 -> SAFE
                    if branch_taken { maybe_promote_map_val(state, *left); }
                }
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
fn maybe_promote_map_val(state: &mut State, reg: Reg) {
    let (target_id, _target_map_idx) = match state.types.get(reg) {
        RegType::PtrToMapValueOrNull { id, map_idx } => (id, map_idx),
        _ => return,
    };
    for r in Reg::ALL {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = state.types.get(r) {
            if id == target_id {
                state.types.set(r, RegType::PtrToMapValue { offset: Some(0), map_idx });
                assign_zero(&mut state.dbm, r);
            }
        }
    }
    let stack_keys: Vec<i16> = state.types.stack.keys().cloned().collect();
    for k in stack_keys {
        if let RegType::PtrToMapValueOrNull { id, map_idx } = state.types.get_stack(k) {
            if id == target_id {
                state.types.set_stack(k, RegType::PtrToMapValue { offset: Some(0), map_idx });
            }
        }
    }
}

fn validate_helper_args(
    env: &mut VerifierEnv,
    state: &State,
    helper: u32,
    types: &TypeState,
    pc: usize,
) {
    match helper {
        constants::BPF_MAP_LOOKUP_ELEM => {
            // R1 = map, R2 = key pointer
            let key_size = get_map_key_size(types.get(Reg::R1), env);
            if let Some(size) = key_size {
                check_readable_arg(env, state, types, Reg::R2, size, pc);
            }
        }
        constants::BPF_MAP_UPDATE_ELEM => {
            // R1 = map, R2 = key pointer, R3 = value pointer, R4 = flags
            let (key_size, val_size) = get_map_key_value_size(types.get(Reg::R1), env);
            if let Some(size) = key_size {
                check_readable_arg(env, state, types, Reg::R2, size, pc);
            }
            if let Some(size) = val_size {
                check_readable_arg(env, state, types, Reg::R3, size, pc);
            }
        }
        constants::BPF_MAP_DELETE_ELEM => {
            // R1 = map, R2 = key pointer
            let key_size = get_map_key_size(types.get(Reg::R1), env);
            if let Some(size) = key_size {
                check_readable_arg(env, state, types, Reg::R2, size, pc);
            }
        }
        constants::BPF_GET_SOCKET_COOKIE | constants::BPF_CSUM_UPDATE  => { 
            // R1 must be PtrToCtx
            if !matches!(types.get(Reg::R1), RegType::PtrToCtx) {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            }
        }
        constants::BPF_SKB_ECN_SET_CE => {
            // R1 can be PtrToCtx or NULL
            if !matches!(types.get(Reg::R1), RegType::PtrToCtx) && !is_zero(&state.dbm, Reg::R1) {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            }
        }
        _ => {
            warn!("Helper arg not checked.");
        }
    }
}

fn check_readable_arg(
    env: &mut VerifierEnv,
    state: &State,
    types: &TypeState,
    reg: Reg,
    size: u32,
    pc: usize,
) {
    match types.get(reg) {
        RegType::PtrToStack { offset: Some(off) } => {
            access::check_stack_arg_readable(env, state, off, size as i64, pc);
        }
        RegType::PtrToStack { offset: None } => {
            // Unknown stack offset - need to use DBM bounds
            // For now, reject conservatively
            env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
        }
        RegType::PtrToMapValue { .. } => {
            // Map values are always considered initialized
        }
        RegType::PtrToPacket { .. } => {
            // Packet data is initialized (bounds checked elsewhere)
        }
        _ => {
            // Not a valid pointer type for this argument
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!("Not a valid pointer type for argument")
        }
    }
}

fn get_map_key_size(map_type: RegType, env: &VerifierEnv) -> Option<u32> {
    match map_type {
        RegType::PtrToMapObject { map_idx } => 
            env.ctx.map_defs.get(map_idx).map(|md| md.key_size),
        _ => None,
    }
}

fn get_map_key_value_size(map_type: RegType, env: &VerifierEnv) -> (Option<u32>, Option<u32>) {
    match map_type {
        RegType::PtrToMapObject { map_idx } => {
            if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                (Some(map_def.key_size), Some(map_def.value_size))
            } else {
                (None, None)
            }
        }
        _ => (None, None),
    }
}

fn check_ptr_bounds(
    env: &mut VerifierEnv,
    state: &State,
    reg: Reg,
) {
    let (lo, hi) = get_bounds(&state.dbm, reg);
    
    match state.types.get(reg) {
        RegType::PtrToMapValue { map_idx, .. } => {
            if let Some(map_def) = env.ctx.map_defs.get(map_idx) {
                let in_bounds = match (lo, hi) {
                    (Some(l), Some(h)) => l >= 0 && h < map_def.value_size as i64,
                    _ => false,
                };
                if !in_bounds {
                    env.fail(VerificationError::PointerOutOfBounds { pc: state.pc });
                }
            } else {
                warn!("This should be unreachable")
            }
        }
        RegType::PtrToStack { .. } => {
            let in_bounds = match (lo, hi) {
                (Some(l), Some(h)) => l >= constants::BPF_STACK_MIN && h <= 0,
                _ => false,
            };
            if !in_bounds {
                env.fail(VerificationError::PointerOutOfBounds { pc: state.pc });
            }
        }
        _ => {}
    }
}
