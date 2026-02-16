// src/analysis/transfer/mod.rs
//
// Transfer function for BPF instruction abstract interpretation.
// This module dispatches to specialized handlers for each instruction type.

mod alu;
mod branch;
mod call;
mod common;
mod memory;
mod types;

use crate::analysis::machine::env::VerificationError;
use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{EndianOp, Instr, Width};
use crate::zone::domain::{
    apply_and_imm, assign_interval, forget, get_interval, get_interval_i64,
    preserve_anchor_constraints,
};

/// Main transfer function - dispatches to appropriate handler based on instruction type.
pub fn transfer(env: &mut VerifierEnv, mut state: State, instr: &Instr) -> Vec<State> {
    // 1. Mark as Seen
    if state.pc < env.insn_aux_data.len() {
        env.insn_aux_data[state.pc].seen = true;
    }

    match instr {
        Instr::MovArg0 { dst } => transfer_mov_arg0(state, *dst),

        Instr::Alu {
            width,
            op,
            dst,
            src,
        } => alu::transfer_alu(env, state, *width, *op, *dst, src.clone()),

        Instr::Endian {
            dst,
            op,
            size,
            width,
        } => transfer_endian(env, state, *dst, *op, *size, *width),

        Instr::If {
            width,
            left,
            op,
            right,
            target,
        } => branch::transfer_if(env, state, *width, *left, *op, right.clone(), *target),

        Instr::Load {
            size,
            dst,
            base,
            off,
        } => memory::transfer_load(env, state, *size, *dst, *base, *off),

        Instr::Store {
            size,
            base,
            off,
            src,
        } => memory::transfer_store(env, state, *size, *base, *off, src),

        Instr::LoadPacket {
            size,
            mode,
            offset_imm,
            src,
        } => memory::transfer_packet_load(env, state, *size, *mode, *offset_imm, *src),

        Instr::LoadMap {
            dst,
            kind,
            map_fd,
            off: _,
        } => memory::transfer_map_load(env, state, *dst, *kind, *map_fd),

        Instr::Atomic {
            op,
            size,
            fetch,
            base,
            off,
            src,
        } => memory::transfer_atomic(env, state, *op, *fetch, *size, *base, *off, *src),

        Instr::Call { helper } => call::transfer_call(env, state, *helper),

        Instr::CallRel { target } => call::transfer_call_rel(env, state, *target),

        Instr::Jmp { target } => {
            state.pc = *target;
            vec![state]
        }

        Instr::Exit => transfer_exit(env, state),
    }
}

/// Transfer function for MovArg0 (initialize R1 with context pointer).
fn transfer_mov_arg0(mut state: State, dst: Reg) -> Vec<State> {
    forget(&mut state.dbm, dst);
    state.types.set(dst, RegType::PtrToCtx);
    state.pc += 1;
    vec![state]
}

/// Transfer function for Endian (byte swap) instructions.
fn transfer_endian(
    _env: &VerifierEnv,
    mut state: State,
    dst: Reg,
    op: EndianOp,
    size: u32,
    width: Width,
) -> Vec<State> {
    // 1. Types: Endian ops destroy pointers -> Scalar
    state.types.set(dst, RegType::ScalarValue);

    match op {
        EndianOp::ToLe => {
            match size {
                64 => { /* Identity for LE host; Keep constraints if Width::W64 */ }
                32 => apply_and_imm(&mut state.dbm, dst, 0xFFFF_FFFF),
                16 => apply_and_imm(&mut state.dbm, dst, 0xFFFF),
                _ => forget(&mut state.dbm, dst),
            }
        }
        EndianOp::ToBe => {
            // Big Endian always swaps on LE host -> Value changes non-linearly
            // We must forget the old value.
            // However, we know the new max value based on the swap size.
            match size {
                16 => apply_and_imm(&mut state.dbm, dst, 0xFFFF),
                32 => apply_and_imm(&mut state.dbm, dst, 0xFFFF_FFFF),
                // 64-bit BE swap: Result is u64 (if Width::W64) or u32 (if Width::W32)
                64 => forget(&mut state.dbm, dst),
                _ => forget(&mut state.dbm, dst),
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
        apply_and_imm(&mut state.dbm, dst, 0xFFFF_FFFF);
    }

    state.pc += 1;
    vec![state]
}

/// Transfer function for Exit instruction.
fn transfer_exit(env: &mut VerifierEnv, mut state: State) -> Vec<State> {
    let pc = state.pc;

    let (min, max) = get_interval(&state.dbm, Reg::R0);
    let r0_min = min.unwrap_or(i64::MIN);
    let r0_max = max.unwrap_or(i64::MAX);

    // Use the helper method on the ProgramKind stored in env
    if env.ctx.prog_kind.requires_strict_return_code() {
        if r0_min < 0 || r0_max > 1 {
            env.fail(VerificationError::InvalidReturnCode { pc: state.pc });
            return vec![];
        }
    }

    // R0 must be readable at the main frame (it's the return value)
    if state.at_main_frame() && state.types.get(Reg::R0) == RegType::NotInit {
        env.fail(VerificationError::RegisterNotReadable { pc, reg: Reg::R0 });
        return vec![];
    }

    // Check if there is any released reference
    if state.at_main_frame() && state.has_unreleased_refs() {
        println!("Unreleased reference: {:?}", state.active_refs);
        env.fail(VerificationError::UnreleasedReference);
        return vec![];
    }

    // Check if there is any unreleased locks
    if state.has_active_lock() {
        env.fail(VerificationError::UnreleasedLock);
        return vec![];
    }

    if state.num_frames() >= 8 {
        env.fail(VerificationError::MaxCallDepthExceeded { pc: state.pc });
        return vec![];
    }

    if !state.at_main_frame() {
        if matches!(state.types.get(Reg::R0), RegType::PtrToStack { .. }) {
            env.fail(VerificationError::CannotReturnStackPointer { pc: state.pc });
            return vec![];
        }
    }

    if let Some(frame) = state.pop_frame() {
        // Save callee's R0 (the return value) before restoring caller state
        let ret_type = state.types.get(Reg::R0);
        let ret_tnum = state.get_tnum(Reg::R0);
        let ret_bounds = get_interval_i64(&state.dbm, Reg::R0);
        let ret_anchor_info = state.save_anchor_info(Reg::R0);

        // Save callee's anchor constraints before overwriting
        let callee_dbm = state.dbm.clone();

        let return_pc = frame.return_pc;
        state.types = frame.caller_types;
        state.dbm = frame.caller_dbm;
        state.tnums = frame.caller_tnums;

        // Preserve anchor-to-anchor constraints from the callee.
        // These represent packet bounds (data/data_end/data_meta)
        // that were verified in the callee and remain valid.
        preserve_anchor_constraints(&mut state.dbm, &callee_dbm);

        // Re-apply R0 from callee's return value
        state.types.set(Reg::R0, ret_type);
        state.set_tnum(Reg::R0, ret_tnum);
        forget(&mut state.dbm, Reg::R0);
        assign_interval(&mut state.dbm, Reg::R0, ret_bounds.0, ret_bounds.1);

        // Restore R0's anchor relationship (e.g., packet pointer offset from AnchorData)
        if let (Some(anchor), lo, hi) = ret_anchor_info {
            if let Some(h) = hi {
                state.dbm.add_constraint(Reg::R0, anchor, h);
            }
            if let Some(l) = lo {
                state.dbm.add_constraint(anchor, Reg::R0, l);
            }
            state.dbm.close();
        }

        state.types.set(
            Reg::R10,
            RegType::PtrToStack {
                frame_level: state.current_frame_level(),
            },
        );
        state.pc = return_pc;
        vec![state]
    } else {
        vec![]
    }
}
