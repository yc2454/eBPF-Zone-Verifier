// src/analysis/transfer/mod.rs
//
// Transfer function for BPF instruction abstract interpretation.
// This module dispatches to specialized handlers for each instruction type.

mod alu;
mod branch;
mod call;
mod memory;
mod refinement;
mod types;
mod common;
mod packet_load;
mod map_load;

use crate::analysis::env::VerifierEnv;
use crate::analysis::state::State;
use crate::analysis::reg_types::RegType;
use crate::ast::{Instr, EndianOp, Width};
use crate::zone::domain::{Reg, forget, assign_and_mask, bit_and_const};

/// Main transfer function - dispatches to appropriate handler based on instruction type.
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
            alu::transfer_alu(env, state, *width, *op, *dst, src.clone()),
        
        Instr::Endian { dst, op, size, width } => 
            transfer_endian(env, state, *dst, *op, *size, *width),
        
        Instr::If { width, left, op, right, target } => 
            branch::transfer_if(env, state, *width, *left, *op, right.clone(), *target),
        
        Instr::Load { size, dst, base, off } => 
            memory::transfer_load(env, state, *size, *dst, *base, *off),
        
        Instr::Store { size, base, off, src } => 
            memory::transfer_store(env, state, *size, *base, *off, src),

        Instr::LoadPacket { size, mode, offset_imm, src } => 
            packet_load::transfer_packet_load(env, state, *size, *mode, *offset_imm, *src),

        Instr::LoadMap { dst, kind, map_fd, off } => 
            map_load::transfer_map_load(env, state, *dst, *kind, *map_fd),
        
        Instr::AtomicAdd { size, base, off, src } => 
            memory::transfer_atomic_add(env, state, *size, *base, *off, *src),
        
        Instr::Call { helper } => 
            call::transfer_call(env, state, *helper),
        
        Instr::CallRel { target } => 
            call::transfer_call_rel(env, state, *target),
        
        Instr::Jmp { target } => {
            state.pc = *target;
            vec![state]
        },
        
        Instr::Exit => vec![],
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
