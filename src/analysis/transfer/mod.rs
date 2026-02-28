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

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{EndianOp, Instr, Width};
use log::warn;

/// Main transfer function - dispatches to appropriate handler based on instruction type.
pub fn transfer(env: &mut VerifierEnv, mut state: State, instr: &Instr) -> Vec<State> {
    if state.pc < env.insn_aux_data.len() {
        env.insn_aux_data[state.pc].seen = true;
    }

    match instr {
        Instr::Alu {
            width,
            op,
            dst,
            src,
        } => alu::transfer_alu(env, state, *width, *op, *dst, *src),

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
        } => branch::transfer_if(env, state, *width, *left, *op, *right, *target),

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
                32 => state.domain.apply_and_imm(dst, 0xFFFF_FFFF),
                16 => state.domain.apply_and_imm(dst, 0xFFFF),
                _ => state.domain.forget(dst),
            }
        }
        EndianOp::ToBe => {
            // Big Endian always swaps on LE host -> Value changes non-linearly
            // We must forget the old value.
            // However, we know the new max value based on the swap size.
            match size {
                16 => state.domain.apply_and_imm(dst, 0xFFFF),
                32 => state.domain.apply_and_imm(dst, 0xFFFF_FFFF),
                // 64-bit BE swap: Result is u64 (if Width::W64) or u32 (if Width::W32)
                64 => state.domain.forget(dst),
                _ => state.domain.forget(dst),
            }
        }
    }

    // 3. Handle Implicit 32-bit Zero Extension
    // This provides a tighter bound [0, U32_MAX] even if the operation was "Unknown".
    if width == Width::W32 {
        state.domain.apply_and_imm(dst, 0xFFFF_FFFF);
    }

    state.pc += 1;
    vec![state]
}

/// Transfer function for Exit instruction.
fn transfer_exit(env: &mut VerifierEnv, mut state: State) -> Vec<State> {
    let pc = state.pc;

    let (r0_min, r0_max) = state.domain.get_interval(Reg::R0);

    // Use the helper method on the ProgramKind stored in env
    if env.ctx.prog_kind.requires_strict_return_code() && (r0_min < 0 || r0_max > 1) {
        env.fail(VerificationError::InvalidReturnCode { pc: state.pc });
        return vec![];
    }

    // R0 must be readable at the main frame (it's the return value)
    if state.at_main_frame() && state.types.get(Reg::R0) == RegType::NotInit {
        env.fail(VerificationError::RegisterNotReadable { pc, reg: Reg::R0 });
        return vec![];
    }

    // Check if there is any released reference
    if state.at_main_frame() && state.has_unreleased_refs() {
        warn!("Unreleased reference: {:?}", state.active_refs);
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

    if !state.at_main_frame() && matches!(state.types.get(Reg::R0), RegType::PtrToStack { .. }) {
        env.fail(VerificationError::CannotReturnStackPointer { pc: state.pc });
        return vec![];
    }

    if let Some(frame) = state.pop_frame() {
        // Save callee's R0 (the return value) before restoring caller state
        let ret_type = state.types.get(Reg::R0);
        let ret_tnum = state.get_tnum(Reg::R0);
        let ret_bounds = state.domain.get_interval(Reg::R0);
        let ret_anchor_info = state.save_anchor_info(Reg::R0);
        // Also save interval mode PtrOffset for packet pointer returns
        let ret_interval_ptr_offset = state.save_interval_ptr_offset(Reg::R0);

        // Save callee-saved registers' (R6-R9) packet range info.
        // These registers may have been updated by bounds checks in the callee.
        let callee_saved_packet_info: Vec<_> = [Reg::R6, Reg::R7, Reg::R8, Reg::R9]
            .iter()
            .map(|&r| (r, state.types.get(r), state.save_interval_ptr_offset(r)))
            .collect();

        // Save callee's anchor constraints before overwriting
        let callee_domain = state.domain.clone();

        let return_pc = frame.return_pc;
        state.types = frame.caller_types;
        state.domain = frame.caller_domain;
        state.tnums = frame.caller_tnums;

        // Preserve anchor-to-anchor constraints from the callee.
        // These represent packet bounds (data/data_end/data_meta)
        // that were verified in the callee and remain valid.
        state.domain.preserve_anchor_constraints(&callee_domain);

        // Re-apply R0 from callee's return value
        state.types.set(Reg::R0, ret_type.clone());
        state.set_tnum(Reg::R0, ret_tnum);
        state.domain.forget(Reg::R0);
        state.domain.assign_interval(Reg::R0, ret_bounds.0, ret_bounds.1);

        // Restore R0's anchor relationship (e.g., packet pointer offset from AnchorData)
        if let (Some(anchor), lo, hi) = ret_anchor_info {
            if let Some(h) = hi {
                state.domain.add_constraint(Reg::R0, anchor, h);
            }
            if let Some(l) = lo {
                state.domain.add_constraint(anchor, Reg::R0, l);
            }
            state.domain.close();
        }

        // Restore interval mode PtrOffset for packet pointer returns
        if let (Some(off), var_off_opt, range) = ret_interval_ptr_offset {
            use crate::domains::numeric::NumericDomain;
            use crate::domains::interval::PtrOffset;

            // Determine anchor from register type
            let anchor = match &ret_type {
                RegType::PtrToPacket => Some(Reg::AnchorData),
                RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
                RegType::PtrToPacketEnd => Some(Reg::AnchorDataEnd),
                _ => None,
            };

            if let Some(anchor) = anchor {
                if let NumericDomain::Interval(ref mut ivl) = state.domain {
                    let var_off = var_off_opt.unwrap_or(0);
                    let ptr_offset = PtrOffset {
                        anchor,
                        off,
                        var_off,
                        range,
                    };
                    ivl.get_mut(Reg::R0).ptr_offset = Some(ptr_offset);
                }
            }
        }

        // Restore callee-saved registers' (R6-R9) packet range info.
        // If a bounds check in the callee proved range for these registers,
        // we need to carry that forward to the caller.
        {
            use crate::domains::numeric::NumericDomain;

            for (reg, callee_type, (off_opt, var_off_opt, range)) in callee_saved_packet_info {
                // Only restore if the callee had a packet pointer with range info
                if let (Some(off), Some(range_val)) = (off_opt, range) {
                    // Determine anchor from the callee's register type
                    let anchor = match callee_type {
                        RegType::PtrToPacket => Some(Reg::AnchorData),
                        RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
                        _ => None,
                    };

                    // Only update if caller also has a packet pointer in this register
                    // and the anchor matches
                    if let Some(anchor) = anchor {
                        if matches!(state.types.get(reg), RegType::PtrToPacket | RegType::PtrToPacketMeta) {
                            if let NumericDomain::Interval(ref mut ivl) = state.domain {
                                // Check if caller's register has compatible offset info
                                if let Some(caller_ptr_off) = ivl.get_ptr_offset(reg) {
                                    if caller_ptr_off.anchor == anchor
                                        && caller_ptr_off.off == off
                                        && caller_ptr_off.var_off == var_off_opt.unwrap_or(0)
                                    {
                                        // Update range to the max of caller and callee
                                        let caller_range = caller_ptr_off.range.unwrap_or(0);
                                        if range_val > caller_range {
                                            let mut new_ptr_off = caller_ptr_off.clone();
                                            new_ptr_off.range = Some(range_val);
                                            ivl.get_mut(reg).ptr_offset = Some(new_ptr_off);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
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
