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
use crate::ast::{CallKind, EndianOp, Instr, Operand, Width};
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

        Instr::LoadSx {
            size,
            dst,
            base,
            off,
        } => memory::transfer_load_sx(env, state, *size, *dst, *base, *off),

        Instr::MovSx {
            width,
            src_bits,
            dst,
            src,
        } => alu::transfer_mov_sx(env, state, *width, *src_bits, *dst, *src),

        Instr::Store {
            size,
            base,
            off,
            src,
        } => memory::transfer_store(env, state, *size, *base, *off, src),

        Instr::LoadAcq {
            size,
            dst,
            base,
            off,
        } => {
            if reject_atomic_on_typed_ptr(env, &state, *base) {
                return vec![];
            }
            memory::transfer_load(env, state, *size, *dst, *base, *off)
        }

        Instr::StoreRel {
            size,
            base,
            off,
            src,
        } => {
            if reject_atomic_on_typed_ptr(env, &state, *base) {
                return vec![];
            }
            memory::transfer_store(env, state, *size, *base, *off, &Operand::Reg(*src))
        }

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

        Instr::Call { kind } => match *kind {
            CallKind::Helper { id } => call::transfer_call(env, state, id),
            CallKind::Kfunc { btf_id, .. } => call::transfer_kfunc(env, state, btf_id),
        },

        Instr::CallRel { target } => call::transfer_call_rel(env, state, *target),

        Instr::Jmp { target } => {
            state.pc = *target;
            vec![state]
        }

        Instr::MayGoto { target } => {
            // `may_goto` models a bounded back-edge: the kernel inlines a
            // per-program counter check that either takes the jump (counter
            // positive, decrement) or falls through (counter exhausted).
            // We fork two successors accordingly. When the budget on this
            // path is already zero, the taken edge is infeasible and only
            // the fallthrough survives — this is what guarantees
            // termination of the abstract interpreter on otherwise
            // unbounded loops. No REJECT: the kernel itself doesn't reject
            // here, it just stops iterating.
            let fallthrough_pc = state.pc + 1;
            let mut state_fall = state.clone();
            state_fall.pc = fallthrough_pc;

            if state.goto_budget() == 0 {
                return vec![state_fall];
            }

            let mut state_taken = state;
            state_taken.consume_goto_budget();
            state_taken.pc = *target;
            vec![state_taken, state_fall]
        }

        Instr::Exit => transfer_exit(env, state),
    }
}

/// Kernel rejects BPF_ATOMIC (including LOAD_ACQ / STORE_REL) against
/// ctx/packet/flow_keys pointer bases. Returns true if the program should
/// be rejected — caller then bails out without running the transfer.
fn reject_atomic_on_typed_ptr(env: &mut VerifierEnv, state: &State, base: Reg) -> bool {
    let base_ty = state.types.get(base);
    let rejected = matches!(
        base_ty,
        RegType::PtrToCtx
            | RegType::PtrToPacket
            | RegType::PtrToPacketMeta
            | RegType::PtrToPacketEnd
    );
    if rejected {
        env.fail(VerificationError::UnsupportedModernFeature {
            pc: state.pc,
            feature: "BPF_ATOMIC (LOAD_ACQ / STORE_REL) against ctx/packet pointer",
        });
    }
    rejected
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
        EndianOp::Bswap => {
            // BPF v4 BSWAP: byte-swap of the low `size` bits, independent of
            // host endianness. Result fits in `size` bits — narrow, but the
            // exact value is non-linear so the prior interval is forgotten.
            match size {
                16 => state.domain.apply_and_imm(dst, 0xFFFF),
                32 => state.domain.apply_and_imm(dst, 0xFFFF_FFFF),
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

    // Exception-callback exit: when the active analysis pass is
    // verifying an `__exception_cb` body (`analyze_exception_cb`),
    // mirror the kernel's `in_exception_callback_fn` behavior — apply
    // the main-program exit rule at the cb's exit. For fentry/fexit
    // attach flavors, that rule is R0 ∈ [0, 0] (kernel:
    // "At program exit the register R0 has ... should be ..."). We do
    // not enforce this on ordinary fentry main-program exits because
    // the existing corpus relies on the looser local behavior; the
    // tighter rule fires only inside the cb pass.
    if env.analyzing_exception_cb
        && state.at_main_frame()
        && matches!(env.ctx.attach_flavor.as_deref(), Some("fentry") | Some("fexit"))
    {
        if r0_min != 0 || r0_max != 0 {
            env.fail(VerificationError::InvalidReturnCode { pc: state.pc });
            return vec![];
        }
    }

    // Cluster B: per-attach-type retval range. When a finer rule applies
    // for the (prog_kind, attach_subtype) pair, prefer it over the coarse
    // `requires_strict_return_code` check below — the kernel's per-hook
    // ranges are tighter (e.g. cgroup/recvmsg* must return exactly 1).
    if state.at_main_frame() {
        if let Some(rule) = crate::ast::expected_retval_rule(
            env.ctx.prog_kind,
            env.ctx.attach_subtype.as_deref(),
        ) {
            let out_of_range = r0_min < rule.lo || r0_max > rule.hi;
            let needs_known = rule.require_known
                && (r0_min != r0_max
                    || state.types.get(Reg::R0) != RegType::ScalarValue);
            if out_of_range || needs_known {
                env.fail(VerificationError::InvalidReturnCode { pc: state.pc });
                return vec![];
            }
        } else if env.ctx.prog_kind.requires_strict_return_code()
            && (r0_min < 0 || r0_max > 1)
        {
            env.fail(VerificationError::InvalidReturnCode { pc: state.pc });
            return vec![];
        }
    } else if env.ctx.prog_kind.requires_strict_return_code() && (r0_min < 0 || r0_max > 1) {
        env.fail(VerificationError::InvalidReturnCode { pc: state.pc });
        return vec![];
    }

    // R0 must be readable at the main frame (it's the return value).
    // W6.4a-followon: void-returning struct_ops methods are exempt — the
    // kernel verifier doesn't require R0 to be set when the matched
    // ops-struct member's FUNC_PROTO declares a void return.
    if state.at_main_frame()
        && state.types.get(Reg::R0) == RegType::NotInit
        && !env.ctx.entry_returns_void
    {
        env.fail(VerificationError::RegisterNotReadable { pc, reg: Reg::R0 });
        return vec![];
    }

    // Check if there is any released reference
    if state.at_main_frame() && state.has_unreleased_refs() {
        warn!("Unreleased reference: {:?}", state.active_refs);
        env.fail(VerificationError::UnreleasedReference);
        return vec![];
    }

    // W3.2b: open-coded iterators must be destroyed on every exit path.
    // An Active or Drained iterator slot anywhere in the frame stack is
    // a leak — parallel to unreleased refs above.
    //
    // At main exit, walk all frames (defensive, though only frame[0] is
    // live then). At non-main exit (subprog return), check the current
    // frame: iter slots on the callee's stack vanish when the frame is
    // popped, so an undestroyed iter is a leak — kernel emits
    // "returning from callee: ... Unreleased reference".
    let iter_leak = if state.at_main_frame() {
        state.frames.iter().any(|f| f.stack.has_active_iterators())
    } else {
        state.frames.current().stack.has_active_iterators()
    };
    if iter_leak {
        env.fail(VerificationError::UnreleasedIterator);
        return vec![];
    }

    // W4.2c: ref-bearing dynptr slots (today: ringbuf reservations)
    // must be submitted or discarded on every exit path. Non-ref
    // dynptrs (Local/Skb/Xdp) are pure metadata over a pointer and
    // need no release. Same per-frame logic as iterators above.
    let dynptr_leak = if state.at_main_frame() {
        state
            .frames
            .iter()
            .any(|f| f.stack.has_unreleased_dynptr_refs())
    } else {
        state.frames.current().stack.has_unreleased_dynptr_refs()
    };
    if dynptr_leak {
        env.fail(VerificationError::UnreleasedDynptr);
        return vec![];
    }

    // Check if there is any unreleased locks
    if state.has_active_lock() {
        env.fail(VerificationError::UnreleasedLock);
        return vec![];
    }

    // Check if any RCU read-side section is still open (W5.2)
    if state.in_rcu_read_section() {
        env.fail(VerificationError::UnreleasedRcuRead);
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

    // W3.4b: a callback frame's Exit doesn't return into the caller —
    // the helper's post-call state is emitted separately at the call
    // site. We only validate the callback's R0 (must be a scalar — for
    // bpf_loop specifically the kernel requires 0 or 1; we keep the
    // check loose here and let future work tighten) and drop the path.
    if state.frames.current().is_callback() {
        if state.types.get(Reg::R0) != RegType::ScalarValue {
            env.fail(VerificationError::InvalidReturnCode { pc });
            return vec![];
        }
        // W3.4c: bpf_loop callback must return 0 (continue) or 1 (break).
        // Other callback helpers use their return value differently
        // (for_each_map_elem: 0/1 too; timer: void) — only tighten what
        // we know is kernel-enforced.
        if state.frames.current().callback_helper() == Some(crate::common::constants::BPF_LOOP) {
            let (lo, hi) = state.domain.get_interval(Reg::R0);
            if lo < 0 || hi > 1 {
                env.fail(VerificationError::InvalidReturnCode { pc });
                return vec![];
            }
        }
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
        state
            .domain
            .assign_interval(Reg::R0, ret_bounds.0, ret_bounds.1);

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
        crate::analysis::transfer::call::transfer::restore_interval_ptr_offset_from_return(
            &mut state.domain,
            &ret_type,
            ret_interval_ptr_offset,
        );

        // Restore callee-saved registers' (R6-R9) packet range info.
        // If a bounds check in the callee proved range for these registers,
        // we need to carry that forward to the caller.
        crate::analysis::transfer::call::transfer::restore_callee_interval_packet_info(
            &mut state.domain,
            &state.types,
            callee_saved_packet_info,
        );

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
