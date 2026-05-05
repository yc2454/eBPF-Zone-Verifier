// src/analysis/transfer/mod.rs
//
// Transfer function for BPF instruction abstract interpretation.
// This module dispatches to specialized handlers for each instruction type.

mod alu;
mod branch;
pub(crate) mod call;
mod common;
mod memory;
pub(crate) mod types;

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
            // `may_goto` (BPF_JCOND, v6.8) models a bounded back-edge.
            // The kernel inlines a per-program counter that decrements on
            // every execution of the may_goto, regardless of which edge
            // is taken; once the counter hits zero the may_goto becomes
            // a no-op (fall through). Mirroring that decrement on BOTH
            // successors is what lets the abstract interpreter actually
            // terminate: each loop iteration shrinks the budget, so
            // pruning at the loop head eventually subsumes future
            // iterations once widening (or empty live-regs) makes the
            // body's effect on tracked state stable.
            //
            // Bucket F-D: also mirror the kernel's static may_goto
            // machinery (`check_cond_jmp_op` BPF_JCOND arm, verifier.c
            // v6.15 ~L16400-16410): on each visit, find a previous
            // explored state at this same insn_idx, run
            // `widen_imprecise_scalars` to coarsen scalars whose abstract
            // value disagrees, and bump `may_goto_depth` on the queued
            // state. The depth bump powers a separate RANGE_WITHIN prune
            // class at this pc (~L19102) and defuses the EXACT inf-loop
            // trap (~L19118). Without this, loops like
            // `for (i=0; i<N && can_loop; i++) { arr[i]; cond_break; }`
            // never converge: `i` is precision-marked at `arr[i]` and
            // each iteration produces a fresh state, but the loop has
            // both an `If`-style exit (`i < N`) and a may_goto, so our
            // `force_widen_for_may_goto` (gated on `only_may_goto_exit`)
            // never fires.
            let fallthrough_pc = state.pc + 1;
            let cur_pc = state.pc;

            // Snapshot a previous explored state at this insn for the
            // widener (kernel `find_prev_entry`). The worklist driver
            // calls `record_state` before `transfer`, so
            // `explored_states[cur_pc].last()` IS the current state —
            // skip it and take the second-most-recent. Without this
            // skip the widener compares cur against itself and never
            // coarsens anything.
            let prev_snapshot: Option<State> = env
                .explored_states
                .get(&cur_pc)
                .and_then(|prev_states| {
                    let mut iter = prev_states.iter().rev().filter(|s| s.pc == cur_pc);
                    iter.next();
                    iter.next()
                })
                .cloned();

            if state.goto_budget() == 0 {
                let mut state_fall = state;
                state_fall.pc = fallthrough_pc;
                state_fall.may_goto_depth = state_fall.may_goto_depth.saturating_add(1);
                if let Some(prev) = prev_snapshot.as_ref() {
                    call::kfunc::widen_imprecise_scalars_at_iter_next(prev, &mut state_fall);
                }
                return vec![state_fall];
            }

            let mut state_taken = state.clone();
            state_taken.consume_goto_budget();
            state_taken.pc = *target;
            state_taken.may_goto_depth = state_taken.may_goto_depth.saturating_add(1);

            let mut state_fall = state;
            state_fall.consume_goto_budget();
            state_fall.pc = fallthrough_pc;
            state_fall.may_goto_depth = state_fall.may_goto_depth.saturating_add(1);

            if let Some(prev) = prev_snapshot.as_ref() {
                call::kfunc::widen_imprecise_scalars_at_iter_next(prev, &mut state_taken);
                call::kfunc::widen_imprecise_scalars_at_iter_next(prev, &mut state_fall);
            }

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
    let is_flow_keys = matches!(
        &base_ty,
        RegType::PtrToBtfId { type_name, .. } if *type_name == "bpf_flow_keys"
    );
    let rejected = matches!(
        base_ty,
        RegType::PtrToCtx
            | RegType::PtrToPacket
            | RegType::PtrToPacketMeta
            | RegType::PtrToPacketEnd
    ) || is_flow_keys;
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

    // Kernel-aligned: main-program exit return-value precision sink
    // (verifier.c v6.15 check_return_code marks R0 precise before
    // enforcing the prog-type retval range). Per-path lineage walk
    // via parent_cache_id — marks precise on this path's specific
    // cached ancestors only, not all cached states at intermediate
    // PCs.
    if state.at_main_frame()
        && let Some(hidx) = state.history_idx
    {
        env.mark_chain_precision_backward(hidx, state.parent_cache_id, Reg::R0);
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
    }
    // Kernel `check_return_code` only fires at the *main* program's
    // exit — subprog (global_func) return values are unconstrained
    // (test_global_func8::foo returns `bpf_get_prandom_u32()` and
    // upstream accepts). Don't enforce the prog-type retval rule on
    // non-main exits.

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

    // Check if there is any unreleased locks. The kernel tracks a
    // single program-level active_lock, so a subprog `exit` may leave
    // the lock held for the caller to release (mirrors `verifier_spin_lock::
    // lock_in_subprog_without_unlock`). Only enforce at the main frame.
    if state.at_main_frame() && state.has_active_lock() {
        env.fail(VerificationError::UnreleasedLock);
        return vec![];
    }

    // Check if any RCU read-side section is still open (W5.2). For
    // programs entered with the kernel's implicit RCU CS (kprobe,
    // tracepoint, raw_tp, perf_event), depth=1 at exit is the
    // kernel-supplied baseline — the kernel releases on return — so
    // tolerate it. Anything above 1 in that case, or anything > 0 in
    // sleepable / non-tracing programs, is an unreleased explicit
    // bpf_rcu_read_lock.
    let baseline = if state.implicit_rcu_at_entry { 1 } else { 0 };
    if state.rcu_read_depth > baseline {
        env.fail(VerificationError::UnreleasedRcuRead);
        return vec![];
    }

    // Main-prog exit inside a preempt-disabled region (kernel verifier.c
    // v6.15 ~L11096). Subprog exits are fine: kernel only checks at the
    // root frame's BPF_EXIT, mirroring `check_lock` callers.
    if state.at_main_frame() && state.in_preempt_disabled() {
        env.fail(VerificationError::ExitInPreemptDisabled);
        return vec![];
    }

    // Main-prog exit inside an IRQ-disabled region (kernel verifier.c
    // v6.15 ~L11086). Same shape as the preempt check above. Subprog
    // exits are fine — kernel only checks at the root frame.
    if state.at_main_frame() && state.in_irq_disabled() {
        env.fail(VerificationError::IrqState {
            pc: state.pc,
            reason: "BPF_EXIT in main prog inside bpf_local_irq_save-ed region".into(),
        });
        return vec![];
    }
    // Also reject leaked irq flag stack slots (parallel to
    // has_active_iterators above).
    let irq_leak = if state.at_main_frame() {
        state.frames.iter().any(|f| f.stack.has_unreleased_irq_flags())
    } else {
        state.frames.current().stack.has_unreleased_irq_flags()
    };
    if irq_leak {
        env.fail(VerificationError::IrqState {
            pc: state.pc,
            reason: "leaked irq flag stack slot at exit".into(),
        });
        return vec![];
    }

    // Exit-time sanity guard: depth at exit shouldn't exceed the
    // kernel's MAX_CALL_FRAMES = 8. The pre-push `> 8` check in
    // `transfer_call_rel` already prevents pushing a 9th frame, so
    // hitting this at exit means a bug in frame bookkeeping. Use the
    // same `> 8` rule so a legitimate `main → 7 subprogs → exit`
    // chain (depth = 8 at the deepest) doesn't FR.
    if state.num_frames() > 8 {
        env.fail(VerificationError::MaxCallDepthExceeded { pc: state.pc });
        return vec![];
    }

    if !state.at_main_frame() && matches!(state.types.get(Reg::R0), RegType::PtrToStack { .. }) {
        env.fail(VerificationError::CannotReturnStackPointer { pc: state.pc });
        return vec![];
    }

    // W3.4b: a callback frame's Exit doesn't merge back into the caller
    // by way of CallRel return semantics — the helper's post-call state
    // is emitted separately at the call site (see
    // `transfer_callback_helper`'s skip_state). What we DO emit here
    // (bucket E) is a SECOND post-call state at the call site's pc+1
    // that carries the cb's effects on caller-frame stack memory. This
    // mirrors the kernel's iterative cb model (verifier.c v6.15
    // ~L10903+): cb-touched scalar stack slots get widened on the
    // surviving caller state when the cb may run ≥ 2 times. For
    // nr_loops ≤ 1 (or single-shot helpers like find_vma) we keep the
    // cb's writes concretely, since there's no "previous iteration" to
    // widen against.
    if state.frames.current().is_callback() {
        if state.types.get(Reg::R0) != RegType::ScalarValue {
            env.fail(VerificationError::InvalidReturnCode { pc });
            return vec![];
        }
        // Kernel-aligned: callback return-value precision sink
        // (verifier.c v6.15 prepare_func_exit L10862). Per-path
        // lineage walk via parent_cache_id.
        if let Some(hidx) = state.history_idx {
            env.mark_chain_precision_backward(hidx, state.parent_cache_id, Reg::R0);
        }
        // W3.4c: bpf_loop / bpf_for_each_map_elem / bpf_user_ringbuf_drain
        // callbacks must return 0 (continue) or 1 (break). Timer callbacks
        // are void-returning and not constrained here.
        let cb_helper_id = state.frames.current().callback_helper();
        if matches!(
            cb_helper_id,
            Some(crate::common::constants::BPF_LOOP)
                | Some(crate::common::constants::BPF_FOR_EACH_MAP_ELEM)
                | Some(crate::common::constants::BPF_USER_RINGBUF_DRAIN)
        ) {
            let (lo, hi) = state.domain.get_interval(Reg::R0);
            if lo < 0 || hi > 1 {
                env.fail(VerificationError::InvalidReturnCode { pc });
                return vec![];
            }
        }
        return cb_exit_propagate(env, state);
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

        // Global-subprog isolation: restore the caller's rcu_read_depth
        // snapshot taken at push time. The body's bpf_rcu_read_lock /
        // _unlock calls are local to the global subprog's analysis and
        // must not leak into the caller's view (kernel verifies global
        // subprogs separately and treats their lock-state effects as
        // opaque). Closes
        // `rcu_read_lock.c::rcu_read_lock_global_subprog_unlock`.
        if let Some(snapshot) = frame.caller_rcu_read_depth_snapshot {
            state.rcu_read_depth = snapshot;
        }

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

/// Build a post-cb state at the helper call's pc+1 that carries the
/// cb's effects on caller-frame memory. Mirrors kernel's
/// `prepare_func_exit` cb-return path + `widen_imprecise_scalars`
/// (verifier.c v6.15 ~L10898–10920). Caller-frame stack writes done
/// via the cb's ctx pointer have already landed on the right frame
/// (PtrToStack carries frame_level); we pop the cb frame, restore
/// caller regs, and—if the cb may iterate ≥ 2 times—invalidate the
/// stack slots that differ from the snapshot taken at cb-entry.
fn cb_exit_propagate(env: &VerifierEnv, mut state: State) -> Vec<State> {
    use crate::analysis::machine::frame_stack::FrameLevel;
    use crate::analysis::machine::reg_types::RegType;
    use crate::analysis::transfer::call::transfer::apply_return_bounds_for_cb_helper;
    use crate::domains::tnum::Tnum;
    use std::collections::HashSet;

    let Some(frame) = state.pop_frame() else {
        return vec![];
    };
    let return_pc = frame.return_pc;
    let helper = frame.callback_helper().unwrap_or(0);
    let should_widen = frame.cb_should_widen();
    let caller_level = frame.caller_frame_level();
    let snapshot = frame.caller_stack_snapshot().cloned();
    let cb_writeable: Vec<i16> = frame.cb_writeable_caller_offsets().to_vec();

    // Restore caller regs (cb's R0 etc. are dropped).
    state.types = frame.caller_types;
    state.domain = frame.caller_domain;
    state.tnums = frame.caller_tnums;

    // Helper return value lives in R0; bounds depend on helper kind.
    state.types.set(Reg::R0, RegType::ScalarValue);
    apply_return_bounds_for_cb_helper(&mut state, helper);
    state.clear_scalar_id(Reg::R0);

    // Forget arg regs (helpers clobber R1..R5).
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        state.types.set(r, RegType::ScalarValue);
        state.domain.forget(r);
        state.set_tnum(r, Tnum::unknown());
        state.clear_scalar_id(r);
    }

    // Apply widening to caller-frame stack slots the cb touched. We
    // detect "touched" by comparing each slot against the pre-cb
    // snapshot. With cb_should_widen=false (nr_loops ≤ 1, find_vma)
    // we keep the cb's writes concretely; this lets `_ok`-style tests
    // verify with the post-cb concrete value while still abstracting
    // multi-iteration cases.
    if should_widen
        && let (Some(snap), Some(idx)) = (snapshot, caller_level)
    {
        let caller_stack = state.stack_at_mut(FrameLevel::from_index(idx));
        let mut all_offsets: HashSet<i16> = snap.slot_offsets().into_iter().collect();
        all_offsets.extend(caller_stack.slot_offsets());
        for off in all_offsets {
            let snap_slot = snap.get_slot(off);
            let cur_slot = caller_stack.get_slot(off);
            let differs = match (snap_slot, cur_slot) {
                (None, None) => false,
                (None, Some(_)) | (Some(_), None) => true,
                (Some(a), Some(b)) => a != b,
            };
            if differs {
                caller_stack.invalidate_slot(off);
            }
        }
        // Also invalidate every slot the cb body could write through
        // its ctx-pointer on ANY branch (pre-computed at env init via
        // static scan). This is the kernel's multi-iteration cb model:
        // when nr_loops > 1, different cb branches can fire on
        // different iterations, so the post-loop continuation must
        // reflect the union of all branches' effects (verifier.c v6.15
        // ~L10903 widen_imprecise_scalars over iter-state). Without
        // this, single-branch cb-exits leave non-this-branch slots
        // concrete and the continuation falsely accepts patterns that
        // require interleaved iterations (`iter_limit_bug`).
        for off in cb_writeable {
            caller_stack.invalidate_slot(off);
        }
    }

    state.pc = return_pc;

    // Bucket F-D / cb-return widener (kernel verifier.c v6.15 ~L10903-10920):
    //   prev_st = in_callback_fn ? find_prev_entry(env, state, *insn_idx) : NULL;
    //   if (prev_st)
    //       widen_imprecise_scalars(env, prev_st, state);
    //
    // The snapshot-based widening above (W3.4b cb-effect) widens stack
    // slots the cb wrote during THIS iteration. The kernel additionally
    // runs `widen_imprecise_scalars` between this post-cb state and a
    // PRIOR post-cb visit at the same continuation pc — coarsening
    // values that differ across iterations of a multi-iteration helper
    // (bpf_loop, bpf_for_each_map_elem). This is the same machinery
    // already wired at iter_next and may_goto.
    //
    // Gated on `should_widen` (set when nr_loops > 1 at the helper call
    // site). For nr_loops ≤ 1 (or single-shot helpers like find_vma) the
    // cb runs once; widening between successive call sites would
    // destroy precision the test relies on (e.g.
    // `bpf_loop_iter_limit_nested` enumerates exact post-cb values).
    //
    // Skip-cur logic mirrors the may_goto site: record_state precedes
    // transfer in the worklist driver, so the most recent cached state
    // at `return_pc` is the just-recorded current state — skip it and
    // take the previous one.
    if should_widen
        && let Some(prev_states) = env.explored_states.get(&return_pc)
    {
        let mut iter = prev_states.iter().rev().filter(|s| s.pc == return_pc);
        iter.next();
        if let Some(prev) = iter.next() {
            crate::analysis::transfer::call::kfunc::widen_imprecise_scalars_at_iter_next(
                prev, &mut state,
            );
        }
    }

    vec![state]
}
