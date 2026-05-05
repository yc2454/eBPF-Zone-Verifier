use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/call/transfer.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{PtrFlags, RegType};
use crate::analysis::machine::state::State;
use crate::analysis::transfer::types::{
    helper_invalidates_packets, update_call_rel_types, update_call_types,
};
use crate::ast::ProgramKind;
use crate::common::constants;
use crate::domains::interval::new_scalar_id;
use crate::domains::numeric::NumericDomain;
use crate::domains::tnum::Tnum;
use log::{debug, error, trace};

use super::checks::{check_mem_size_pairs, is_valid_helper_id, validate_helper_args};
use super::signatures::get_helper_proto;

/// Transfer function for helper Call instructions.
pub(crate) fn transfer_call(env: &mut VerifierEnv, mut state: State, helper: u32) -> Vec<State> {
    let in_types = state.types.clone();
    let pc = state.pc;

    // =======================================================================
    // Check if helper ID is valid
    // =======================================================================
    if !is_valid_helper_id(helper) {
        env.fail(VerificationError::InvalidHelperId { pc, helper });
        return vec![];
    }

    // ========================================================================
    // Check if the call is forbidden under an active lock
    // ========================================================================
    if state.has_active_lock() && !allowed_while_in_active_lock(helper) {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R0 });
        return vec![];
    }

    // ========================================================================
    // Validate pointer-size pairs
    // ========================================================================
    debug!("[Verifier] pc {}: checking mem size pairs", pc);
    if let Some(p) = get_helper_proto(helper)
        && !check_mem_size_pairs(env, &state, &p, pc)
    {
        return vec![];
    }

    // ========================================================================
    // Validate helper arguments BEFORE executing
    // ========================================================================
    debug!("[Verifier] pc {}: validating helper arguments", pc);
    validate_helper_args(env, &state, helper, &in_types, pc);

    // ========================================================================
    // SPECIAL CASES
    // ========================================================================

    // bpf_tail_call
    if helper == constants::BPF_TAIL_CALL {
        if state.has_unreleased_refs() {
            error!("Entering tail calls but has unreleased references!");
            env.fail(VerificationError::UnreleasedReference {});
            return vec![];
        }
        // Kernel `check_lock` path (verifier.c v6.15 ~L11096) gates
        // tail_call alongside BPF_EXIT under preempt-disable: tail-calling
        // out of a preempt-disabled region would jump into a different
        // program with the disable count leaked.
        if state.in_preempt_disabled() {
            env.fail(VerificationError::TailCallInPreemptDisabled { pc });
            return vec![];
        }
        // Kernel `check_lock` (verifier.c v6.15 ~L11086) also rejects
        // bpf_tail_call inside an irq-disabled region.
        if state.in_irq_disabled() {
            env.fail(VerificationError::IrqState {
                pc,
                reason: "bpf_tail_call inside bpf_local_irq_save-ed region".into(),
            });
            return vec![];
        }
        // Kernel `verifier.c` v6.15 ~L11069: bpf_tail_call cannot be
        // used inside a `bpf_rcu_read_lock`-ed region — the tail-call
        // jumps into a different program with the RCU read lock leaked.
        // Mirrors `tailcall_fail::reject_tail_call_rcu_lock`. Re-uses
        // the existing InvalidArgType / R0 family — no dedicated
        // variant for this rejection family elsewhere.
        if state.in_rcu_read_section() {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R0 });
            return vec![];
        }
        update_call_types(env, &in_types, &mut state, helper);

        for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            state.domain.forget(r);
        }

        // Cluster D4: tail-called program may rewrite packet contents, so
        // any packet pointer in callee-saved regs or stack slots is no
        // longer valid afterwards. Invalidate them — accesses through
        // such pointers must be rejected unless re-derived from
        // skb->data after the tail call.
        for r in Reg::ALL {
            if r == Reg::R10 {
                continue;
            }
            match state.types.get(r) {
                RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta => {
                    state.types.set(r, RegType::NotInit);
                    state.domain.forget(r);
                }
                _ => {}
            }
        }
        for frame in state.frames.iter_mut() {
            for offset in frame.stack.slot_offsets() {
                let ty = frame.stack.get_slot_type(offset);
                if matches!(
                    ty,
                    RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta
                ) {
                    frame.stack.set_slot_type(offset, RegType::NotInit, None);
                }
            }
            // Caller-saved register snapshots (r6-r9) restored on subprog
            // exit must also be invalidated — otherwise main resumes with
            // a stale packet pointer that survived the tail-call. Mirrors
            // kernel `clear_all_pkt_pointers` walking every frame.
            for r in [Reg::R6, Reg::R7, Reg::R8, Reg::R9] {
                if matches!(
                    frame.caller_types.get(r),
                    RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta
                ) {
                    frame.caller_types.set(r, RegType::NotInit);
                }
            }
        }

        state.pc += 1;
        return vec![state];
    }

    // Special check for sk_release: R1 must have a reference
    if helper == constants::BPF_SK_RELEASE && state.types.get(Reg::R1).get_ref_id().is_none() {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
        return vec![];
    }

    // bpf_sk_release: not allowed in flow_dissector / sockops / tracing
    // / sock-cgroup / lwt-* prog types (kernel's per-prog-type
    // func_proto returns NULL for BPF_FUNC_sk_release in these).
    // Closes the cluster-A sockmap_mutate FA on
    // `test_flow_dissector_update` exposed once we widened
    // `bpf_map_update_elem` R3 for SOCKMAP/SOCKHASH — without the
    // widening, the test was rejected at the update site; with it,
    // execution reaches sk_release, which the kernel separately
    // forbids in flow_dissector.
    if helper == constants::BPF_SK_RELEASE
        && matches!(
            env.ctx.prog_kind,
            crate::ast::ProgramKind::FlowDissector
                | crate::ast::ProgramKind::SockOps
                | crate::ast::ProgramKind::Tracing
                | crate::ast::ProgramKind::Tracepoint
                | crate::ast::ProgramKind::RawTracepoint
                | crate::ast::ProgramKind::RawTracepointWritable
                | crate::ast::ProgramKind::Lsm
                | crate::ast::ProgramKind::PerfEvent
                | crate::ast::ProgramKind::Kprobe
        )
    {
        env.fail(VerificationError::HelperNotAllowedForProgram {
            pc,
            helper,
            kind: env.ctx.prog_kind,
        });
        return vec![];
    }

    // bpf_per_cpu_ptr / bpf_this_cpu_ptr: R1 must be a PERCPU-flagged
    // pointer. Kernel `check_helper_call` reports "type=<actual>
    // expected=percpu_ptr_" for anything else (verifier.c v6.15
    // ARG_PTR_TO_PERCPU_BTF_ID dispatch). Accept `PtrToMapKptr*` and
    // `PtrToBtfId*` carrying the PERCPU flag; reject Scalar and other
    // non-percpu pointer types.
    if helper == constants::BPF_THIS_CPU_PTR || helper == constants::BPF_PER_CPU_PTR {
        let r1 = state.types.get(Reg::R1);
        let percpu_ok = matches!(
            r1,
            RegType::PtrToMapKptr { .. }
                | RegType::PtrToMapKptrOrNull { .. }
                | RegType::PtrToBtfId { .. }
                | RegType::PtrToBtfIdOrNull { .. }
        ) && r1
            .ptr_flags()
            .contains(crate::analysis::machine::reg_types::PtrFlags::PERCPU);
        if !percpu_ok {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
    }

    // bpf_kptr_xchg(&map_value->kptr_field, new_obj):
    //   - R1 must be a `PtrToMapValue` whose constant offset exactly hits
    //     a *referenced* kptr slot (Ref/Rcu/Percpu). Unref slots reject:
    //     kernel "off=N kptr isn't referenced kptr".
    //   - R2 must be either NULL (scalar 0) or a reference-tracked
    //     pointer (`get_ref_id().is_some()`). Kernel "R2 must be referenced".
    //   - Return R0: `PtrToMapKptrOrNull` carrying the slot's
    //     `pointee_btf_id` and matching flags, with a fresh `ref_id` —
    //     this is the *previous* slot contents, ownership transferred to
    //     the program. R2's ref is consumed (transferred into the map).
    if helper == constants::BPF_KPTR_XCHG {
        let r1 = state.types.get(Reg::R1);
        let RegType::PtrToMapValue {
            offset: r1_off_opt,
            map_idx,
            ..
        } = r1
        else {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        };
        let final_off = crate::analysis::transfer::memory::map::resolve_const_map_off(
            &state, Reg::R1, r1_off_opt, 0,
        );
        let Some(off_val) = final_off else {
            env.fail(VerificationError::KptrAccessVariableOffset { pc, map_idx });
            return vec![];
        };
        let map_def = match env.ctx.map_defs.get(map_idx) {
            Some(m) => m,
            None => {
                env.fail(VerificationError::MapNotFound { pc, map_idx });
                return vec![];
            }
        };
        let Some(field) =
            crate::analysis::transfer::memory::map::kptr_field_at(map_def, off_val, 8)
        else {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        };
        use crate::parsing::elf::KptrFieldKind;
        if matches!(field.kind, KptrFieldKind::Unref | KptrFieldKind::Uptr) {
            // Unref kptr: "off=N kptr isn't referenced kptr".
            // Uptr: kptr_xchg has no meaning on a userspace-pointer slot —
            // mirror the unref path's rejection.
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
        let pointee_btf_id = field.pointee_btf_id;
        let slot_flags = match field.kind {
            KptrFieldKind::Ref => crate::analysis::machine::reg_types::PtrFlags::MEM_ALLOC,
            KptrFieldKind::Rcu => crate::analysis::machine::reg_types::PtrFlags::RCU,
            KptrFieldKind::Percpu => crate::analysis::machine::reg_types::PtrFlags::PERCPU,
            KptrFieldKind::Unref | KptrFieldKind::Uptr => {
                unreachable!("rejected above")
            }
        };

        // R2: either NULL (scalar 0) or a ref-tracked pointer.
        let r2 = state.types.get(Reg::R2);
        let r2_ref = r2.get_ref_id();
        let r2_is_null = matches!(r2, RegType::ScalarValue) && state.domain.proven_zero(Reg::R2);
        if r2_ref.is_none() && !r2_is_null {
            // "R2 must be referenced"
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R2 });
            return vec![];
        }

        // R2 pointee-type compat (kernel `map_kptr_match_type`,
        // verifier.c v6.15 L5780 `btf_struct_ids_match`). For Ref slots
        // the kernel demands a strict struct-name match between R2's
        // pointee BTF and the kptr field's pointee BTF — different
        // BTFs (vmlinux / module / prog) are normalized via the type
        // name. Without this, `bpf_obj_new(struct node_data2)` followed
        // by `bpf_kptr_xchg(&mapval->node /* expects node_data */, ...)`
        // is accepted as the FA on local_kptr_stash_fail::stash_rb_nodes
        // showed. Skip the check when R2 is null (no pointee) or its
        // pointee BTF id is unknown (lite-scope producers).
        if !r2_is_null {
            let r2_pointee = match r2 {
                RegType::PtrToOwnedKptr { pointee_btf_id, .. } => pointee_btf_id,
                RegType::PtrToMapKptr { pointee_btf_id, .. } => Some(pointee_btf_id),
                _ => None,
            };
            if let Some(r2_id) = r2_pointee {
                let kptr_name = env.ctx.btf.struct_name(pointee_btf_id);
                let r2_name = env.ctx.btf.struct_name(r2_id);
                if let (Some(a), Some(b)) = (kptr_name, r2_name)
                    && a != b
                {
                    env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R2 });
                    return vec![];
                }
            }
        }

        // Consume R2's ref (transfer ownership into the map).
        if let Some(id) = r2_ref {
            state.release_ref(id);
            state.invalidate_ref(id);
        }

        // R0 = previous slot contents: PtrToMapKptrOrNull, fresh ref_id.
        let new_ref = state.acquire_ref();
        state.types.set(
            Reg::R0,
            RegType::PtrToMapKptrOrNull {
                pointee_btf_id,
                ref_id: Some(new_ref),
                flags: slot_flags,
            },
        );
        state.domain.forget(Reg::R0);
        state.clear_scalar_id(Reg::R0);

        // Forget caller-saved scalars (R1..R5) per helper-call ABI.
        for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            state.domain.forget(r);
        }

        state.pc += 1;
        return vec![state];
    }

    // bpf_dynptr_from_mem: R1 (data pointer) must not be a stack pointer.
    // The kernel's "Unsupported reg type fp for bpf_dynptr_from_mem data"
    // — wrapping a stack region as a Local dynptr would let the dynptr
    // outlive its frame. The generic `PtrToMem` validator accepts stack
    // for most helpers, so we special-case here.
    if helper == constants::BPF_DYNPTR_FROM_MEM
        && matches!(state.types.get(Reg::R1), RegType::PtrToStack { .. })
    {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
        return vec![];
    }

    // ========================================================================
    // Proto-flag-driven pre-call mutations (W5.2)
    //
    // bpf_spin_lock / _unlock and bpf_rcu_read_lock / _unlock all run
    // their state mutation here. Arg shape is already validated by
    // `validate_helper_args` (MapValueSpecial { SpinLock } for the lock
    // helpers); this hook only handles the lock/RCU state machine and
    // its rejection cases.
    if let Some(p) = get_helper_proto(helper)
        && !apply_pre_call_lock_flags(env, &mut state, helper, &p)
    {
        return vec![];
    }

    // bpf_sock_map_update: only allowed in BPF_PROG_TYPE_SOCK_OPS programs
    if helper == constants::BPF_SOCK_MAP_UPDATE
        && !matches!(env.ctx.prog_kind, ProgramKind::SockOps)
    {
        env.fail(VerificationError::HelperNotAllowedForProgram {
            pc,
            helper,
            kind: env.ctx.prog_kind,
        });
        return vec![];
    }

    // F: sockmap/sockhash mutation via map_update_elem / map_delete_elem.
    // Kernel's `may_update_sockmap` (net/core/sock_map.c) accepts every
    // prog type except RawTracepoint / RawTracepointWritable (the
    // verifier_sockmap_mutate.c `__failure` corpus pins down only those
    // two as rejected). Mirror that denylist instead of an allowlist so
    // SocketFilter / Tracing / Xdp / SkLookup / SkReuseport-mapped-Unknown
    // / etc. all pass without enumeration.
    if matches!(
        helper,
        constants::BPF_MAP_UPDATE_ELEM | constants::BPF_MAP_DELETE_ELEM
    ) {
        let map_idx = match state.types.get(Reg::R1) {
            RegType::PtrToMapObject { map_idx } => Some(map_idx),
            _ => None,
        };
        if let Some(idx) = map_idx
            && let Some(map_def) = env.ctx.map_defs.get(idx)
            && matches!(
                map_def.type_,
                constants::BPF_MAP_TYPE_SOCKMAP | constants::BPF_MAP_TYPE_SOCKHASH
            )
            && matches!(
                env.ctx.prog_kind,
                ProgramKind::RawTracepoint | ProgramKind::RawTracepointWritable
            )
        {
            env.fail(VerificationError::HelperNotAllowedForProgram {
                pc,
                helper,
                kind: env.ctx.prog_kind,
            });
            return vec![];
        }
    }

    // bpf_ktime_get_coarse_ns: not in the helper whitelist for tracing
    // program types (kprobe, tracepoint, perf_event, raw_tracepoint*).
    // Mirrors kernel's per-prog-type helper allowlist (D1).
    if helper == constants::BPF_KTIME_GET_COARSE_NS
        && matches!(
            env.ctx.prog_kind,
            ProgramKind::Kprobe
                | ProgramKind::Tracepoint
                | ProgramKind::PerfEvent
                | ProgramKind::RawTracepoint
                | ProgramKind::RawTracepointWritable
        )
    {
        env.fail(VerificationError::HelperNotAllowedForProgram {
            pc,
            helper,
            kind: env.ctx.prog_kind,
        });
        return vec![];
    }

    // bpf_d_path is restrictive
    if helper == constants::BPF_D_PATH {
        if !matches!(env.ctx.prog_kind, ProgramKind::Tracing | ProgramKind::Lsm) {
            env.fail(VerificationError::HelperNotAllowedForProgram {
                pc,
                helper,
                kind: env.ctx.prog_kind,
            });
            return vec![];
        } else if matches!(env.ctx.prog_kind, ProgramKind::Tracing)
            && (matches!(env.ctx.kfunc.as_deref(), Some("d_path"))
                || matches!(env.ctx.attach_subtype.as_deref(), Some("d_path")))
        {
            env.fail(VerificationError::HelperNotAllowedForProgram {
                pc,
                helper,
                kind: env.ctx.prog_kind,
            });
            return vec![];
        }
    }

    // W3.4b: callback-taking helpers (bpf_loop / bpf_for_each_map_elem /
    // bpf_timer_set_callback) split into two successors:
    //   - "skip": helper returns to pc+1 with its normal return-value
    //     bounds; the callback body is not treated as executing along
    //     this path (abstractly: zero iterations).
    //   - "enter callback": push a callback-flagged frame at the
    //     subprog entry with typed args. On the callback's Exit we
    //     drop the path (see `transfer_exit`), so only the skip path
    //     carries helper post-state forward.
    if is_callback_helper(helper) {
        return transfer_callback_helper(env, state, &in_types, helper);
    }

    // bpf_get_local_storage doesn't not support type 1 map and flag must be 0
    if helper == constants::BPF_GET_LOCAL_STORAGE {
        if let RegType::PtrToMapObject { map_idx } = state.types.get(Reg::R1)
            && let Some(map_def) = env.ctx.map_defs.get(map_idx)
            && map_def.type_ == constants::BPF_MAP_TYPE_HASH
        {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
        if !state.domain.proven_zero(Reg::R2) {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R2 });
            return vec![];
        }
    }

    // ========================================================================
    // Normal helper handling
    // ========================================================================

    // 1. Update types
    update_call_types(env, &in_types, &mut state, helper);

    // 2. Apply return value bounds for specific helpers
    apply_return_bounds(&mut state, helper);

    // 2.1 Scalar ID for helper return value.
    // An unknown scalar R0 gets a fresh id so that copies of it can later
    // be linked and refined together (W2.1c).  Pointer or constant returns
    // don't need scalar linking.
    use crate::analysis::machine::reg_types::RegType;
    if state.types.get(Reg::R0) == RegType::ScalarValue
        && state.get_tnum(Reg::R0).is_unknown()
    {
        state.alloc_scalar_id(Reg::R0);
    } else {
        state.clear_scalar_id(Reg::R0);
    }

    // 2.5 Initialize memory buffers for PtrToUninitMem arguments
    initialize_uninit_mem_args(&mut state, &in_types, helper);

    // 3. Update DBM - forget caller-saved registers and reset Tnums.
    // W7.2: skip for fastcall helpers — kernel guarantees R1..R5 are
    // preserved, so clang-emitted no-spill sequences must keep their
    // pre-call values + tnums + scalar_ids visible to the verifier.
    if !super::signatures::is_fastcall_helper(helper) {
        for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            state.domain.forget(r);
            state.set_tnum(r, Tnum::unknown());
            state.clear_scalar_id(r);
        }
    }

    // 4. Forget packet pointer DBM entries if they were invalidated
    if helper_invalidates_packets(helper) {
        for r in Reg::ALL {
            if r != Reg::R10 {
                match in_types.get(r) {
                    RegType::PtrToPacket | RegType::PtrToPacketEnd | RegType::PtrToPacketMeta => {
                        state.domain.forget(r);
                    }
                    _ => {}
                }
            }
        }
        state.domain.reset_packet_anchors();
    }

    // 5. Advance PC and return
    state.pc += 1;
    vec![state]
}

/// Initializes stack slots that were passed as PtrToUninitMem helper arguments.
fn initialize_uninit_mem_args(
    state: &mut State,
    in_types: &crate::analysis::machine::reg_types::TypeState,
    helper: u32,
) {
    use super::signatures::ArgKind;
    use crate::analysis::transfer::types::update_store_types;
    use crate::ast::MemSize;

    if let Some(sig) = get_helper_proto(helper) {
        for pair in sig.mem_size_pairs {
            if let Some(ptr_arg_type) = sig.args.get(pair.ptr_reg.idx().saturating_sub(2))
                && matches!(
                    ptr_arg_type,
                    ArgKind::PtrToUninitMem | ArgKind::PtrToUninitMemOrNull
                )
            {
                if let RegType::PtrToStack { frame_level } = in_types.get(pair.ptr_reg) {
                    if let Some(off) = state.domain.get_distance_fixed(pair.ptr_reg, Reg::R10) {
                        let (_, max_size) = state.domain.get_interval(pair.size_reg);
                        {
                            if max_size != i64::MAX && max_size > 0 {
                                let max_bytes = (max_size as usize).min(512); // Bound to max stack size just in case
                                let stack = state.stack_at_mut(frame_level);
                                for i in 0..max_bytes {
                                    if let Ok(slot) = i16::try_from(off + i as i64) {
                                        update_store_types(
                                            stack,
                                            RegType::ScalarValue,
                                            MemSize::U8,
                                            Some(slot as i64),
                                        );
                                    }
                                }
                            }
                        }
                    } else {
                        trace!("Could not get fixed distance to R10");
                    }
                } else {
                    trace!(
                        "Arg is NOT PtrToStack, it is {:?}",
                        state.types.get(pair.ptr_reg)
                    );
                }
            }
        }
    }
}

/// Apply return value bounds based on helper semantics.
/// Public re-export of `apply_return_bounds` for the cb-Exit
/// propagation path in `transfer/mod.rs`. The cb-Exit path needs the
/// same R0 bounds the helper would normally produce on its skip-path,
/// minus the side-effect modeling that depends on caller-side
/// `in_types`. `apply_return_bounds` is pure on-state.
pub(crate) fn apply_return_bounds_for_cb_helper(state: &mut State, helper: u32) {
    apply_return_bounds(state, helper);
}

fn apply_return_bounds(state: &mut State, helper: u32) {
    state.domain.forget(Reg::R0);
    state.set_tnum(Reg::R0, Tnum::unknown());
    match helper {
        constants::BPF_REDIRECT => {
            state.domain.assume_ge_imm(Reg::R0, 0);
            state.domain.assume_le_imm(Reg::R0, 7);
        }
        constants::BPF_FIB_LOOKUP => {
            state.domain.assume_ge_imm(Reg::R0, 0);
            state.domain.assume_le_imm(Reg::R0, 8);
        }
        constants::BPF_MAP_UPDATE_ELEM
        | constants::BPF_MAP_DELETE_ELEM
        | constants::BPF_SKB_STORE_BYTES
        | constants::BPF_SKB_LOAD_BYTES
        | constants::BPF_XDP_ADJUST_HEAD
        | constants::BPF_L3_CSUM_REPLACE
        | constants::BPF_L4_CSUM_REPLACE
        | constants::BPF_GET_CURRENT_COMM
        | constants::BPF_SKB_VLAN_PUSH
        | constants::BPF_SKB_VLAN_POP
        | constants::BPF_SOCK_MAP_UPDATE => {
            // Returns 0 on success, or -errno
            state.domain.assume_le_imm(Reg::R0, 0);
            state.domain.assume_ge_imm(Reg::R0, -constants::MAX_ERRNO);
        }
        constants::BPF_GET_PRANDOM_U32
        | constants::BPF_GET_CGROUP_CLASS_ID
        | constants::BPF_GET_HASH_RECALC => {
            // Returns a positive u32
            state.domain.assume_ge_imm(Reg::R0, 0);
            state.domain.assume_le_imm(Reg::R0, 0xFFFF_FFFF);
            state.set_tnum(Reg::R0, Tnum::u32_unknown());
            // Assign scalar_id for tracking related scalars
            interval_set_scalar_id(&mut state.domain, Reg::R0);
        }
        constants::BPF_CSUM_DIFF => {
            // Returns a positive u32 (checksum) or negative error
            state.domain.assume_ge_imm(Reg::R0, -constants::MAX_ERRNO);
            state.domain.assume_le_imm(Reg::R0, 0xFFFF_FFFF);
            state.set_tnum(Reg::R0, Tnum::u32_unknown());
        }
        constants::BPF_GET_TASK_STACK => {
            let pairs = get_helper_proto(helper).map(|p| p.mem_size_pairs).unwrap_or(&[]);
            let size_reg = pairs[0].size_reg;
            let (_, hi) = state.domain.get_interval(size_reg);
            state.domain.assume_le_imm(Reg::R0, hi);
        }
        constants::BPF_GET_STACK => {
            let pairs = get_helper_proto(helper).map(|p| p.mem_size_pairs).unwrap_or(&[]);
            let size_reg = pairs[0].size_reg;
            let (_, hi) = state.domain.get_interval(size_reg);
            state.domain.assume_le_imm(Reg::R0, hi);
            state.domain.assume_ge_imm(Reg::R0, -constants::MAX_ERRNO);
        }
        constants::BPF_KFUNC_CALL_DUMMY => {
            // Assume unsupported external kfuncs return an unknown opaque pointer that can be dereferenced
            state.types.set(
                Reg::R0,
                RegType::PtrToBtfId {
                    type_name: "unknown",
                    flags: PtrFlags::UNTRUSTED,
                    ref_id: None,
                },
            );
        }
        _ => {}
    }
}

/// True when `helper` takes a callback pointer argument (W3.4b + W6.5).
fn is_callback_helper(helper: u32) -> bool {
    matches!(
        helper,
        constants::BPF_LOOP
            | constants::BPF_FOR_EACH_MAP_ELEM
            | constants::BPF_TIMER_SET_CALLBACK
            | constants::BPF_USER_RINGBUF_DRAIN
            | constants::BPF_FIND_VMA
    )
}

/// Which register holds the callback pointer for `helper`.
fn callback_arg_reg(helper: u32) -> Reg {
    match helper {
        constants::BPF_LOOP => Reg::R2,
        constants::BPF_FOR_EACH_MAP_ELEM => Reg::R2,
        constants::BPF_TIMER_SET_CALLBACK => Reg::R2,
        // W6.5: bpf_user_ringbuf_drain(map, callback, ctx, flags)
        constants::BPF_USER_RINGBUF_DRAIN => Reg::R2,
        // bpf_find_vma(task, addr, callback, callback_ctx, flags)
        constants::BPF_FIND_VMA => Reg::R3,
        _ => unreachable!(),
    }
}

/// Transfer for callback-taking helpers. Emits the skip successor (normal
/// helper post-state at pc+1) and the enter-callback successor (pushes a
/// callback frame at subprog_pc with typed args). See `is_callback_helper`.
fn transfer_callback_helper(
    env: &mut VerifierEnv,
    state: State,
    in_types: &crate::analysis::machine::reg_types::TypeState,
    helper: u32,
) -> Vec<State> {
    let pc = state.pc;
    let cb_reg = callback_arg_reg(helper);
    let RegType::PtrToCallback { subprog_pc } = state.types.get(cb_reg) else {
        env.fail(VerificationError::InvalidArgType { pc, reg: cb_reg });
        return vec![];
    };
    let cb_entry = subprog_pc as usize;

    // W3.4c: bpf_timer_set_callback must be registered with no held locks
    // and no unreleased refs — the callback runs asynchronously, so any
    // state the verifier is still tracking on the caller frame would be
    // leaked. (Other callback helpers are synchronous and rely on the
    // generic active-lock check in `transfer_call` above.)
    if helper == constants::BPF_TIMER_SET_CALLBACK
        && (state.has_active_lock() || state.has_unreleased_refs())
    {
        env.fail(VerificationError::InvalidArgType { pc, reg: cb_reg });
        return vec![];
    }

    // Successor A: skip the callback and emit the helper's post-state.
    let mut skip_state = state.clone();
    // Kernel-pessimism for sync callbacks: the callback could have
    // re-initialized any dynptr reachable through its ctx arg, which
    // invalidates slices tagged with the old `dynptr_id`. Mirrors the
    // `bpf_for_each_reg_in_vstate` sweep done by
    // `destroy_if_dynptr_stack_slot` (verifier.c v6.15 L913-919) once
    // the kernel determines the ctx may alias a dynptr stack slot.
    // Without this, `invalid_data_slices` (dynptr_fail.c) would accept
    // a `*slice = 1` after `bpf_loop(.., &ptr, 0)`.
    let cb_ctx_reg = match helper {
        constants::BPF_LOOP
        | constants::BPF_FOR_EACH_MAP_ELEM
        | constants::BPF_USER_RINGBUF_DRAIN => Some(Reg::R3),
        constants::BPF_FIND_VMA => Some(Reg::R4),
        _ => None,
    };
    if let Some(ctx_reg) = cb_ctx_reg
        && let RegType::PtrToStack { frame_level } = skip_state.types.get(ctx_reg)
        && let Some(off) = skip_state.domain.get_distance_fixed(ctx_reg, Reg::R10)
        && let Ok(base_off) = i16::try_from(off)
    {
        let touched = skip_state
            .stack_at(frame_level)
            .dynptr_pairs_touched_by_write(base_off as i64, 16);
        if !touched.is_empty() {
            let stack = skip_state.stack_at_mut(frame_level);
            for (b, _) in &touched {
                stack.stack_clear_dynptr(*b);
                stack.stack_clear_dynptr(*b + 8);
            }
            for (_, vid) in &touched {
                skip_state.invalidate_dynptr_slices(*vid);
            }
        }
    }
    update_call_types(env, in_types, &mut skip_state, helper);
    apply_return_bounds(&mut skip_state, helper);
    if skip_state.types.get(Reg::R0) == RegType::ScalarValue
        && skip_state.get_tnum(Reg::R0).is_unknown()
    {
        skip_state.alloc_scalar_id(Reg::R0);
    } else {
        skip_state.clear_scalar_id(Reg::R0);
    }
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        skip_state.domain.forget(r);
        skip_state.set_tnum(r, Tnum::unknown());
        skip_state.clear_scalar_id(r);
    }
    skip_state.pc = pc + 1;

    // Successor B: enter the callback with a fresh frame. Bail with the
    // skip state only if we're already at the kernel's max call depth.
    if state.num_frames() >= 8 {
        return vec![skip_state];
    }

    // Decide whether cb iteration could run ≥ 2 times — drives the widen
    // decision on cb-Exit propagation. Mirrors kernel's
    // `widen_imprecise_scalars` only triggering when find_prev_entry
    // returns a previous iteration to compare against (verifier.c v6.15
    // L10903–10920).
    let cb_should_widen = match helper {
        constants::BPF_LOOP => {
            // nr_loops is caller's R1. If max ≤ 1, only one iter possible
            // (concrete merge). Else widen.
            let (_, hi) = state.domain.get_interval(Reg::R1);
            hi > 1
        }
        // bpf_for_each_map_elem / user_ringbuf_drain / find_vma: variable
        // count (depends on map size / ringbuf entries / vma matches).
        // The kernel's iteration logic walks ≥ 2 entries when the cb's
        // exit-state isn't iter-stable, so widen scalar effects across
        // iterations — matches the `unsafe_find_vma` reject pattern in
        // verifier_iterating_callbacks.c.
        constants::BPF_FOR_EACH_MAP_ELEM
        | constants::BPF_USER_RINGBUF_DRAIN
        | constants::BPF_FIND_VMA => true,
        _ => false,
    };

    // Pre-push: capture caller's ctx-arg register so we can install it
    // as the cb's ctx parameter after the frame push (which clears the
    // caller-side regs). For sync callbacks the kernel passes the
    // caller's ctx pointer to a specific cb arg register
    // (`set_loop_callback_state` etc., verifier.c v6.15 ~L10685+).
    // Without this, the cb body's first read of ctx hits "R2 !read_ok".
    // Build the full caller→cb propagation list. Each entry is
    // `(cb_dst, caller_src_type, caller_src_tnum, caller_src_bounds)`.
    // Mirrors kernel `set_*_callback_state` (verifier.c v6.15 ~L10685+).
    // Without typed propagation the cb body's first read of the arg
    // hits "R2/R3 !read_ok".
    let mut ctx_propagations: Vec<(Reg, RegType, Tnum, (i64, i64))> = Vec::new();
    let snap = |st: &State, r: Reg| (st.types.get(r), st.get_tnum(r), st.domain.get_interval(r));
    match helper {
        // bpf_loop(nr_loops, cb, ctx, flags) → cb(idx, ctx); R1=idx (scalar, set later), ctx → R2.
        constants::BPF_LOOP
        // bpf_user_ringbuf_drain(map, cb, ctx, flags) → cb(dynptr, ctx); R1=dynptr (left NotInit; few tests deref), ctx → R2.
        | constants::BPF_USER_RINGBUF_DRAIN => {
            let (ty, tn, b) = snap(&state, Reg::R3);
            ctx_propagations.push((Reg::R2, ty, tn, b));
        }
        // bpf_for_each_map_elem(map, cb, ctx, flags) → cb(map, key, val, ctx);
        // R1=caller's R1 (the map ptr); R2=PTR_TO_MAP_KEY, R3=PTR_TO_MAP_VALUE
        // (we don't track those distinctly — use a lax BTF-typed pointer that
        // permits generic loads, mirroring the timer-cb fallback); R4=ctx.
        constants::BPF_FOR_EACH_MAP_ELEM => {
            let (ty1, tn1, b1) = snap(&state, Reg::R1);
            ctx_propagations.push((Reg::R1, ty1, tn1, b1));
            let (ty3, tn3, b3) = snap(&state, Reg::R3);
            ctx_propagations.push((Reg::R4, ty3, tn3, b3));
        }
        // bpf_find_vma(task, addr, cb, ctx, flags) → cb(task, vma, ctx);
        // R1=caller's R1 (task), R2=PTR_TO_BTF_ID{vm_area_struct}, R3=ctx.
        constants::BPF_FIND_VMA => {
            let (ty1, tn1, b1) = snap(&state, Reg::R1);
            ctx_propagations.push((Reg::R1, ty1, tn1, b1));
            let (ty4, tn4, b4) = snap(&state, Reg::R4);
            ctx_propagations.push((Reg::R3, ty4, tn4, b4));
        }
        _ => {}
    }

    // Caller's ctx-arg base offset (relative to caller's R10). Captured
    // before the move into cb_state below; needed to translate cb-body
    // store offsets into caller-frame stack offsets for the widening
    // propagation set.
    let caller_ctx_base_off: Option<i64> = {
        let caller_ctx_reg = match helper {
            constants::BPF_LOOP
            | constants::BPF_USER_RINGBUF_DRAIN
            | constants::BPF_FOR_EACH_MAP_ELEM => Some(Reg::R3),
            constants::BPF_FIND_VMA => Some(Reg::R4),
            _ => None,
        };
        caller_ctx_reg.and_then(|r| state.domain.get_distance_fixed(r, Reg::R10))
    };

    let mut cb_state = state;
    let caller_level_idx = cb_state.current_frame_level();
    let caller_stack_snapshot =
        cb_state.frames.get(caller_level_idx).stack.clone();
    cb_state.push_callback_frame(pc + 1, helper);
    cb_state.frames.current_mut().set_cb_propagation(
        caller_stack_snapshot,
        caller_level_idx.index(),
        cb_should_widen,
    );
    // Pre-computed cb-body store offsets (relative to the cb's ctx-arg
    // pointer). Translate to caller-frame offsets by adding the
    // caller's ctx-arg base offset (distance from caller's R10), then
    // stash on the cb frame so cb_exit_propagate can invalidate them
    // on widening.
    if let (Some(offsets), Some(base)) = (
        env.cb_body_store_offsets.get(&cb_entry),
        caller_ctx_base_off,
    ) {
        let translated: Vec<i16> = offsets
            .iter()
            .filter_map(|&cb_off| {
                let total = base.checked_add(cb_off as i64)?;
                i16::try_from(total).ok()
            })
            .collect();
        cb_state
            .frames
            .current_mut()
            .set_cb_writeable_caller_offsets(translated);
    }
    update_call_rel_types(&mut cb_state);
    cb_state.domain.clear_packet_size_bounds();

    // Minimal arg typing: clear R1..R5, then re-install per-helper. R1
    // for bpf_loop is the iteration index (scalar). Other helpers' R1
    // and additional pointer args are installed via `ctx_propagations`
    // and the static-typed table below; remaining regs stay NotInit so
    // callbacks that dereference them REJECT.
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        cb_state.types.set(r, RegType::NotInit);
        cb_state.domain.forget(r);
        cb_state.set_tnum(r, Tnum::unknown());
        cb_state.clear_scalar_id(r);
    }
    // bpf_loop only: R1 = iteration index (scalar). Other helpers
    // install R1 via ctx_propagations.
    if helper == constants::BPF_LOOP {
        cb_state.types.set(Reg::R1, RegType::ScalarValue);
        cb_state.domain.forget(Reg::R1);
        cb_state.set_tnum(Reg::R1, Tnum::unknown());
        cb_state.alloc_scalar_id(Reg::R1);
    }

    // Install propagated args after the generic clear.
    for (dst, ty, tnum, (lo, hi)) in ctx_propagations.drain(..) {
        cb_state.types.set(dst, ty);
        cb_state.set_tnum(dst, tnum);
        cb_state.domain.forget(dst);
        cb_state.domain.assign_interval(dst, lo, hi);
        cb_state.clear_scalar_id(dst);
    }

    // Static-typed cb args (kernel `set_*_callback_state` PTR_TO_BTF_ID /
    // PTR_TO_MAP_KEY / PTR_TO_MAP_VALUE entries). We don't track
    // PTR_TO_MAP_KEY / VALUE distinctly — approximate with a lax
    // BTF-typed pointer that admits generic loads (existing timer-cb
    // pattern). Tighter typing is future work.
    {
        use crate::analysis::machine::reg_types::PtrFlags;
        let unknown_btf = || RegType::PtrToBtfId {
            type_name: "unknown",
            flags: PtrFlags::TRUSTED,
            ref_id: None,
        };
        match helper {
            // cb(map, key, val, ctx) — R2=key, R3=val (lax pointers).
            constants::BPF_FOR_EACH_MAP_ELEM => {
                for r in [Reg::R2, Reg::R3] {
                    cb_state.types.set(r, unknown_btf());
                    cb_state.domain.forget(r);
                    cb_state.set_tnum(r, Tnum::unknown());
                    cb_state.clear_scalar_id(r);
                }
            }
            // cb(task, vma, ctx) — R2 = PTR_TO_BTF_ID{vm_area_struct, TRUSTED}.
            constants::BPF_FIND_VMA => {
                cb_state.types.set(
                    Reg::R2,
                    RegType::PtrToBtfId {
                        type_name: "vm_area_struct",
                        flags: PtrFlags::TRUSTED,
                        ref_id: None,
                    },
                );
                cb_state.domain.forget(Reg::R2);
                cb_state.set_tnum(Reg::R2, Tnum::unknown());
                cb_state.clear_scalar_id(Reg::R2);
            }
            _ => {}
        }
    }

    // Timer cb signature is `(struct bpf_map *, void *key, void *value)`
    // — kernel `set_timer_callback_state` (verifier.c ~L10685, v6.15)
    // sets R1=CONST_PTR_TO_MAP, R2=PTR_TO_MAP_KEY, R3=PTR_TO_MAP_VALUE
    // off the timer's owning map. Without typed R2/R3 the cb body
    // hits "R2 !read_ok" on the very first `Mov R1=R2`.
    // Approximate with scalar pointers: the cb in
    // `verifier_private_stack.c::private_stack_async_callback_2`
    // immediately forwards `key` to a global subprog that
    // dereferences it as `int *`, so a generic readable scalar
    // suffices for that closure. Tighter typing (real PTR_TO_MAP_KEY
    // / VALUE) is future work — surfaced as the next FR if any test
    // does map-aware arithmetic in a timer cb.
    if helper == constants::BPF_TIMER_SET_CALLBACK {
        // R1=map ptr, R2=key ptr, R3=value ptr. We don't track
        // PTR_TO_MAP_KEY/VALUE distinctly, so approximate with a lax
        // BTF-typed pointer (type_name="unknown" gives the existing
        // "unknown-layout" load/store policy: any offset accepted,
        // loads produce ScalarValue). Concrete enough that subprogs
        // dereferencing the key (e.g. `subprog1(key) → *val`) verify;
        // loose enough that we don't claim more precision than the
        // kernel actually requires for these pointer args.
        use crate::analysis::machine::reg_types::PtrFlags;
        let unknown_btf = || RegType::PtrToBtfId {
            type_name: "unknown",
            flags: PtrFlags::TRUSTED,
            ref_id: None,
        };
        for r in [Reg::R1, Reg::R2, Reg::R3] {
            cb_state.types.set(r, unknown_btf());
            cb_state.domain.forget(r);
            cb_state.set_tnum(r, Tnum::unknown());
            cb_state.clear_scalar_id(r);
        }
    }

    cb_state.pc = cb_entry;

    vec![skip_state, cb_state]
}

fn allowed_while_in_active_lock(helper: u32) -> bool {
    match helper {
        constants::BPF_GET_PRANDOM_U32 => false,
        _ => true,
    }
}

/// Transfer function for relative Call (BPF-to-BPF function call) instructions.
pub(crate) fn transfer_call_rel(
    env: &mut VerifierEnv,
    mut state: State,
    target: usize,
) -> Vec<State> {
    let pc = state.pc;
    // Kernel: `state->curframe + 1 >= MAX_CALL_FRAMES (8)` rejects when
    // the *new* frame's index would reach the limit. Our 1-based
    // `num_frames()` counts the current depth. The kernel allows 8
    // frames total (main + 7 subprog frames); a chain like
    // `test_global_func4`'s `main → f7 → ... → f1` hits exactly 8
    // frames at f1. Use `> 8` so we reject only on the *9th* push.
    if state.num_frames() > 8 {
        env.fail(VerificationError::MaxCallDepthExceeded { pc });
        return vec![];
    }

    // Reject any direct (or transitively-resolved) call whose target
    // resolves to the registered exception callback. The kernel
    // disallows the program from invoking its own exception_cb directly:
    // unwinding is the only legal entry into it. Mirrors the kernel's
    // "cannot call exception cb directly" diagnostic.
    if let Some(cb_name) = env.ctx.exception_callback.as_deref()
        && let Some(target_name) = env.ctx.pc_to_subprog_name.get(&target)
        && target_name == cb_name
    {
        env.fail(VerificationError::ExceptionCallbackInvalid {
            reason: "cannot call exception cb directly".to_string(),
        });
        return vec![];
    }

    // W6.5: global subprogs are verified independently against their
    // declared BTF FUNC_PROTO. At each call site we must:
    //   1. Reject malformed global signatures (void return, FWD args)
    //      that the kernel would reject at function-load time.
    //   2. Validate caller's R1..R5 against declared types (catches
    //      "Caller passes invalid args into func#N").
    //   3. After push_frame, override callee's R1..R5 with declared
    //      types so the body is verified the way the kernel would —
    //      pointers come in as PTR_TO_MEM | PTR_MAYBE_NULL, etc.
    // Static subprogs skip all of this: callee inherits caller's
    // concrete types, matching kernel `__noinline static` semantics.
    let callee_global = env
        .ctx
        .pc_to_subprog_name
        .get(&target)
        .cloned()
        .filter(|n| env.ctx.btf.is_global_func(n));
    if let Some(name) = callee_global.as_ref() {
        // Kernel verifier.c L10538: global subprog calls are unconditionally
        // rejected while a bpf_spin_lock is held. Global subprogs are
        // verified separately and may execute helpers/kfuncs that are
        // disallowed under lock; static subprogs are inlined and exempt.
        if state.has_active_lock() {
            env.fail(VerificationError::GlobalFuncCallUnderLock {
                pc,
                func: name.clone(),
            });
            return vec![];
        }
        // Static call-graph gate: kernel rejects a global subprog whose
        // body transitively reaches a MIGHT_SLEEP helper/kfunc when the
        // call site is inside an irq- or preempt-disabled region. Path-
        // independent (closes irq_sleepable_*_subprog* and
        // preempt_global_sleepable_subprog_indirect FAs that escape the
        // per-call MIGHT_SLEEP gate when the dataflow-pruned path
        // dead-codes the inner sleepable call).
        if env.ctx.may_sleep_subprogs.contains(&target)
            && (state.in_irq_disabled() || state.in_preempt_disabled())
        {
            env.fail(VerificationError::GlobalFuncMaySleepInNonSleepable {
                pc,
                func: name.clone(),
            });
            return vec![];
        }
        if env.ctx.btf.func_returns_void(name) {
            env.fail(VerificationError::GlobalFuncMalformed {
                pc,
                func: name.clone(),
                reason: "doesn't return scalar".to_string(),
            });
            return vec![];
        }
        if let Some(args) = env.ctx.btf.resolve_global_func_args(name) {
            // Reject malformed args (FWD).
            for (i, arg) in args.iter().enumerate() {
                if let crate::parsing::btf::GlobalFuncArg::PtrToFwd { name: tname } = arg {
                    env.fail(VerificationError::GlobalFuncMalformed {
                        pc,
                        func: name.clone(),
                        reason: format!(
                            "reference type('FWD {}') size cannot be determined (arg #{})",
                            tname,
                            i + 1
                        ),
                    });
                    return vec![];
                }
            }
            // Caller-side type compatibility check.
            let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
            for (i, (arg, reg)) in args.iter().zip(arg_regs.iter()).enumerate() {
                let actual = state.types.get(*reg);
                // For scalars passed where a pointer is declared, the
                // kernel admits only literal NULL — not arbitrary
                // scalar values. Use the domain to prove the value is
                // exactly 0; otherwise reject.
                let scalar_is_zero = || {
                    let (lo, hi) = state.domain.get_interval(*reg);
                    lo == 0 && hi == 0
                };
                if !caller_arg_compatible(arg, actual, scalar_is_zero) {
                    env.fail(VerificationError::GlobalFuncBadCallerArg {
                        pc,
                        func: name.clone(),
                        arg_index: i,
                    });
                    return vec![];
                }
                // For PtrToStack passed to PtrToMem(mem_size), the
                // kernel additionally verifies the caller's stack
                // region is large enough and fully initialized. This
                // catches "small struct passed to large declared arg"
                // — the kernel emits "invalid read from stack" when
                // the callee would later access bytes past the
                // caller's allocation.
                if let crate::parsing::btf::GlobalFuncArg::PtrToMem { mem_size, .. } = arg
                    && let RegType::PtrToStack { .. } = actual
                    && let Some(off) = state.domain.get_distance_fixed(*reg, Reg::R10)
                {
                    crate::analysis::transfer::memory::check_stack_arg_readable(
                        env,
                        &state,
                        off,
                        *mem_size as i64,
                        pc,
                        crate::analysis::transfer::memory::access::AccessKind::HelperBuffer,
                    );
                    if env.failed() {
                        return vec![];
                    }
                }
                // Read-only map value (.rodata) passed to a writable
                // PtrToMem arg: the global subprog signature has no
                // `__arg_const` tag, so the callee may store through it.
                // Kernel reports "Caller passes invalid args into func#N".
                if let crate::parsing::btf::GlobalFuncArg::PtrToMem { .. } = arg
                    && let RegType::PtrToMapValue { map_idx, .. } = actual
                    && let Some(map_def) = env.ctx.map_defs.get(map_idx)
                    && map_def.map_flags & crate::common::constants::BPF_F_RDONLY_PROG != 0
                {
                    env.fail(VerificationError::GlobalFuncBadCallerArg {
                        pc,
                        func: name.clone(),
                        arg_index: i,
                    });
                    return vec![];
                }
                // "kptr cannot be accessed indirectly by helper" extends
                // to global subprog calls: a `PtrToMapValue` arg whose
                // declared mem region overlaps a kptr field is rejected.
                if let crate::parsing::btf::GlobalFuncArg::PtrToMem { mem_size, .. } = arg
                    && let RegType::PtrToMapValue {
                        offset: map_off,
                        map_idx,
                        ..
                    } = actual
                    && let Some(map_def) = env.ctx.map_defs.get(map_idx)
                {
                    crate::analysis::transfer::memory::check_kptr_field_access(
                        env,
                        &state,
                        map_def,
                        map_idx,
                        *reg,
                        map_off,
                        0,
                        *mem_size as i64,
                        pc,
                        /*is_store=*/ true,
                    );
                    if env.failed() {
                        return vec![];
                    }
                }
            }
        }
    }

    // Global-subprog calls get an isolated frame: kernel verifies them
    // separately, so RCU lock-state changes inside the body must NOT
    // propagate back to the caller. `push_global_subprog_frame` stamps
    // a snapshot of `rcu_read_depth` that `transfer_exit` restores on
    // Exit. Static (non-global) subprogs use the regular `push_frame`
    // since the kernel walks them inline (state changes propagate).
    if callee_global.is_some() {
        state.push_global_subprog_frame(pc + 1);
    } else {
        state.push_frame(pc + 1);
    }
    update_call_rel_types(&mut state);

    // Override callee R1..R5 with declared types for global subprogs.
    // Pointer args become PtrToAllocMemOrNull bounded by the pointee's
    // BTF size — the callee must null-check before dereferencing,
    // which is the surface for `invalid mem access 'mem_or_null'`
    // when the body unconditionally derefs.
    if let Some(name) = callee_global.as_ref()
        && let Some(args) = env.ctx.btf.resolve_global_func_args(name)
    {
        let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
        for (arg, reg) in args.iter().zip(arg_regs.iter()) {
            match arg {
                crate::parsing::btf::GlobalFuncArg::Scalar => {
                    state.types.set(*reg, RegType::ScalarValue);
                    state.domain.forget(*reg);
                }
                crate::parsing::btf::GlobalFuncArg::PtrToMem { mem_size, nonnull } => {
                    let id = crate::analysis::machine::reg_types::new_ptr_id();
                    let ty = if *nonnull {
                        RegType::PtrToAllocMem {
                            id,
                            mem_size: *mem_size as u64,
                            ref_id: None,
                            dynptr_id: None,
                        }
                    } else {
                        RegType::PtrToAllocMemOrNull {
                            id,
                            mem_size: *mem_size as u64,
                            ref_id: None,
                            dynptr_id: None,
                        }
                    };
                    state.types.set(*reg, ty);
                    state.domain.forget(*reg);
                }
                crate::parsing::btf::GlobalFuncArg::PtrToCtx => {
                    state.types.set(*reg, RegType::PtrToCtx);
                    state.domain.forget(*reg);
                }
                crate::parsing::btf::GlobalFuncArg::PermissivePtr => {
                    // Most `void *` global subprog args are ctx
                    // pointers in practice; pick PtrToCtx as the
                    // best guess for callee body verification.
                    state.types.set(*reg, RegType::PtrToCtx);
                    state.domain.forget(*reg);
                }
                crate::parsing::btf::GlobalFuncArg::PtrToFwd { .. } => {
                    // Already rejected above; keep arm exhaustive.
                }
                crate::parsing::btf::GlobalFuncArg::PtrToDynptr => {
                    // Preserve caller's stack pointer + dynptr-slot
                    // state so the callee's `bpf_dynptr_data` / `_slice`
                    // calls can resolve the slot. Kernel
                    // ARG_PTR_TO_DYNPTR | MEM_RDONLY (btf.c:7784) — no
                    // override.
                }
                crate::parsing::btf::GlobalFuncArg::PtrToBtfIdTrusted {
                    type_name,
                    nullable,
                } => {
                    use crate::analysis::machine::reg_types::PtrFlags;
                    // type_name is a runtime string; the RegType variant
                    // holds a `&'static str`, so leak the (small, bounded)
                    // name once. Subsequent calls reuse the leaked copy
                    // via the leak-safe identity check on the call site
                    // path — bounded by the number of distinct kernel
                    // types referenced as `__arg_trusted` in any one
                    // verified ELF.
                    let leaked: &'static str =
                        Box::leak(type_name.clone().into_boxed_str());
                    let flags = PtrFlags::TRUSTED;
                    let ty = if *nullable {
                        RegType::PtrToBtfIdOrNull {
                            id: 0,
                            type_name: leaked,
                            flags,
                            ref_id: None,
                        }
                    } else {
                        RegType::PtrToBtfId {
                            type_name: leaked,
                            flags,
                            ref_id: None,
                        }
                    };
                    state.types.set(*reg, ty);
                    state.domain.forget(*reg);
                }
            }
        }
    }

    // Clear packet size bounds for the callee.
    // The kernel verifier tracks bounds per-function, so each function
    // starts with no proven packet size. This is important for cases where
    // the caller did a bounds check but the callee spills a fresh packet
    // pointer before doing its own check.
    state.domain.clear_packet_size_bounds();

    state.pc = target;

    vec![state]
}

/// Caller-side compatibility for a global subprog arg (W6.5). The
/// kernel rejects calls whose actual reg type doesn't satisfy the
/// declared kind:
///   - declared Scalar: actual must be ScalarValue.
///   - declared PtrToMem: actual must be a memory-style pointer
///     (PtrToStack / PtrToMapValue / PtrToMem / PtrToAllocMem) OR
///     a scalar that's *provably zero* (literal NULL — the kernel
///     does not admit arbitrary scalars cast to a pointer).
fn caller_arg_compatible<F: Fn() -> bool>(
    declared: &crate::parsing::btf::GlobalFuncArg,
    actual: RegType,
    scalar_is_zero: F,
) -> bool {
    use crate::parsing::btf::GlobalFuncArg;
    match declared {
        GlobalFuncArg::Scalar => matches!(actual, RegType::ScalarValue),
        GlobalFuncArg::PtrToMem { .. } => match actual {
            RegType::PtrToStack { .. }
            | RegType::PtrToMapValue { .. }
            | RegType::PtrToMapValueOrNull { .. }
            | RegType::PtrToAllocMem { .. }
            | RegType::PtrToAllocMemOrNull { .. } => true,
            RegType::ScalarValue => scalar_is_zero(),
            _ => false,
        },
        GlobalFuncArg::PtrToCtx => matches!(actual, RegType::PtrToCtx),
        GlobalFuncArg::PtrToFwd { .. } => false,
        GlobalFuncArg::PtrToBtfIdTrusted {
            nullable,
            type_name,
        } => match actual {
            // `__arg_trusted` accepts any kernel BTF id pointer the
            // caller produced (acquired or static). `__arg_nullable`
            // additionally admits the OrNull variant and literal NULL.
            RegType::PtrToBtfId { .. } => true,
            RegType::PtrToBtfIdOrNull { .. } => *nullable,
            // Acquire-tracked specializations (PtrToTask, PtrToSocket,
            // …) are kernel BTF ids in disguise — accept them when the
            // declared type_name matches. CO-RE flavor suffix
            // (`task_struct___local`) just renames the same kernel
            // type, so strip the trailing `___…` before matching.
            RegType::PtrToTask { .. } | RegType::PtrToTaskOrNull { .. } => {
                let base = type_name
                    .split("___")
                    .next()
                    .unwrap_or(type_name.as_str());
                base == "task_struct"
                    && (matches!(actual, RegType::PtrToTask { .. }) || *nullable)
            }
            RegType::PtrToSocket { .. } | RegType::PtrToSocketOrNull { .. } => {
                let base = type_name
                    .split("___")
                    .next()
                    .unwrap_or(type_name.as_str());
                base == "sock"
                    && (matches!(actual, RegType::PtrToSocket { .. }) || *nullable)
            }
            RegType::PtrToCpumask { .. } | RegType::PtrToCpumaskOrNull { .. } => {
                let base = type_name
                    .split("___")
                    .next()
                    .unwrap_or(type_name.as_str());
                base == "bpf_cpumask"
                    && (matches!(actual, RegType::PtrToCpumask { .. }) || *nullable)
            }
            RegType::ScalarValue => *nullable && scalar_is_zero(),
            _ => false,
        },
        GlobalFuncArg::PtrToDynptr => matches!(actual, RegType::PtrToStack { .. }),
        GlobalFuncArg::PermissivePtr => match actual {
            RegType::PtrToCtx
            | RegType::PtrToStack { .. }
            | RegType::PtrToMapValue { .. }
            | RegType::PtrToMapValueOrNull { .. }
            | RegType::PtrToAllocMem { .. }
            | RegType::PtrToAllocMemOrNull { .. } => true,
            RegType::ScalarValue => scalar_is_zero(),
            _ => false,
        },
    }
}

/// Apply the W5.2 lock / RCU pre-call flags carried on `proto`.
/// Returns `false` (and calls `env.fail`) if the lock or RCU state
/// machine rejects this call. Arg-shape checks already ran in
/// `validate_helper_args`; here we only mutate `state.active_lock` /
/// `state.rcu_read_depth` and reject mismatched ordering.
pub(crate) fn apply_pre_call_lock_flags(
    env: &mut VerifierEnv,
    state: &mut State,
    helper: u32,
    proto: &super::signatures::CallProto,
) -> bool {
    use super::signatures::CallFlags;
    let pc = state.pc;

    // Helpers/kfuncs marked RCU require an active read-side section.
    if proto.flags.contains(CallFlags::RCU) && !state.in_rcu_read_section() {
        env.fail(VerificationError::NotInRcuReadSection { pc, helper });
        return false;
    }

    // W5.4: kfuncs marked SPIN_LOCK_HELD (rbtree / list mutation)
    // require any spin_lock to be active. Lite scope doesn't match the
    // lock to a specific map's lock — any held lock satisfies.
    if proto.flags.contains(CallFlags::SPIN_LOCK_HELD) && !state.has_active_lock() {
        env.fail(VerificationError::NotInSpinLockSection { pc, helper });
        return false;
    }

    if proto.flags.contains(CallFlags::SPIN_LOCK_ACQUIRE) {
        if state.has_active_lock() {
            env.fail(VerificationError::LockAlreadyHeld { pc });
            return false;
        }
        // R1 was validated by `validate_map_value_special` as either a
        // PtrToMapValue or a PtrToOwnedKptr aimed at a SpinLock field.
        // The kernel `process_spin_lock` (verifier.c v6.15 L8271+)
        // accepts both shapes; the lock-state-machine identity is
        // (id, offset) for map values and (ref_id, foo_offset) for
        // freshly-allocated objects (`bpf_obj_new`'d struct foo with
        // a `bpf_spin_lock` member). Without this arm, every linked
        // / rbtree test that takes `bpf_spin_lock(&f->lock)` rejects
        // the *_in_list family in linked_list.c).
        let (id, off) = match state.types.get(Reg::R1) {
            RegType::PtrToMapValue { offset: Some(o), id, .. } => (id, o as u32),
            RegType::PtrToOwnedKptr { ref_id, offset, .. } => (
                ref_id.unwrap_or(0),
                offset as u32,
            ),
            _ => {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
                return false;
            }
        };
        state.acquire_lock(id, off);
    }

    if proto.flags.contains(CallFlags::SPIN_LOCK_RELEASE) {
        let id = match state.types.get(Reg::R1) {
            RegType::PtrToMapValue { id, .. } => id,
            RegType::PtrToOwnedKptr { ref_id, .. } => ref_id.unwrap_or(0),
            _ => {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
                return false;
            }
        };
        let Some(lock) = state.get_active_lock() else {
            env.fail(VerificationError::LockNotHeld { pc });
            return false;
        };
        if lock.ptr_id != id {
            env.fail(VerificationError::LockNotHeld { pc });
            return false;
        }
        state.release_lock();
        // Kernel `verifier.c` v6.15 L8382: `process_spin_lock` calls
        // `invalidate_non_owning_refs` on unlock — non-owning refs
        // produced by `bpf_rbtree_add` / `bpf_list_push_*` under this
        // lock are only safe to dereference while the lock is held.
        state.invalidate_non_owning_refs();
    }

    if proto.flags.contains(CallFlags::RCU_READ_LOCK) {
        state.rcu_read_lock();
    }

    if proto.flags.contains(CallFlags::RCU_READ_UNLOCK) {
        if !state.rcu_read_unlock() {
            env.fail(VerificationError::RcuReadNotHeld { pc });
            return false;
        }
        // Kernel verifier.c v6.15 ~L13543: on rcu_read_unlock, every
        // MEM_RCU reg/slot is re-flagged PTR_UNTRUSTED. We mirror this
        // for iter slots only — the use-after-unlock pattern (lock /
        // iter_*_new / next / unlock / next or unlock / lock / next)
        // is what `iters_task_failure::iter_tasks_lock_and_unlock`
        // exercises. Other reg-type RCU promotions are out of scope.
        if !state.in_rcu_read_section() {
            state.invalidate_rcu_iter_slots();
        }
    }

    // Preempt-region (kernel verifier.c v6.15 ~L13560).
    //
    // MIGHT_SLEEP is checked BEFORE PREEMPT_DISABLE/ENABLE state changes:
    // a sleepable helper inside an existing disabled region rejects
    // regardless of whether this call would itself toggle the count.
    // (`bpf_preempt_disable` and `bpf_preempt_enable` themselves are not
    // marked MIGHT_SLEEP.)
    if proto.flags.contains(CallFlags::MIGHT_SLEEP) && state.in_preempt_disabled() {
        env.fail(VerificationError::SleepableInPreemptDisabled { pc, helper });
        return false;
    }
    // IRQ-disabled region also rejects sleepable calls (kernel
    // verifier.c v6.15 ~L13576).
    if proto.flags.contains(CallFlags::MIGHT_SLEEP) && state.in_irq_disabled() {
        env.fail(VerificationError::IrqState {
            pc,
            reason: "sleepable call inside bpf_local_irq_save-ed region".into(),
        });
        return false;
    }
    // Explicit-RCU-CS region rejects sleepable calls (kernel verifier.c
    // v6.15 L13549: "kernel func %s is sleepable within rcu_read_lock
    // region"). Gated on explicit `bpf_rcu_read_lock` only — the
    // implicit-RCU-at-entry baseline for non-sleepable tracing progs
    // (kprobe/tp/raw_tp/perf_event) is excluded so MIGHT_SLEEP calls
    // from those programs hit the (separate) "non-sleepable context"
    // gates instead.
    let explicit_rcu_baseline =
        if state.implicit_rcu_at_entry { 1 } else { 0 };
    if proto.flags.contains(CallFlags::MIGHT_SLEEP)
        && state.rcu_read_depth > explicit_rcu_baseline
    {
        env.fail(VerificationError::SleepableInRcuReadSection { pc, helper });
        return false;
    }

    // bpf_res_spin_unlock{,_irqrestore} (kernel `process_spin_lock`,
    // is_lock=false, verifier.c v6.15 L8358-8379). Validates LIFO match
    // on `acquired_res_locks`; emits the kernel rejection family
    // ("without taking a lock" / "different lock" / "out of order" /
    // wrong-class).
    if proto.flags.contains(CallFlags::RES_SPIN_LOCK_RELEASE) {
        let arg = state.types.get(Reg::R1);
        let (reg_id, ptr_id) = match arg {
            RegType::PtrToMapValue { id, map_idx, .. } => (id, map_idx as u32),
            RegType::PtrToOwnedKptr { ref_id, .. } => (ref_id.unwrap_or(0), 0u32),
            _ => {
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
                return false;
            }
        };
        // Distinguish the irqsave flavor from the plain one. We piggy-
        // back on the IRQ_RESTORE side-effect class — this kfunc has
        // `IrqRestoreFromArg { kfunc_class: Lock }` only when it's the
        // irqrestore variant; the plain `_unlock` doesn't.
        let is_irq = proto.side_effects.iter().any(|e| {
            matches!(
                e,
                super::signatures::SideEffect::IrqRestoreFromArg {
                    kfunc_class: crate::analysis::machine::stack_state::IrqKfuncClass::Lock,
                    ..
                }
            )
        });
        match state.res_lock_release(reg_id, ptr_id, is_irq) {
            Ok(()) => {}
            Err(crate::analysis::machine::state::ResLockReleaseError::Empty) => {
                env.fail(VerificationError::LockNotHeld { pc });
                return false;
            }
            Err(_) => {
                // NotInStack / OutOfOrder / WrongClass — single error
                // variant; specific kernel message string is lost but
                // the rejection (and per-test classification) matches.
                env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
                return false;
            }
        }
    }

    if proto.flags.contains(CallFlags::PREEMPT_DISABLE) {
        state.preempt_disable();
    }

    if proto.flags.contains(CallFlags::PREEMPT_ENABLE) && !state.preempt_enable() {
        env.fail(VerificationError::PreemptNotDisabled { pc });
        return false;
    }

    // IRQ_SAVE / IRQ_RESTORE: validator already checked the arg type;
    // the side-effect handler mutates the state. We only set up the
    // gate here for completeness symmetry — actual mutation is in
    // `apply_call_proto_r0`'s side-effect loop.
    // (No state changes here; gating belongs to the proto path's
    // arg validator + side-effect applier.)

    true
}

pub(crate) fn interval_set_scalar_id(domain: &mut NumericDomain, reg: Reg) {
    if let NumericDomain::Interval(ivl) = domain {
        ivl.get_bounds_mut(reg).scalar_id = Some(new_scalar_id());
    }
}

pub(crate) fn restore_interval_ptr_offset_from_return(
    domain: &mut NumericDomain,
    ret_type: &RegType,
    ret_interval_ptr_offset: (Option<i64>, Option<u64>, Option<i64>),
) {
    if let (Some(off), var_off_opt, range) = ret_interval_ptr_offset {
        use crate::domains::interval::PtrOffset;

        // Determine anchor from register type
        let anchor = match ret_type {
            RegType::PtrToPacket => Some(Reg::AnchorData),
            RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
            RegType::PtrToPacketEnd => Some(Reg::AnchorDataEnd),
            _ => None,
        };

        if let Some(anchor) = anchor {
            if let NumericDomain::Interval(ivl) = domain {
                let var_off = var_off_opt.unwrap_or(0);
                let ptr_offset = PtrOffset {
                    anchor,
                    off,
                    var_off,
                    range,
                    // id not currently round-tripped across subprog
                    // returns; conservative None loses id-aware
                    // refinement at the boundary but is sound.
                    id: None,
                };
                ivl.get_mut(Reg::R0).ptr_offset = Some(ptr_offset);
            }
        }
    }
}

pub(crate) fn restore_callee_interval_packet_info(
    domain: &mut NumericDomain,
    caller_types: &crate::analysis::machine::reg_types::TypeState,
    callee_saved_packet_info: Vec<(Reg, RegType, (Option<i64>, Option<u64>, Option<i64>))>,
) {
    for (reg, callee_type, (off_opt, var_off_opt, range)) in callee_saved_packet_info {
        if let (Some(off), Some(range_val)) = (off_opt, range) {
            let anchor = match callee_type {
                RegType::PtrToPacket => Some(Reg::AnchorData),
                RegType::PtrToPacketMeta => Some(Reg::AnchorDataMeta),
                _ => None,
            };

            if let Some(anchor) = anchor {
                if matches!(
                    caller_types.get(reg),
                    RegType::PtrToPacket | RegType::PtrToPacketMeta
                ) {
                    if let NumericDomain::Interval(ivl) = domain {
                        if let Some(caller_ptr_off) = ivl.get_ptr_offset(reg) {
                            if caller_ptr_off.anchor == anchor
                                && caller_ptr_off.off == off
                                && caller_ptr_off.var_off == var_off_opt.unwrap_or(0)
                            {
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
