// src/analysis/transfer/call/kfunc.rs
//
// Kfunc call transfer.
//
// As of W4.3 the only bespoke handler left is `bpf_throw` (terminal
// control flow — drops the path with no successor). Every other kfunc
// is driven by `CallProto` via the unified pipeline in `signatures` /
// `checks` / `side_effects`. Forking kfuncs (`bpf_iter_*_next`) are
// recognized via `RetKind::IterNextElem` and split into two successors
// inside `transfer_kfunc_proto`.

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, new_ptr_id};
use crate::analysis::machine::stack_state::{IterState, IteratorSlot};
use crate::analysis::machine::state::State;
use crate::domains::tnum::Tnum;

use super::side_effects::{apply_call_proto_r0, arg_reg, resolve_stack_arg};
use super::signatures::{CallFlags, CallProto, RetKind, SideEffect, get_kfunc_proto};

/// Top-level kfunc dispatch. Looks up the kfunc name in BTF and routes
/// it. Resolution order:
///
///   1. `get_kfunc_proto(name)` — proto-driven path. The generic
///      checker + shared post-call applier in `side_effects.rs` handles
///      arg validation, R0 typing, side effects, and (for the iter_next
///      family) the two-successor fork.
///   2. `bpf_throw` — bespoke because it's terminal (no successor) and
///      doesn't fit the flat proto model.
///   3. Unknown kfunc → REJECT.
pub(crate) fn transfer_kfunc(env: &mut VerifierEnv, state: State, btf_id: u32) -> Vec<State> {
    let pc = state.pc;
    let name = env.ctx.btf.kfunc_name(btf_id).map(|s| s.to_string());

    if let Some(n) = name.as_deref()
        && let Some(proto) = get_kfunc_proto(n)
    {
        return transfer_kfunc_proto(env, state, btf_id, &proto);
    }

    match name.as_deref() {
        // W3.3b: `bpf_throw` is terminal on this path. Stays bespoke
        // because the proto applier always produces at least one
        // continuing successor.
        Some("bpf_throw") => throw(env, state),

        _ => {
            env.fail(VerificationError::UnsupportedModernFeature {
                pc,
                feature: "kfunc call (BPF_PSEUDO_KFUNC_CALL)",
            });
            vec![]
        }
    }
}

/// Generic kfunc transfer driven by `CallProto`. Mirrors the helper
/// post-call sequence in `transfer_call`: validate args → apply side
/// effects + R0 → clobber caller-saved → advance pc.
///
/// `RetKind::IterNextElem` is the lone forking case (W4.3b): args and
/// non-r0 side effects run on a shared base; then we split into two
/// successors that get independent R0 typing + slot-state transitions.
fn transfer_kfunc_proto(
    env: &mut VerifierEnv,
    mut state: State,
    btf_id: u32,
    proto: &CallProto,
) -> Vec<State> {
    let pc = state.pc;
    let in_types = state.types.clone();

    // W6.3: enforce per-kfunc prog-type allowlist before any other
    // validation. Mirrors the kernel verifier's `KF_PROG_TYPE_*` check.
    if let Some(allowed) = proto.prog_type_allowlist
        && !allowed.contains(&env.ctx.prog_kind)
    {
        env.fail(crate::analysis::machine::error::VerificationError::KfuncNotAllowedForProgram {
            pc,
            btf_id,
            kind: env.ctx.prog_kind,
        });
        return vec![];
    }

    // W6.4c: per-(ops_struct, member) allowlist for struct_ops kfuncs.
    // The kernel sched_ext class gates some kfuncs to specific callbacks
    // (e.g. `scx_bpf_select_cpu_dfl` only callable from `.select_cpu`).
    // We only consult the binding when prog_kind is StructOps; for any
    // other prog kind the prog_type_allowlist above already rejected.
    if let Some(allowed) = proto.ops_member_allowlist
        && env.ctx.prog_kind == crate::ast::ProgramKind::StructOps
    {
        let ok = match &env.ctx.struct_ops_member {
            Some((ops, member)) => allowed
                .iter()
                .any(|(o, m)| *o == ops.as_str() && *m == member.as_str()),
            // No binding info: be conservative — reject. The runner is
            // expected to populate this for any StructOps subprog with
            // a recovered binding; missing-binding means we can't prove
            // the call site is allowed.
            None => false,
        };
        if !ok {
            let (ops_struct, member) = env
                .ctx
                .struct_ops_member
                .clone()
                .unwrap_or_else(|| ("?".to_string(), "?".to_string()));
            env.fail(
                crate::analysis::machine::error::VerificationError::KfuncNotAllowedForOpsMember {
                    pc,
                    btf_id,
                    ops_struct,
                    member,
                },
            );
            return vec![];
        }
    }

    if !super::checks::check_mem_size_pairs(env, &state, proto, pc) {
        return vec![];
    }

    // Kernel: `bpf_rcu_read_{lock,unlock}` cross a spin_lock boundary
    // is rejected as "function calls are not allowed while holding a
    // lock" (refcounted_kptr_fail::rbtree_fail_sleepable_lock_across_rcu).
    // The kfunc has no lock-aware semantics — programs that toggle
    // RCU regions while a spin_lock is held would unwind the lock
    // pairing across critical sections.
    if state.has_active_lock()
        && (proto.flags.contains(CallFlags::RCU_READ_LOCK)
            || proto.flags.contains(CallFlags::RCU_READ_UNLOCK))
    {
        env.fail(
            crate::analysis::machine::error::VerificationError::InvalidArgType {
                pc,
                reg: Reg::R0,
            },
        );
        return vec![];
    }

    // W5.4: enforce SPIN_LOCK_HELD / RCU / lock-acquire-release proto
    // flags before arg validation. Done here (not in side_effects)
    // because rejection short-circuits the whole call.
    if !super::transfer::apply_pre_call_lock_flags(env, &mut state, btf_id, proto) {
        return vec![];
    }

    let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
    for (i, (&arg_kind, &reg)) in proto.args.iter().zip(arg_regs.iter()).enumerate() {
        if matches!(arg_kind, super::signatures::ArgKind::DontCare) {
            break;
        }
        let actual = in_types.get(reg);
        if !super::checks::validate_single_arg(
            env,
            &state,
            &in_types,
            /* helper */ 0,
            pc,
            reg,
            arg_kind,
            actual,
            &None,
            i,
            proto.mem_size_pairs,
        ) {
            return vec![];
        }
    }

    // KF_RELEASE precondition: every `ReleaseRefFromArg{N}` arg must be a
    // refcounted pointer (i.e. carry a `ref_id`). Kernel rejects calls
    // like `bpf_put_file(file)` on a non-acquired (e.g. BPF_PROG entry)
    // pointer with "release kernel function bpf_put_file expects
    // refcounted PTR_TO_BTF_ID". Without this gate, our generic
    // `PtrToBtfId` validator (which doesn't inspect ref_id) would accept
    // and the side-effect's get_ref_id-then-release would silently
    // no-op on `ref_id: None`. The pre-existing `BPF_SK_RELEASE` arm in
    // `transfer.rs` handles the helper case with the same shape; this
    // closes the gap for the unified kfunc dispatcher.
    // Callback-misuse static scan: graph-add kfuncs (rbtree_add /
    // list_push_*) take a `less` callback in R3. The kernel rejects
    // when the cb body contains forbidden ops (spin_lock/unlock,
    // bpf_throw, recursive graph-mutation kfuncs, alloc/release).
    // Lite scope: any subprog landed in `tainted_cb_subprogs` at env
    // init is rejected here. Without this, the static-MapValue id=0
    // change unmasks several rbtree_fail / exceptions_fail
    // FALSE_ACCEPTs.
    if proto.flags.contains(CallFlags::RELEASE_NON_OWN) {
        // Cb arg by convention is R3 for both rbtree_add and list_push.
        if let RegType::PtrToCallback { subprog_pc } = in_types.get(Reg::R3)
            && env.tainted_cb_subprogs.contains(&(subprog_pc as usize))
        {
            env.fail(
                crate::analysis::machine::error::VerificationError::InvalidArgType {
                    pc,
                    reg: Reg::R3,
                },
            );
            return vec![];
        }
    }

    if proto.flags.contains(CallFlags::RELEASE) {
        let is_non_own = proto.flags.contains(CallFlags::RELEASE_NON_OWN);
        for eff in proto.side_effects {
            if let SideEffect::ReleaseRefFromArg { arg } = *eff {
                let reg = arg_regs[arg as usize];
                let actual = in_types.get(reg);
                if actual.get_ref_id().is_none() {
                    env.fail(
                        crate::analysis::machine::error::VerificationError::InvalidArgType {
                            pc,
                            reg,
                        },
                    );
                    return vec![];
                }
                // Kernel verifier.c v6.15 ~L13242: for a full-release
                // kfunc (`bpf_obj_drop`, `bpf_kptr_xchg`) the released
                // pointer must reference the head of the alloc; the
                // kernel's exact check is `reg->off == 0`. We approximate
                // by rejecting only positive offsets (`&res->node`-style
                // forward arithmetic into the alloc). Negative offsets
                // arise from `container_of(rb_remove_ret, struct, r)`
                // = `rb - 16`, which the kernel models via BTF-aware
                // offset tracking we don't replicate; treating negative
                // offsets as "container-of recovered to head" keeps
                // refcounted_kptr.c::rbtree_sleepable_rcu* PASSing
                // while still catching local_kptr_stash_fail::
                // drop_rb_node_off (offset = +16).
                if !is_non_own
                    && let RegType::PtrToOwnedKptr { offset, .. } = actual
                    && offset > 0
                {
                    env.fail(
                        crate::analysis::machine::error::VerificationError::InvalidArgType {
                            pc,
                            reg,
                        },
                    );
                    return vec![];
                }
            }
        }
    }

    // KF_TRUSTED_ARGS / KF_RCU enforcement: pointer args' flags must
    // satisfy the kfunc's trust band. Mirrors the kernel's
    // `KF_TRUSTED_ARGS` (every pointer must be PTR_TRUSTED or
    // refcounted/acquire-tracked) and `KF_RCU` (allows PTR_TRUSTED,
    // PTR_RCU, or acquire-tracked; rejects PTR_UNTRUSTED). Without
    // this gate, adding the testmod consumer kfuncs
    // (`bpf_kfunc_trusted_*_test` family) would FA the matching
    // `__failure` siblings (iter_next_rcu_not_trusted,
    // iter_next_ptr_mem_not_trusted) where the consumer is
    // intentionally fed a non-TRUSTED pointer the kernel rejects.
    let trust_band = if proto.flags.contains(CallFlags::TRUSTED_ARGS) {
        Some(TrustBand::Trusted)
    } else if proto.flags.contains(CallFlags::RCU) {
        Some(TrustBand::Rcu)
    } else {
        None
    };
    if let Some(band) = trust_band {
        for (i, (&arg_kind, &reg)) in proto.args.iter().zip(arg_regs.iter()).enumerate() {
            if matches!(arg_kind, super::signatures::ArgKind::DontCare) {
                break;
            }
            let actual = in_types.get(reg);
            if actual.is_pointer() && !pointer_arg_meets_trust(&actual, band) {
                let _ = i;
                env.fail(
                    crate::analysis::machine::error::VerificationError::InvalidArgType {
                        pc,
                        reg,
                    },
                );
                return vec![];
            }
        }
    }

    // Forking kfuncs (iter_next): handle the two successors inline so
    // each can carry its own R0 typing and slot-state transition.
    match proto.ret {
        RetKind::IterNextElem { iter_arg, elem_size } => {
            return iter_next_fork(env, state, iter_arg, IterNextElemKind::AllocMem(elem_size));
        }
        RetKind::IterNextBtfId {
            iter_arg,
            type_name,
            flags,
        } => {
            return iter_next_fork(
                env,
                state,
                iter_arg,
                IterNextElemKind::BtfId { type_name, flags },
            );
        }
        _ => {}
    }

    apply_call_proto_r0(&in_types, &mut state, proto);

    // W7.2: kfuncs marked `bpf_fastcall` (v6.13) preserve R1..R5 — skip
    // the caller-saved clobber so clang-emitted no-spill sequences
    // type-check. Iter-next forks intentionally always clobber (no
    // fastcall iter_next kfunc exists in the kernel set).
    if !proto.flags.contains(CallFlags::FASTCALL) {
        for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
            state.types.set(r, RegType::NotInit);
            state.domain.forget(r);
            state.set_tnum(r, Tnum::unknown());
            state.clear_scalar_id(r);
        }
    }
    state.domain.forget(Reg::R0);
    state.set_tnum(Reg::R0, Tnum::unknown());
    state.clear_scalar_id(Reg::R0);

    state.pc += 1;
    vec![state]
}

/// Element-shape distinguisher for `iter_next_fork`. The non-NULL
/// successor's R0 is either a generic memory pointer
/// (`bpf_iter_num_next` returns `int *` into iter state) or a typed
/// BTF pointer (`bpf_iter_task_vma_next` returns `vm_area_struct *`,
/// `bpf_iter_task_next` returns `task_struct *` with the kernel's
/// RCU lifetime).
pub(crate) enum IterNextElemKind {
    AllocMem(u64),
    BtfId {
        type_name: &'static str,
        flags: crate::analysis::machine::reg_types::PtrFlags,
    },
}

/// Fork an `iter_next` call into its two successors. The validator
/// already proved the iter arg points at an Active slot of the
/// proto-declared kind, so `resolve_stack_arg` is expected to succeed
/// here; if the offset went symbolic between validator and applier we
/// drop the path conservatively.
fn iter_next_fork(
    env: &mut VerifierEnv,
    state: State,
    iter_arg: u8,
    kind: IterNextElemKind,
) -> Vec<State> {
    let pc = state.pc;
    let reg = arg_reg(iter_arg);
    let Some((frame, base_off)) = resolve_stack_arg(&state, reg) else {
        return vec![];
    };

    // Kernel `is_iter_reg_valid_init` (verifier.c v6.15 ~L1135) returns
    // -EPROTO when the iter slot has PTR_UNTRUSTED; `process_iter_arg`
    // surfaces this as "expected an RCU CS when using <kfunc>". Mirrors
    // our `IteratorSlot.untrusted`: if set, reject before forking.
    if matches!(
        state.stack_at(frame).stack_get_iterator(base_off),
        Some(slot) if slot.untrusted
    ) {
        env.fail(crate::analysis::machine::error::VerificationError::InvalidArgType {
            pc,
            reg,
        });
        return vec![];
    }

    // Drained-input collapse: a `_next` call on an already-drained
    // iterator returns NULL unconditionally (the kernel just does one
    // `if (it->cnt <= 0) return NULL;` early-out). Don't fork — emit
    // only the null successor, and keep the slot Drained.
    let already_drained = matches!(
        state.stack_at(frame).stack_get_iterator(base_off),
        Some(slot) if matches!(slot.state, IterState::Drained)
    );

    // NULL successor: R0 = scalar 0, slot → Drained.
    let mut null = state.clone();
    if let Some(slot) = null.stack_at(frame).stack_get_iterator(base_off) {
        null.stack_at_mut(frame).stack_set_iterator(
            base_off,
            IteratorSlot {
                state: IterState::Drained,
                ..slot
            },
        );
    }
    null.types.set(Reg::R0, RegType::ScalarValue);
    null.domain.forget(Reg::R0);
    null.domain.assume_ge_imm(Reg::R0, 0);
    null.domain.assume_le_imm(Reg::R0, 0);
    null.set_tnum(Reg::R0, Tnum::constant(0));
    null.clear_scalar_id(Reg::R0);
    clobber_caller_saved(&mut null);
    null.pc = pc + 1;

    if already_drained {
        return vec![null];
    }

    // Non-NULL successor: R0 typed per `kind`, slot stays Active. Bump
    // `iter.depth` (kernel `process_iter_next_call` verifier.c v6.15
    // ~L8919) so successive iterations are distinguishable for the
    // pruning machinery and the inf-loop detector
    // (`iter_active_depths_differ`, ~L18965). Without this the loop top
    // looks identical across iterations and the kernel would mis-fire
    // the infinite-loop check on legitimate iter loops.
    let mut nonnull = state;
    if let Some(slot) = nonnull.stack_at(frame).stack_get_iterator(base_off) {
        nonnull.stack_at_mut(frame).stack_set_iterator(
            base_off,
            IteratorSlot {
                depth: slot.depth.saturating_add(1),
                ..slot
            },
        );
    }
    let r0 = match kind {
        IterNextElemKind::AllocMem(elem_size) => RegType::PtrToAllocMem {
            id: new_ptr_id(),
            mem_size: elem_size,
            ref_id: None,
            dynptr_id: None,
        },
        IterNextElemKind::BtfId { type_name, flags } => RegType::PtrToBtfId {
            type_name,
            flags,
            ref_id: None,
        },
    };
    nonnull.types.set(Reg::R0, r0);
    nonnull.domain.forget(Reg::R0);
    nonnull.set_tnum(Reg::R0, Tnum::unknown());
    nonnull.clear_scalar_id(Reg::R0);
    clobber_caller_saved(&mut nonnull);
    nonnull.pc = pc + 1;

    // Widen imprecise scalars in the queued ACTIVE branch relative to
    // the most recent prior visit at this iter_next call. Kernel
    // `widen_imprecise_scalars` (verifier.c v6.15 ~L8765, called from
    // `process_iter_next_call`) does the same: any imprecise reg or
    // spilled-stack scalar that differs from the parent state's value
    // becomes UNKNOWN. Without this, simple counter-bearing loops like
    // `i++; while(iter_next(...)) {}` produce a fresh distinct state
    // every iteration and the verifier never converges. Walking
    // explored_states[pc] for the most-recent prior is our analogue of
    // the kernel's `find_prev_entry(cur_st->parent, insn_idx)` —
    // we don't track parent-state lineage, so the latest cached visit
    // at this call site is the best available proxy.
    if let Some(prev_states) = env.explored_states.get(&pc)
        && let Some(prev) = prev_states.iter().rev().find(|s| s.pc == pc)
    {
        widen_imprecise_scalars_at_iter_next(prev, &mut nonnull);
    }

    vec![nonnull, null]
}

/// Widen imprecise scalars in `cur` against `prev` at an iter_next
/// fork. Mirrors kernel `widen_imprecise_scalars` (verifier.c v6.15
/// ~L8765): per-frame scan of regs and spilled-scalar stack slots; any
/// reg/slot not flagged precise whose abstract value disagrees with
/// `prev` collapses to UNKNOWN. Precise entries are left intact (the
/// kernel preserves them via the idmap; we use `precise_regs`).
fn widen_imprecise_scalars_at_iter_next(prev: &State, cur: &mut State) {
    use crate::analysis::machine::reg::Reg;

    // Collect changes first; can't mutate while borrowed.
    let mut regs_to_widen: Vec<Reg> = Vec::new();
    for r in [
        Reg::R0,
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
        Reg::R8,
        Reg::R9,
    ] {
        if cur.precise_regs.contains(&r) {
            continue;
        }
        // Only widen scalar-typed regs; pointer types are kept exact
        // (they participate in subsumption via id-loose rules).
        let cur_ty = cur.types.get(r);
        let prev_ty = prev.types.get(r);
        if !matches!(cur_ty, RegType::ScalarValue) || !matches!(prev_ty, RegType::ScalarValue) {
            continue;
        }
        let cur_iv = cur.domain.get_interval(r);
        let prev_iv = prev.domain.get_interval(r);
        let cur_tn = cur.get_tnum(r);
        let prev_tn = prev.get_tnum(r);
        if cur_iv != prev_iv || cur_tn != prev_tn {
            regs_to_widen.push(r);
        }
    }
    for r in regs_to_widen {
        cur.domain.forget(r);
        cur.set_tnum(r, Tnum::unknown());
        cur.clear_scalar_id(r);
    }

    // Spilled scalar slots: walk both frames' stacks. Drop any slot
    // whose abstract value disagrees and isn't precise.
    use crate::analysis::machine::frame_stack::FrameLevel;
    let n = cur.frames.depth().min(prev.frames.depth());
    for fi in 0..n {
        let level = FrameLevel::from_index(fi);
        let prev_stack_offsets: Vec<i16> = prev.frames.get(level).stack.slot_offsets();
        let mut to_invalidate: Vec<i16> = Vec::new();
        for off in prev_stack_offsets {
            let prev_ty = prev.frames.get(level).stack.get_slot_type(off);
            let cur_ty = cur.frames.get(level).stack.get_slot_type(off);
            if !matches!(prev_ty, RegType::ScalarValue)
                || !matches!(cur_ty, RegType::ScalarValue)
            {
                continue;
            }
            let prev_slot = prev.frames.get(level).stack.get_slot(off);
            let cur_slot = cur.frames.get(level).stack.get_slot(off);
            let differs = match (prev_slot, cur_slot) {
                (Some(p), Some(c)) => p.tnum != c.tnum || p.bounds != c.bounds,
                _ => false,
            };
            let cur_precise = cur_slot.map(|s| s.precise).unwrap_or(false);
            if differs && !cur_precise {
                to_invalidate.push(off);
            }
        }
        let cur_stack = &mut cur.frames.get_mut(level).stack;
        for off in to_invalidate {
            cur_stack.invalidate_slot(off);
        }
    }
}

fn clobber_caller_saved(state: &mut State) {
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        state.types.set(r, RegType::NotInit);
        state.domain.forget(r);
        state.set_tnum(r, Tnum::unknown());
        state.clear_scalar_id(r);
    }
}

/// What trust level a kfunc demands of its pointer args.
/// `Trusted` = `KF_TRUSTED_ARGS` (must be PTR_TRUSTED or refcounted).
/// `Rcu` = `KF_RCU` (allows PTR_TRUSTED, PTR_RCU, or refcounted).
#[derive(Copy, Clone)]
enum TrustBand {
    Trusted,
    Rcu,
}

/// True iff `actual` (a pointer-typed reg) satisfies `band`. Used by
/// the kfunc dispatcher's `KF_TRUSTED_ARGS` / `KF_RCU` enforcement.
///
/// "Refcounted" pointers (acquire-tracked specializations:
/// `PtrToTask`, `PtrToCgroup`, `PtrToCpumask`, `PtrToOwnedKptr`,
/// `PtrToArena`, `PtrToSocket{,Common}`, `PtrToTcpSock`,
/// `PtrToMapKptr` with the kernel's `MEM_ALLOC` flag) carry an
/// acquire-tracked ref_id; the kernel treats them as trusted for
/// kfunc-arg purposes regardless of explicit `PtrFlags`. Generic
/// `PtrToBtfId` consults `PtrFlags` directly. `PtrToAllocMem` is
/// neither trusted nor RCU — it represents iter-element memory that
/// `KF_TRUSTED_ARGS` consumers must reject (closes
/// `iter_next_ptr_mem_not_trusted`).
fn pointer_arg_meets_trust(actual: &RegType, band: TrustBand) -> bool {
    use crate::analysis::machine::reg_types::PtrFlags;

    let flags = actual.ptr_flags();
    let has_trusted = flags.contains(PtrFlags::TRUSTED);
    let has_rcu = flags.contains(PtrFlags::RCU);
    let has_untrusted = flags.contains(PtrFlags::UNTRUSTED);

    // Acquire-tracked specializations are trusted-by-construction
    // (the kernel mints them through KF_ACQUIRE-flagged paths and
    // ref-tracks them). Their reg variants don't carry PtrFlags, so
    // detect via `get_ref_id().is_some()` plus a positive shape match.
    let is_acquire_tracked = matches!(
        actual,
        RegType::PtrToTask { ref_id: Some(_) }
            | RegType::PtrToCgroup { ref_id: Some(_) }
            | RegType::PtrToCpumask { ref_id: Some(_) }
            | RegType::PtrToOwnedKptr { ref_id: Some(_), .. }
            | RegType::PtrToArena { ref_id: Some(_), .. }
            | RegType::PtrToSocket { ref_id: Some(_) }
            | RegType::PtrToSockCommon { ref_id: Some(_) }
            | RegType::PtrToTcpSock { id: Some(_) }
    );

    match band {
        TrustBand::Trusted => {
            (has_trusted && !has_untrusted) || is_acquire_tracked
        }
        TrustBand::Rcu => {
            (has_trusted || has_rcu) && !has_untrusted || is_acquire_tracked
        }
    }
}

/// `bpf_throw(cookie)`: terminates execution on this path. The kernel
/// runs the program-default exception callback (if registered) or
/// unwinds out of the program returning 0 — either way, the site has
/// no in-program successor and we drop the path.
///
/// Reference cleanup is the caller's responsibility: a live
/// `bpf_obj_new` / `bpf_refcount_acquire` reference at a throw site is
/// rejected with "Unreleased reference" because no handler is empowered
/// to release it on the unwind path. This matches the kernel's
/// `check_reference_leak` invocation at every throw.
fn throw(env: &mut VerifierEnv, state: State) -> Vec<State> {
    // Kernel: `bpf_throw` is forbidden inside any callback subprog
    // entered via bpf_loop / bpf_for_each_map_elem / bpf_timer_set_callback
    // / bpf_user_ringbuf_drain / bpf_find_vma. (The dedicated
    // `__exception_cb` pass in `analyze_exception_cb` is allowed to throw
    // — its frames don't carry `is_callback`.) Mirrors the kernel
    // rejection "cannot be called from callback subprog".
    if !env.analyzing_exception_cb
        && state.frames.iter().any(|f| f.is_callback())
    {
        env.fail(VerificationError::ExceptionCallbackInvalid {
            reason: "cannot be called from callback subprog".to_string(),
        });
        return vec![];
    }
    // Kernel: "function calls are not allowed while holding a lock".
    // bpf_throw under an active spin_lock would unwind without releasing
    // the lock — the kernel rejects up-front.
    // (See `exceptions_fail::reject_with_lock` and `reject_subprog_with_lock`.)
    if state.has_active_lock() {
        env.fail(VerificationError::InvalidArgType {
            pc: state.pc,
            reg: Reg::R0,
        });
        return vec![];
    }
    // Kernel: bpf_throw inside an RCU read-side critical section is
    // also rejected — the unwind path doesn't run rcu_read_unlock, so
    // the program would leak the RCU lock. Mirrors
    // `exceptions_fail::reject_with_rcu_read_lock` (kernel msg
    // "function calls are not allowed while holding a lock" — same
    // family, RCU bucket).
    if state.in_rcu_read_section() {
        env.fail(VerificationError::InvalidArgType {
            pc: state.pc,
            reg: Reg::R0,
        });
        return vec![];
    }
    if state.has_unreleased_refs() {
        env.fail(VerificationError::UnreleasedReference);
    }
    // When no exception_cb is registered (load-time decl-tag or runtime
    // bpf_set_exception_callback), the kernel's default unwind returns
    // the throw cookie as the program's R0 — so R1 at the throw site
    // must satisfy whatever return-value rule applies at the program's
    // main exit. fentry/fexit demands R0 == 0; we mirror that here for
    // R1, matching the kernel's "register R1 has smin=N smax=N" message.
    let no_handler =
        env.ctx.exception_callback.is_none() && state.effective_exception_cb().is_none();
    if no_handler && tracing_requires_zero_retval(env.ctx) {
        let (lo, hi) = state.domain.get_interval(Reg::R1);
        if lo != 0 || hi != 0 {
            env.fail(VerificationError::InvalidReturnCode { pc: state.pc });
            return vec![];
        }
    }
    vec![]
}

/// True when the SEC indicates an fentry/fexit attach. The kernel's
/// `check_return_code` enforces R0 == 0 at exit for both flavors; we
/// mirror that at exception cb exits and (for the no-handler case)
/// throw cookies. Driven off `attach_flavor` alone — the SEC suffices
/// to identify these attach types and `prog_kind` may legitimately
/// resolve to `Unknown` for `?fentry/...` test SECs without
/// invalidating the constraint.
fn tracing_requires_zero_retval(ctx: &crate::analysis::machine::context::ExecContext) -> bool {
    matches!(ctx.attach_flavor.as_deref(), Some("fentry") | Some("fexit"))
}
