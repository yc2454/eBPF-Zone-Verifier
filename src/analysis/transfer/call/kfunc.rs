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
    if proto.flags.contains(CallFlags::RELEASE) {
        for eff in proto.side_effects {
            if let SideEffect::ReleaseRefFromArg { arg } = *eff {
                let reg = arg_regs[arg as usize];
                if in_types.get(reg).get_ref_id().is_none() {
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

    // Forking kfuncs (iter_next): handle the two successors inline so
    // each can carry its own R0 typing and slot-state transition.
    if let RetKind::IterNextElem { iter_arg, elem_size } = proto.ret {
        return iter_next_fork(state, iter_arg, elem_size);
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

/// Fork an `iter_next` call into its two successors. The validator
/// already proved the iter arg points at an Active slot of the
/// proto-declared kind, so `resolve_stack_arg` is expected to succeed
/// here; if the offset went symbolic between validator and applier we
/// drop the path conservatively.
fn iter_next_fork(state: State, iter_arg: u8, elem_size: u64) -> Vec<State> {
    let pc = state.pc;
    let reg = arg_reg(iter_arg);
    let Some((frame, base_off)) = resolve_stack_arg(&state, reg) else {
        return vec![];
    };

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

    // Non-NULL successor: R0 = PtrToAllocMem, slot stays Active.
    let mut nonnull = state;
    nonnull.types.set(
        Reg::R0,
        RegType::PtrToAllocMem {
            id: new_ptr_id(),
            mem_size: elem_size,
            ref_id: None,
        },
    );
    nonnull.domain.forget(Reg::R0);
    nonnull.set_tnum(Reg::R0, Tnum::unknown());
    nonnull.clear_scalar_id(Reg::R0);
    clobber_caller_saved(&mut nonnull);
    nonnull.pc = pc + 1;

    vec![nonnull, null]
}

fn clobber_caller_saved(state: &mut State) {
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        state.types.set(r, RegType::NotInit);
        state.domain.forget(r);
        state.set_tnum(r, Tnum::unknown());
        state.clear_scalar_id(r);
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
