// src/analysis/transfer/call/kfunc.rs
//
// Kfunc call transfer (Phase 3 W3.2b).
//
// Minimal enablement scoped to open-coded iterators:
//   bpf_iter_{num,task,css,bits}_{new,next,destroy}
//
// Every other kfunc still fails with UnsupportedModernFeature. When W3.3
// adds exception kfuncs or W3.4 needs callback kfuncs, promote this
// name-match dispatch to a proper signature table.

use log::trace;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, new_iter_id, new_ptr_id};
use crate::analysis::machine::stack_state::{IterKind, IterState, IteratorSlot};
use crate::analysis::machine::state::State;
use crate::analysis::transfer::types::update_store_types;
use crate::ast::MemSize;
use crate::common::constants::MAX_ERRNO;
use crate::common::mem_region_model::bpf_iter_size;
use crate::domains::tnum::Tnum;

/// Top-level kfunc dispatch. Looks up the kfunc name in BTF and routes
/// to the matching transfer. Unknown kfuncs fail loudly.
pub(crate) fn transfer_kfunc(env: &mut VerifierEnv, state: State, btf_id: u32) -> Vec<State> {
    let pc = state.pc;
    let name = env.ctx.btf.kfunc_name(btf_id).map(|s| s.to_string());

    match name.as_deref() {
        Some("bpf_iter_num_new") => iter_new(env, state, IterKind::Num),
        Some("bpf_iter_task_new") => iter_new(env, state, IterKind::Task),
        Some("bpf_iter_css_new") => iter_new(env, state, IterKind::Css),
        Some("bpf_iter_bits_new") => iter_new(env, state, IterKind::Bits),

        Some("bpf_iter_num_next") => iter_next(env, state, IterKind::Num),
        Some("bpf_iter_task_next") => iter_next(env, state, IterKind::Task),
        Some("bpf_iter_css_next") => iter_next(env, state, IterKind::Css),
        Some("bpf_iter_bits_next") => iter_next(env, state, IterKind::Bits),

        Some("bpf_iter_num_destroy") => iter_destroy(env, state, IterKind::Num),
        Some("bpf_iter_task_destroy") => iter_destroy(env, state, IterKind::Task),
        Some("bpf_iter_css_destroy") => iter_destroy(env, state, IterKind::Css),
        Some("bpf_iter_bits_destroy") => iter_destroy(env, state, IterKind::Bits),

        // W3.3b: exception-frame kfuncs. `bpf_throw` is terminal on this
        // path (unwinds out of the program / into the handler); we don't
        // attempt to re-enter at the handler PC here because that requires
        // PSEUDO_FUNC callback-frame plumbing from W3.4. The plumbed
        // program_exception_cb slot (W3.3a) is still useful for future
        // work — `set_exception_callback` writes to it once W3.4 can
        // resolve the handler target.
        Some("bpf_throw") => throw(env, state),
        Some("bpf_set_exception_callback") => set_exception_callback(env, state),

        _ => {
            env.fail(VerificationError::UnsupportedModernFeature {
                pc,
                feature: "kfunc call (BPF_PSEUDO_KFUNC_CALL)",
            });
            vec![]
        }
    }
}

/// Resolve R1 to `(frame_level, base_offset)` for a PtrToStack argument.
/// Returns None (and fails env) if R1 isn't a stack pointer or its offset
/// is symbolic.
fn resolve_iter_arg(
    env: &mut VerifierEnv,
    state: &State,
) -> Option<(crate::analysis::machine::frame_stack::FrameLevel, i16)> {
    let pc = state.pc;
    let RegType::PtrToStack { frame_level } = state.types.get(Reg::R1) else {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
        return None;
    };
    let Some(off) = state.domain.get_distance_fixed(Reg::R1, Reg::R10) else {
        trace!("iter arg on R1 has non-fixed distance to R10");
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
        return None;
    };
    let Ok(off16) = i16::try_from(off) else {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
        return None;
    };
    Some((frame_level, off16))
}

/// Forget caller-saved registers (R1-R5) after a kfunc call.
fn clobber_caller_saved(state: &mut State) {
    for r in [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5] {
        state.domain.forget(r);
        state.set_tnum(r, Tnum::unknown());
        state.clear_scalar_id(r);
    }
}

/// `bpf_iter_*_new(&it, ...)`: transition Uninit → Active on the
/// iterator slot. The iter struct is stack-allocated by the program;
/// we initialize its bytes (scalar-typed, matching PtrToUninitMem
/// semantics) and stamp a fresh iter_id on the base byte.
///
/// R0 is the kernel return: 0 on success, -errno on failure. We
/// return a scalar in `[-MAX_ERRNO, 0]` and keep the iterator Active
/// in both outcomes — the program must call `*_destroy` on all paths
/// regardless, matching kernel semantics.
fn iter_new(env: &mut VerifierEnv, mut state: State, kind: IterKind) -> Vec<State> {
    let pc = state.pc;
    let Some((frame, base_off)) = resolve_iter_arg(env, &state) else {
        return vec![];
    };

    // Double-init: the slot must be Uninit (annotation absent) before
    // `*_new`. Calling `*_new` on an Active or Drained slot leaks the
    // prior iterator — kernel rejects this, so do we.
    if state.stack_at(frame).stack_get_iterator(base_off).is_some() {
        env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
        return vec![];
    }

    let size_bytes = bpf_iter_size(kind);

    let stack = state.stack_at_mut(frame);
    for i in 0..size_bytes {
        let byte_off = base_off as i64 + i as i64;
        update_store_types(stack, RegType::ScalarValue, MemSize::U8, Some(byte_off));
    }
    stack.stack_set_iterator(
        base_off,
        IteratorSlot {
            kind,
            state: IterState::Active,
            id: new_iter_id(),
        },
    );

    state.types.set(Reg::R0, RegType::ScalarValue);
    state.domain.forget(Reg::R0);
    state.domain.assume_ge_imm(Reg::R0, -MAX_ERRNO);
    state.domain.assume_le_imm(Reg::R0, 0);
    state.set_tnum(Reg::R0, Tnum::unknown());
    state.clear_scalar_id(Reg::R0);

    clobber_caller_saved(&mut state);
    state.pc += 1;
    vec![state]
}

/// `bpf_iter_*_next(&it)`: requires an Active iterator at the slot.
/// Forks two successors:
///   - non-NULL: R0 = PtrToAllocMem, slot stays Active.
///   - NULL:     R0 = 0 (scalar), slot → Drained.
///
/// Element-return typing here is the W3.2 simplification — a generic
/// allocated-memory pointer with a conservative size. Phase 4 will
/// upgrade to per-iter-kind PtrToBtfId so programs can dereference
/// into the real element type.
fn iter_next(env: &mut VerifierEnv, state: State, kind: IterKind) -> Vec<State> {
    let pc = state.pc;
    let Some((frame, base_off)) = resolve_iter_arg(env, &state) else {
        return vec![];
    };

    let cur = state.stack_at(frame).stack_get_iterator(base_off);
    match cur {
        Some(IteratorSlot { state: IterState::Active, kind: k, .. }) if k == kind => {}
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
    }

    // Non-NULL successor: R0 = PtrToAllocMem with element-size bound.
    let elem_size: u64 = match kind {
        IterKind::Num => 4,  // int *
        IterKind::Bits => 8, // u64 *
        // task/css return pointers to large opaque kernel structs; we
        // allow a pointer-sized deref as a placeholder until Phase 4
        // swaps in PtrToBtfId for real field-typed access.
        IterKind::Task | IterKind::Css => 8,
    };
    let mut state_nonnull = state.clone();
    state_nonnull.types.set(
        Reg::R0,
        RegType::PtrToAllocMem {
            id: new_ptr_id(),
            mem_size: elem_size,
        },
    );
    state_nonnull.domain.forget(Reg::R0);
    state_nonnull.set_tnum(Reg::R0, Tnum::unknown());
    state_nonnull.clear_scalar_id(Reg::R0);
    clobber_caller_saved(&mut state_nonnull);
    state_nonnull.pc = pc + 1;

    // NULL successor: R0 = scalar 0, slot → Drained.
    let mut state_null = state;
    if let Some(slot) = state_null.stack_at(frame).stack_get_iterator(base_off) {
        state_null.stack_at_mut(frame).stack_set_iterator(
            base_off,
            IteratorSlot {
                state: IterState::Drained,
                ..slot
            },
        );
    }
    state_null.types.set(Reg::R0, RegType::ScalarValue);
    state_null.domain.forget(Reg::R0);
    state_null.domain.assume_ge_imm(Reg::R0, 0);
    state_null.domain.assume_le_imm(Reg::R0, 0);
    state_null.set_tnum(Reg::R0, Tnum::constant(0));
    state_null.clear_scalar_id(Reg::R0);
    clobber_caller_saved(&mut state_null);
    state_null.pc = pc + 1;

    vec![state_nonnull, state_null]
}

/// `bpf_iter_*_destroy(&it)`: accepts Active or Drained, transitions
/// the slot back to Uninit (annotation cleared). Calling destroy on
/// an Uninit slot is a REJECT — mirrors the kernel which rejects
/// "destroying an iterator that was never initialized".
fn iter_destroy(env: &mut VerifierEnv, mut state: State, kind: IterKind) -> Vec<State> {
    let pc = state.pc;
    let Some((frame, base_off)) = resolve_iter_arg(env, &state) else {
        return vec![];
    };

    let cur = state.stack_at(frame).stack_get_iterator(base_off);
    match cur {
        Some(IteratorSlot { kind: k, .. }) if k == kind => {}
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: Reg::R1 });
            return vec![];
        }
    }

    state.stack_at_mut(frame).stack_clear_iterator(base_off);

    // destroy returns void in the kernel, but BPF calls get an R0 — set
    // to scalar unknown and clobber caller-saved like any kfunc.
    state.types.set(Reg::R0, RegType::ScalarValue);
    state.domain.forget(Reg::R0);
    state.set_tnum(Reg::R0, Tnum::unknown());
    state.clear_scalar_id(Reg::R0);

    clobber_caller_saved(&mut state);
    state.pc += 1;
    vec![state]
}

/// `bpf_throw(cookie)`: terminates execution on this path. The kernel
/// either dispatches to the program-default exception callback (if
/// registered) or unwinds out of the program returning 0. Either way
/// the throw site has no in-program successor — we drop the path.
///
/// Exit-style cleanup checks (unreleased refs / iterators / locks) are
/// intentionally skipped: the kernel releases resources for us on the
/// unwind path. R1 (cookie) can be any scalar; we don't validate it.
fn throw(_env: &mut VerifierEnv, _state: State) -> Vec<State> {
    vec![]
}

/// `bpf_set_exception_callback(fn)`: registers the program-default
/// exception handler. R1 is a PSEUDO_FUNC subprog pointer whose target
/// PC we cannot resolve until W3.4 wires PSEUDO_FUNC into the typed
/// register state. For now we accept the call as a no-op on the handler
/// slot — `bpf_throw` is terminal regardless, so the unresolved handler
/// is not observably wrong. Caller-saved regs are clobbered like any
/// kfunc; R0 is a scalar return (0 on success in the kernel).
fn set_exception_callback(_env: &mut VerifierEnv, mut state: State) -> Vec<State> {
    state.types.set(Reg::R0, RegType::ScalarValue);
    state.domain.forget(Reg::R0);
    state.set_tnum(Reg::R0, Tnum::unknown());
    state.clear_scalar_id(Reg::R0);

    clobber_caller_saved(&mut state);
    state.pc += 1;
    vec![state]
}
