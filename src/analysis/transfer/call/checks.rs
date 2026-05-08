use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/call/checks.rs
//
// Argument validation for BPF helper functions.
// Uses table-driven type compatibility and modular validators.

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::{RegType, TypeState};
use crate::analysis::machine::state::State;
use crate::analysis::transfer::memory::access::{self, AccessKind};
use crate::analysis::transfer::memory::{
    check_kptr_field_access, check_map_access, check_map_rw, check_packet_access,
    check_stack_access, check_stack_arg_readable,
};
use crate::common::constants;
use log::{error, info, warn};

use super::compat::is_nullable_arg_type;
use super::signatures::{ArgKind, CallProto, IterArgExpect, MemSizePair, get_helper_proto};
use super::validators;

// ============================================================================
// MapInfo
// ============================================================================

/// Information about a BPF map needed for validation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct MapInfo {
    pub(crate) key_size: u32,
    pub(crate) value_size: u32,
    /// `BPF_MAP_TYPE_*` raw value. Lets validators dispatch on map
    /// type — SOCKMAP/SOCKHASH accept sock pointers as their
    /// `bpf_map_update_elem` value arg; BPF_MAP_TYPE_ARRAY accepts
    /// PtrToMapValue, etc.
    pub(crate) map_type: u32,
}

pub(crate) fn get_map_info(map_type: RegType, env: &VerifierEnv) -> Option<MapInfo> {
    match map_type {
        RegType::PtrToMapObject { map_idx } => env.ctx.map_defs.get(map_idx).map(|md| MapInfo {
            key_size: md.key_size,
            value_size: md.value_size,
            map_type: md.type_,
        }),
        RegType::PtrToMapValue { map_idx, .. } => env.ctx.map_defs.get(map_idx).and_then(|md| {
            if let Some(inner) = md.inner_map_idx {
                env.ctx.map_defs.get(inner).map(|inner_md| MapInfo {
                    key_size: inner_md.key_size,
                    value_size: inner_md.value_size,
                    map_type: inner_md.type_,
                })
            } else {
                None
            }
        }),
        _ => None,
    }
}

// ============================================================================
// ValidationContext
// ============================================================================

/// Context for validating a single helper argument.
/// Provides consistent access to validation state and error handling.
pub(crate) struct ValidationContext<'a, 'b> {
    pub env: &'a mut VerifierEnv<'b>,
    pub state: &'a State,
    pub types: &'a TypeState,
    pub helper: u32,
    pub pc: usize,
    pub reg: Reg,
    pub arg_index: usize,
    pub map_info: &'a Option<MapInfo>,
    pub actual: RegType,
    /// Pointer-size pairs for the call being validated (W4.2d). Lifted
    /// off the proto at call entry so validators can short-circuit
    /// readability checks for pointers covered by an explicit pair
    /// without re-querying by helper id.
    pub mem_size_pairs: &'static [MemSizePair],
}

impl<'a, 'b> ValidationContext<'a, 'b> {
    /// Create a new validation context.
    pub fn new(
        env: &'a mut VerifierEnv<'b>,
        state: &'a State,
        types: &'a TypeState,
        helper: u32,
        pc: usize,
        reg: Reg,
        arg_index: usize,
        map_info: &'a Option<MapInfo>,
        actual: RegType,
        mem_size_pairs: &'static [MemSizePair],
    ) -> Self {
        Self {
            env,
            state,
            types,
            helper,
            pc,
            reg,
            arg_index,
            map_info,
            actual,
            mem_size_pairs,
        }
    }

    /// Report a failure with logging.
    /// Returns false for convenient use in validation functions.
    pub fn fail_with_log(&mut self, error: VerificationError, msg: &str) -> bool {
        error!("{}", msg);
        self.env.fail(error);
        false
    }
}

// ============================================================================
// Main Entry Points
// ============================================================================

/// Validates all arguments for a helper function based on its signature.
pub(crate) fn validate_helper_args(
    env: &mut VerifierEnv,
    state: &State,
    helper: u32,
    types: &TypeState,
    pc: usize,
) {
    let Some(sig) = get_helper_proto(helper) else {
        warn!(
            "[Verifier] Unknown helper {} at pc {}, skipping arg validation",
            helper, pc
        );
        return;
    };

    // Get map info if first arg is a map (needed for key/value size validation)
    let map_info = if matches!(
        sig.args[0],
        ArgKind::ConstMapPtr | ArgKind::ConstMapPtrOfType(_)
    ) {
        get_map_info(types.get(Reg::R1), env)
    } else {
        None
    };

    // Validate each argument
    let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];

    for (i, (&arg_type, &reg)) in sig.args.iter().zip(arg_regs.iter()).enumerate() {
        info!(
            "[Verifier] pc {}: validating arg R{} as {:?}",
            pc,
            i + 1,
            arg_type
        );
        if arg_type == ArgKind::DontCare {
            break; // No more arguments
        }

        let reg_type = types.get(reg);

        if !validate_single_arg(
            env,
            state,
            types,
            helper,
            pc,
            reg,
            arg_type,
            reg_type,
            &map_info,
            i,
            sig.mem_size_pairs,
        ) {
            // Validation failed, error already reported
            return;
        }
    }
}

/// Validates a single argument against its expected type.
/// Returns true if valid, false if invalid (error already reported).
///
/// This is the main dispatcher that routes to category-specific validators.
pub(crate) fn validate_single_arg(
    env: &mut VerifierEnv,
    state: &State,
    types: &TypeState,
    helper: u32,
    pc: usize,
    reg: Reg,
    expected: ArgKind,
    actual: RegType,
    map_info: &Option<MapInfo>,
    arg_index: usize,
    mem_size_pairs: &'static [MemSizePair],
) -> bool {
    // Create validation context
    let mut ctx = ValidationContext::new(
        env,
        state,
        types,
        helper,
        pc,
        reg,
        arg_index,
        map_info,
        actual,
        mem_size_pairs,
    );

    // Handle nullable types first (unified pattern)
    if is_nullable_arg_type(expected) {
        return validators::validate_nullable(&mut ctx, expected);
    }

    // Dispatch to category-specific validators
    match expected {
        ArgKind::DontCare => true,

        // ---- Map-related types ----
        ArgKind::ConstMapPtr => validators::validate_const_map_ptr(&mut ctx),
        ArgKind::ConstMapPtrOfType(t) => {
            validators::validate_const_map_ptr_of_type(&mut ctx, t)
        }
        ArgKind::PtrToMapKey => validators::validate_ptr_to_map_key(&mut ctx),
        ArgKind::PtrToMapValue => validators::validate_ptr_to_map_value(&mut ctx),
        ArgKind::PtrToUninitMapValue => {
            validators::map::validate_ptr_to_uninit_map_value(&mut ctx)
        }

        // ---- Memory types ----
        ArgKind::PtrToMem => validators::validate_ptr_to_mem(&mut ctx),
        ArgKind::PtrToUninitMem => validators::validate_ptr_to_uninit_mem(&mut ctx),
        ArgKind::PtrToAllocMem => validators::validate_ptr_to_alloc_mem(&mut ctx),
        ArgKind::PtrToConstStr => validate_ptr_to_const_str(&mut ctx),

        // ---- Socket types ----
        ArgKind::PtrToSocket
        | ArgKind::PtrToSockCommon
        | ArgKind::PtrToBTFIdSockCommon => validators::validate_socket_arg(&mut ctx, expected),

        // ---- Scalar/size types ----
        ArgKind::ConstSize => validators::validate_const_size(&mut ctx),
        ArgKind::ConstSizeOrZero | ArgKind::ConstAllocSizeOrZero => {
            validators::validate_const_size_or_zero(&mut ctx)
        }

        // ---- Simple pointer types (inline validation) ----
        ArgKind::PtrToCtx => validate_ptr_to_ctx(&mut ctx),
        ArgKind::PtrToBtfId => validate_ptr_to_btf_id(&mut ctx),
        ArgKind::PtrToBtfIdNamed { type_name } => {
            validate_ptr_to_btf_id_named(&mut ctx, type_name)
        }
        ArgKind::PtrToStack => validate_ptr_to_stack(&mut ctx),
        ArgKind::PtrToLong => validate_ptr_to_long(&mut ctx),
        ArgKind::PtrToCallback => validate_ptr_to_callback(&mut ctx),

        // ---- Dynptr (W4.2c) ----
        ArgKind::DynptrArg { uninit, rdwr_only } => {
            validate_dynptr_arg(&mut ctx, uninit, rdwr_only)
        }

        // ---- Iterator (W4.3) ----
        ArgKind::IterArg { kind, expected } => validate_iter_arg(&mut ctx, kind, expected),

        // ---- IRQ flag ----
        ArgKind::IrqFlagArg { uninit, kfunc_class } => {
            validate_irq_flag_arg(&mut ctx, uninit, kfunc_class)
        }

        ArgKind::ResSpinLockArg { is_irq: _ } => validate_res_spin_lock_arg(&mut ctx),

        // ---- Map-value special field (W5.1) ----
        ArgKind::MapValueSpecial { kind } => validate_map_value_special(&mut ctx, kind),

        // ---- Cpumask (W5.3) ----
        ArgKind::PtrToCpumask => validate_ptr_to_cpumask(&mut ctx),
        ArgKind::PtrToCpumaskRead => validate_ptr_to_cpumask_read(&mut ctx),

        // ---- Cgroup (W6.3-followon) ----
        ArgKind::PtrToCgroup => validate_ptr_to_cgroup(&mut ctx),
        ArgKind::PtrToTask => validate_ptr_to_task(&mut ctx),

        // ---- Arena (W5.5) ----
        ArgKind::PtrToArena => validate_ptr_to_arena(&mut ctx),

        // ---- Owned kptr (W5.4) ----
        ArgKind::PtrToOwnedKptr => validate_ptr_to_owned_kptr(&mut ctx),

        // ---- Anything (just needs to be readable) ----
        ArgKind::Anything => true,

        // Nullable variants are handled above
        ArgKind::PtrToCtxOrNull
        | ArgKind::PtrToMemOrNull
        | ArgKind::PtrToUninitMemOrNull
        | ArgKind::PtrToStackOrNull
        | ArgKind::PtrToMapValueOrNull => {
            // Should not reach here due to is_nullable_arg_type check
            true
        }
    }
}

/// Internal validation that can be called from nullable validator
pub(crate) fn validate_single_arg_inner(
    env: &mut VerifierEnv,
    state: &State,
    types: &TypeState,
    helper: u32,
    pc: usize,
    reg: Reg,
    expected: ArgKind,
    actual: RegType,
    map_info: &Option<MapInfo>,
    arg_index: usize,
    mem_size_pairs: &'static [MemSizePair],
) -> bool {
    validate_single_arg(
        env,
        state,
        types,
        helper,
        pc,
        reg,
        expected,
        actual,
        map_info,
        arg_index,
        mem_size_pairs,
    )
}

// ============================================================================
// Simple Pointer Type Validators (inline for brevity)
// ============================================================================

fn validate_ptr_to_ctx(ctx: &mut ValidationContext) -> bool {
    use crate::analysis::machine::reg_types::PtrFlags;
    let mut ok = matches!(ctx.actual, RegType::PtrToCtx)
        // Kernel `check_kfunc_call` accepts both PTR_TO_CTX and a
        // trusted `PTR_TO_BTF_ID + sk_buff` for kfuncs like
        // `bpf_dynptr_from_skb`. The latter arises from `ctx->skb`
        // of `bpf_nf_ctx` (Netfilter) — closes
        // `verifier_netfilter_ctx::with_valid_ctx_access_test6`.
        || matches!(
            ctx.actual,
            RegType::PtrToBtfId { type_name: "sk_buff", flags, .. }
                if flags.contains(PtrFlags::TRUSTED)
        );
    // bpf_get_socket_cookie has 4 per-prog-type kernel protos:
    // skb-ctx / sock_addr-ctx (covered above by PtrToCtx) plus
    // PTR_TO_SOCKET (sock-class progs) and PTR_TO_BTF_ID rooted at
    // sock_common (iter/tracing). Admit those shapes for this helper
    // only, so ctx-offset validation stays strict for skb-class users.
    if !ok && ctx.helper == crate::common::constants::BPF_GET_SOCKET_COOKIE {
        ok = matches!(
            ctx.actual,
            RegType::PtrToSocket { .. }
                | RegType::PtrToSockCommon { .. }
                | RegType::PtrToTcpSock { .. }
        ) || matches!(
            ctx.actual,
            RegType::PtrToBtfId { type_name, flags, .. }
                if flags.contains(PtrFlags::TRUSTED)
                    && matches!(type_name,
                        "sock_common" | "sock" | "tcp_sock" | "tcp6_sock"
                            | "udp_sock" | "udp6_sock" | "unix_sock"
                            | "tcp_request_sock" | "tcp_timewait_sock")
        );
    }
    if !ok {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_CTX, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

fn validate_ptr_to_btf_id(ctx: &mut ValidationContext) -> bool {
    // The specialized kernel-struct reg-types (PtrToTask, PtrToCgroup,
    // PtrToCpumask, …) are the same kernel object as the generic
    // `PtrToBtfId{type_name=<X>, ...}`; helpers/kfuncs that demand "any
    // PTR_TO_BTF_ID" (no specific struct match) should accept the
    // specialized form too. Without this, e.g.
    // `bpf_copy_from_user_task(..., bpf_get_current_task_btf(), ...)`
    // rejects R4=PtrToTask under the loose proto. Mirrors the
    // equivalence already wired in `validate_ptr_to_btf_id_named`.
    let is_specialized_btf = matches!(
        ctx.actual,
        RegType::PtrToTask { .. }
            | RegType::PtrToCgroup { .. }
            | RegType::PtrToCpumask { .. }
    );
    if !matches!(ctx.actual, RegType::PtrToBtfId { .. }) && !is_specialized_btf {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_BTF_ID, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// Strict variant: arg must be `PtrToBtfId{type_name == expected, ..}`.
/// Drives kfuncs like `bpf_path_d_path` whose first arg is `struct
/// path *` — closes the cluster B residual FA where the test passes
/// `(struct path *)&file->f_task_work` (an interior pointer of type
/// `callback_head` after our new field-arithmetic typing) to the
/// kfunc.
fn validate_ptr_to_btf_id_named(
    ctx: &mut ValidationContext,
    expected: &'static str,
) -> bool {
    // The specialized PtrTo<X> reg-types (PtrToCgroup, PtrToTask, …) are
    // semantically the same kernel struct as the generic
    // PtrToBtfId{type_name=<X>} produced by BTF-typed entry args. A caller
    // that demands "any PTR_TO_BTF_ID for struct cgroup" should accept the
    // specialized form too — otherwise threading an acquired
    // `bpf_task_get_cgroup1(...)` result into `bpf_cgrp_storage_get(R2=cgrp)`
    // rejects on a type-equivalence we deliberately model with a narrower
    // representation.
    let matches = match (expected, ctx.actual) {
        (e, RegType::PtrToBtfId { type_name, .. }) if type_name == e => true,
        ("cgroup", RegType::PtrToCgroup { .. }) => true,
        ("task_struct", RegType::PtrToTask { .. }) => true,
        // PtrToMapKptr from a kptr-field load or bpf_kptr_xchg. Accept
        // when the pointee btf-id resolves to the requested struct name.
        // The ref_id is irrelevant for type-name matching; KF_RELEASE
        // kfuncs separately verify ref_id via the RELEASE precondition
        // gate in transfer_kfunc_proto. Mirrors the cpumask + cgroup
        // validate_ptr_to_* extensions.
        (e, RegType::PtrToMapKptr { pointee_btf_id, .. })
            if ctx.env.ctx.btf.struct_or_fwd_name(pointee_btf_id) == Some(e) =>
        {
            true
        }
        _ => false,
    };
    if matches {
        return true;
    }
    ctx.fail_with_log(
        VerificationError::InvalidArgType {
            pc: ctx.pc,
            reg: ctx.reg,
        },
        &format!(
            "[Verifier] pc {}: R{} expected PTR_TO_BTF_ID(struct {}), got {:?}",
            ctx.pc,
            ctx.arg_index + 1,
            expected,
            ctx.actual
        ),
    )
}

/// Validate `ArgKind::PtrToCpumask` (W5.3).
///
/// Only the non-null `RegType::PtrToCpumask` is accepted: cpumask
/// kfuncs (set_cpu / test_cpu / first / release) all require the
/// program to have null-checked the freshly-created pointer first.
/// `PtrToCpumaskOrNull` would short-circuit fail because the pointer
/// could legitimately be null at the call site.
fn validate_ptr_to_cpumask(ctx: &mut ValidationContext) -> bool {
    // Strict: mutating cpumask consumers only accept the
    // acquire-tracked specialization. See ArgKind::PtrToCpumask docs.
    // Also accept an acquire-tracked `PtrToMapKptr{bpf_cpumask, ref_id:
    // Some}` produced by `bpf_kptr_xchg` — semantically the same
    // refcounted-cpumask handoff (closes test_insert_remove_release's
    // bpf_cpumask_release call site).
    let is_acquired_map_kptr = matches!(
        ctx.actual,
        RegType::PtrToMapKptr { ref_id: Some(_), pointee_btf_id, .. }
            if matches!(
                ctx.env.ctx.btf.struct_or_fwd_name(pointee_btf_id),
                Some("bpf_cpumask")
            )
    );
    if !matches!(ctx.actual, RegType::PtrToCpumask { .. }) && !is_acquired_map_kptr {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_CPUMASK, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// Validate `ArgKind::PtrToCpumaskRead` — read-only KF_RCU consumers.
/// Accepts `PtrToCpumask` (the bpf_cpumask wrapper passes the const
/// arg), `PtrToBtfId{cpumask|bpf_cpumask, TRUSTED}` produced by the
/// BTF field-load typing path (`task->cpus_ptr`, `&task->cpus_mask`),
/// and `PtrToMapKptr{cpumask|bpf_cpumask}` loaded from a `__kptr` /
/// `__rcu` map field — TRUSTED unconditionally, or RCU when inside
/// an active `bpf_rcu_read_lock` section (mirrors kernel KF_RCU
/// acceptance of MEM_RCU pointers; out-of-RCU loads keep failing
/// with the kernel's "must be a rcu pointer" rejection).
fn validate_ptr_to_cpumask_read(ctx: &mut ValidationContext) -> bool {
    use crate::analysis::machine::reg_types::PtrFlags;
    let is_btf_cpumask = matches!(
        ctx.actual,
        RegType::PtrToBtfId { type_name, flags, .. }
            if (type_name == "cpumask" || type_name == "bpf_cpumask")
                && flags.contains(PtrFlags::TRUSTED)
    );
    let is_map_kptr_cpumask = if let RegType::PtrToMapKptr { pointee_btf_id, ref_id, flags, .. } =
        ctx.actual
    {
        let name = ctx.env.ctx.btf.struct_or_fwd_name(pointee_btf_id);
        let name_ok = matches!(name, Some("cpumask") | Some("bpf_cpumask"));
        // Acquire-tracked (ref_id Some — from bpf_kptr_xchg) is trusted
        // unconditionally. Otherwise the load came from a `__kptr` /
        // `__rcu` field at-rest in a map; the kernel admits these as
        // KF_RCU-compatible only inside an active bpf_rcu_read_lock
        // region (rejected as "must be a rcu pointer" otherwise).
        let trust_ok = ref_id.is_some()
            || flags.contains(PtrFlags::TRUSTED)
            || ((flags.contains(PtrFlags::RCU) || flags.contains(PtrFlags::MEM_ALLOC))
                && ctx.state.in_rcu_read_section());
        name_ok && trust_ok
    } else {
        false
    };
    if !matches!(ctx.actual, RegType::PtrToCpumask { .. })
        && !is_btf_cpumask
        && !is_map_kptr_cpumask
    {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_CPUMASK_READ, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// Validate `ArgKind::PtrToCgroup` (W6.3-followon).
///
/// Mirrors `validate_ptr_to_cpumask`: only the non-null
/// `RegType::PtrToCgroup` is accepted. Cgroup consumers
/// (`bpf_cgroup_acquire` / `_release`) require the program to have
/// null-checked the freshly-minted ref first.
fn validate_ptr_to_cgroup(ctx: &mut ValidationContext) -> bool {
    // PtrToCgroup covers acquire-tracked cgroups (`bpf_cgroup_acquire`,
    // `bpf_cgroup_from_id`). For BPF_PROG-style tp_btf/lsm/tracing
    // programs that take `struct cgroup *cgrp` directly, the entry-arg
    // seeder produces `PtrToBtfId{cgroup, TRUSTED}` — also accept that
    // shape. Mirrors the validate_ptr_to_task fallback.
    // PtrToMapKptr{cgroup}: either acquire-tracked (ref_id Some, from
    // bpf_kptr_xchg) or a raw `__kptr` field load (ref_id None). The
    // kernel admits either for KF_RCU consumers like
    // bpf_cgroup_ancestor; KF_TRUSTED_ARGS / KF_RELEASE consumers
    // require acquire-tracked. We don't differentiate at this layer
    // (CallFlags isn't plumbed in), so the more-permissive form is
    // chosen — surfaces FAs on cgrp_kfunc_failure tests that intend
    // the raw-load → release rejection ("must be referenced or
    // trusted"), kept per feedback_additive_vs_invasive.md.
    let is_map_kptr_cgroup = matches!(
        ctx.actual,
        RegType::PtrToMapKptr { pointee_btf_id, .. }
            if matches!(
                ctx.env.ctx.btf.struct_or_fwd_name(pointee_btf_id),
                Some("cgroup")
            )
    );
    if !matches!(ctx.actual, RegType::PtrToCgroup { .. })
        && !matches!(
            ctx.actual,
            RegType::PtrToBtfId { type_name: "cgroup", flags, .. }
                if flags.contains(crate::analysis::machine::reg_types::PtrFlags::TRUSTED)
        )
        && !is_map_kptr_cgroup
    {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_CGROUP, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// Validate `ArgKind::PtrToTask` (Phase 7 wrap-up). Same shape as
/// `validate_ptr_to_cgroup`: only non-null `RegType::PtrToTask`
/// accepted. `bpf_task_acquire`/`_release` consumers require the
/// program to have null-checked an `OrNull` result first.
fn validate_ptr_to_task(ctx: &mut ValidationContext) -> bool {
    // PtrToTask covers acquire-tracked tasks (`bpf_task_acquire`,
    // `bpf_task_from_pid`, `bpf_get_current_task_btf`). For BPF_PROG-style
    // tracing/tp_btf/lsm programs that take `struct task_struct *task`
    // directly (clang's BPF_PROG macro unpacks ctx[N*8] into the typed
    // arg), the entry-arg seeder produces `PtrToBtfId{task_struct, TRUSTED}`
    // — also accept that shape. Other kernel structs the BPF_PROG macro
    // exposes via name use the generic `ArgKind::PtrToBtfId` validator;
    // task is the special case because we have a dedicated reg-type
    // specialization for it.
    // Also accept a PtrToMapKptr pointing at task_struct (kernel models
    // both raw kptr-field loads and xchg-results as PTR_TO_BTF_ID|MEM_ALLOC
    // with task BTF id). Refcount-aware gating still happens downstream:
    // the KF_RELEASE precondition (kfunc.rs `proto.flags.contains(RELEASE)`)
    // rejects when the arg lacks a ref_id, so a raw kptr-field load
    // passed to bpf_task_release is still rejected — but the same shape
    // passed to KF_ACQUIRE | KF_RCU `bpf_task_acquire` is admitted.
    // Closes test_task_acquire_leave_in_map / test_task_xchg_release /
    // test_task_map_acquire_release.
    let map_kptr_task = matches!(
        ctx.actual,
        RegType::PtrToMapKptr { pointee_btf_id, .. }
            if ctx.env.ctx.btf.struct_name(pointee_btf_id) == Some("task_struct")
    );
    if !matches!(ctx.actual, RegType::PtrToTask { .. })
        && !matches!(
            ctx.actual,
            RegType::PtrToBtfId { type_name: "task_struct", flags, .. }
                if flags.contains(crate::analysis::machine::reg_types::PtrFlags::TRUSTED)
                    || flags.contains(crate::analysis::machine::reg_types::PtrFlags::RCU)
        )
        && !map_kptr_task
    {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_TASK, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// Validate `ArgKind::PtrToArena` (W5.5).
///
/// Kernel `verifier.c` ~L10370 (v6.15) for `ARG_PTR_TO_ARENA`:
/// "only PTR_TO_ARENA or SCALAR make sense" — both shapes are
/// accepted. A scalar arg is the runtime case where the program
/// loaded an arena value from a `__arena *` global (loads from
/// PtrToArena `mark_reg_unknown`, kernel `verifier.c` ~L7639) and
/// passes it back into a free helper without re-casting. The kernel
/// rejects everything else as "not a pointer to arena or scalar".
fn validate_ptr_to_arena(ctx: &mut ValidationContext) -> bool {
    if !matches!(
        ctx.actual,
        RegType::PtrToArena { .. } | RegType::ScalarValue
    ) {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_ARENA or SCALAR, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// Validate `ArgKind::PtrToOwnedKptr` (W5.4).
///
/// Accepts either:
///   - `PtrToOwnedKptr` (from `bpf_obj_new` + null-check), or
///   - `PtrToMapKptr { flags: MEM_ALLOC, ref_id: Some(_) }` from
///     `bpf_kptr_xchg` of a `__kptr` (Ref) slot + null-check. Kernel
///     models the xchg-returned pointer as `PTR_TO_BTF_ID | MEM_ALLOC`
///     with refcount-tracking — semantically equivalent to a freshly
///     `bpf_obj_new`'d kptr (drop / list-push / rbtree-add accept it).
///     `__kptr_rcu` / `__kptr_percpu` slots produce other flag bands
///     and are still rejected here (kernel admits drop only on
///     MEM_ALLOC).
fn validate_ptr_to_owned_kptr(ctx: &mut ValidationContext) -> bool {
    use crate::analysis::machine::reg_types::PtrFlags;
    // PtrToMapKptr w/ MEM_ALLOC covers two flows:
    //   - `bpf_kptr_xchg` of a `__kptr` (Ref) slot — sets ref_id to the
    //     new acquire id, ownership transfers out of the map. Drop /
    //     graph-add accept it.
    //   - Plain LOAD of a `__kptr` field (`s->stashed`) — ref_id stays
    //     None, no ownership transfer. Kernel admits this for
    //     `bpf_refcount_acquire` (which bumps refcount and returns a
    //     fresh owned ref); `bpf_obj_drop` and graph-add reject via
    //     the downstream KF_RELEASE precondition (kfunc.rs:287
    //     `actual.get_ref_id().is_none()`), so accepting both shapes
    //     here is safe — the per-kfunc gate catches the wrong-shape
    //     case after the type check.
    let ok = match ctx.actual {
        RegType::PtrToOwnedKptr { .. } => true,
        RegType::PtrToMapKptr { flags, .. } => flags.contains(PtrFlags::MEM_ALLOC),
        _ => false,
    };
    if !ok {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_OWNED_KPTR, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

fn validate_ptr_to_stack(ctx: &mut ValidationContext) -> bool {
    if !matches!(ctx.actual, RegType::PtrToStack { .. }) {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_STACK, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// Validate `ArgKind::DynptrArg` (W4.2c).
///
/// The actual reg must be a `PtrToStack` aimed at the dynptr's first
/// slot. Behavior splits on `uninit`:
///
/// - `uninit = true` (constructor sink): neither the base slot nor its
///   trailing partner may carry a prior dynptr annotation. A pre-
///   existing annotation means the program would overwrite an active
///   dynptr — for `Ringbuf` this leaks the reservation; for the others
///   we follow the kernel's defensive REJECT.
///
/// - `uninit = false` (consumer): the base slot must hold a dynptr with
///   `first_slot == true`. Mid-pair pointers (someone aimed `+8` at the
///   second slot) are rejected. If `rdwr_only` is set, an `rdonly`
///   dynptr is rejected (e.g. `bpf_dynptr_write` on an `Skb` dynptr).
fn validate_dynptr_arg(ctx: &mut ValidationContext, uninit: bool, rdwr_only: bool) -> bool {
    // Kernel `PTR_TO_DYNPTR` (e.g. user-ringbuf cb's R1, set by
    // `set_user_ringbuf_callback_state` verifier.c v6.15 ~L10800):
    // accepted by consumer kfuncs (`uninit:false`); rejected by
    // constructors (`uninit:true`, kernel "Dynptr has to be an
    // uninitialized dynptr"); rdwr-only consumers reject `rdonly`
    // (kernel "cannot write into rdonly dynptr"). The PTR_TO_DYNPTR
    // is kernel-managed, not stack-based — there's no slot to inspect.
    if let RegType::PtrToDynptr { rdonly, .. } = ctx.actual {
        if uninit {
            return ctx.fail_with_log(
                VerificationError::InvalidArgType {
                    pc: ctx.pc,
                    reg: ctx.reg,
                },
                &format!(
                    "[Verifier] pc {}: R{} cannot pass PTR_TO_DYNPTR to dynptr constructor (kernel: 'Dynptr has to be an uninitialized dynptr')",
                    ctx.pc,
                    ctx.arg_index + 1
                ),
            );
        }
        // PTR_TO_DYNPTR carries no acquire ref — kernel-managed.
        // Release-class consumers (`bpf_ringbuf_{submit,discard}_dynptr`)
        // require a refcounted (Ringbuf) dynptr; kernel
        // `release_reference` rejects with "cannot release unowned
        // const bpf_dynptr" (verifier.c v6.15 ~L11800).
        if matches!(
            ctx.helper,
            crate::common::constants::BPF_RINGBUF_SUBMIT_DYNPTR
                | crate::common::constants::BPF_RINGBUF_DISCARD_DYNPTR
        ) {
            return ctx.fail_with_log(
                VerificationError::InvalidArgType {
                    pc: ctx.pc,
                    reg: ctx.reg,
                },
                &format!(
                    "[Verifier] pc {}: R{} cannot release unowned const bpf_dynptr (PTR_TO_DYNPTR)",
                    ctx.pc,
                    ctx.arg_index + 1
                ),
            );
        }
        if rdwr_only && rdonly {
            return ctx.fail_with_log(
                VerificationError::InvalidArgType {
                    pc: ctx.pc,
                    reg: ctx.reg,
                },
                &format!(
                    "[Verifier] pc {}: R{} cannot pass rdonly PTR_TO_DYNPTR to rdwr-only kfunc",
                    ctx.pc,
                    ctx.arg_index + 1
                ),
            );
        }
        return true;
    }
    let RegType::PtrToStack { frame_level } = ctx.actual else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected &bpf_dynptr (PTR_TO_STACK), got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    };

    let Some(off) = ctx.state.domain.get_distance_fixed(ctx.reg, Reg::R10) else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} dynptr arg has non-fixed stack offset",
                ctx.pc,
                ctx.arg_index + 1
            ),
        );
    };
    let Ok(base_off) = i16::try_from(off) else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} dynptr arg offset {} out of i16 range",
                ctx.pc,
                ctx.arg_index + 1,
                off
            ),
        );
    };

    let stack = ctx.state.stack_at(frame_level);
    let base = stack.stack_get_dynptr(base_off);
    let trail = stack.stack_get_dynptr(base_off + 8);

    if uninit {
        // Kernel `is_dynptr_reg_valid_uninit` (verifier.c v6.15 L934)
        // returns true for stack slots — overwrite is allowed.
        // `destroy_if_dynptr_stack_slot` (L880) runs first and only
        // rejects if the existing dynptr is *refcounted*
        // (`dynptr_type_refcounted`, our `Ringbuf` with `ref_id != 0`).
        // For unrefcounted (`Local`/`Skb`/`Xdp`), it tears down both
        // pair slots and invalidates slices tagged with the old
        // `dynptr_id` — that destroy-and-sweep step is performed by
        // the `DynptrInitOnArg` side-effect applier (which runs on
        // success and already mutates the stack to stamp the new
        // annotation), keeping `ctx.state` read-only here.
        for slot in [base, trail].into_iter().flatten() {
            if slot.ref_id != 0 {
                return ctx.fail_with_log(
                    VerificationError::InvalidArgType {
                        pc: ctx.pc,
                        reg: ctx.reg,
                    },
                    &format!(
                        "[Verifier] pc {}: R{} cannot overwrite referenced dynptr",
                        ctx.pc,
                        ctx.arg_index + 1
                    ),
                );
            }
        }
        return true;
    }

    let Some(slot) = base else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} dynptr arg points at uninitialized stack",
                ctx.pc,
                ctx.arg_index + 1
            ),
        );
    };
    if !slot.first_slot {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} dynptr arg aimed at trailing slot of pair",
                ctx.pc,
                ctx.arg_index + 1
            ),
        );
    }
    if rdwr_only && slot.rdonly {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} rdonly dynptr passed where rdwr required",
                ctx.pc,
                ctx.arg_index + 1
            ),
        );
    }
    true
}

/// Validate `ArgKind::IterArg` (W4.3).
///
/// The actual reg must be a `PtrToStack` aimed at the iterator slot's
/// base offset. The slot's recorded `kind` must match `kind`, and its
/// state must satisfy `expected`:
///
/// - `Uninit`            — no annotation present (constructor sink).
/// - `Active`            — slot exists, `state == Active` (`*_next`).
/// - `ActiveOrDrained`   — slot exists, any state (`*_destroy`).
fn validate_iter_arg(
    ctx: &mut ValidationContext,
    kind: crate::analysis::machine::stack_state::IterKind,
    expected: IterArgExpect,
) -> bool {
    use crate::analysis::machine::stack_state::IterState;

    let RegType::PtrToStack { frame_level } = ctx.actual else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!(
                "[Verifier] pc {}: R{} expected &bpf_iter_* (PTR_TO_STACK), got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    };
    let Some(off) = ctx.state.domain.get_distance_fixed(ctx.reg, Reg::R10) else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!(
                "[Verifier] pc {}: R{} iter arg has non-fixed stack offset",
                ctx.pc,
                ctx.arg_index + 1
            ),
        );
    };
    let Ok(base_off) = i16::try_from(off) else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!(
                "[Verifier] pc {}: R{} iter arg offset {} out of i16 range",
                ctx.pc,
                ctx.arg_index + 1,
                off
            ),
        );
    };

    let cur = ctx.state.stack_at(frame_level).stack_get_iterator(base_off);
    let ok = match (expected, cur) {
        (IterArgExpect::Uninit, None) => true,
        (IterArgExpect::Active, Some(slot)) => {
            slot.kind == kind && matches!(slot.state, IterState::Active)
        }
        (IterArgExpect::ActiveOrDrained, Some(slot)) => slot.kind == kind,
        _ => false,
    };
    if !ok {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!(
                "[Verifier] pc {}: R{} iter arg kind/state mismatch (expected {:?} {:?}, got {:?})",
                ctx.pc,
                ctx.arg_index + 1,
                kind,
                expected,
                cur
            ),
        );
    }
    true
}

/// Validate `ArgKind::IrqFlagArg`. Mirrors kernel
/// `is_irq_flag_reg_valid_uninit` (~L1243) for `uninit=true`, and the
/// release-side checks at `unmark_stack_slot_irq_flag` (~L1190) for
/// `uninit=false`. The actual reg must be `PtrToStack` aimed at the
/// 8-byte slot; for the destructor side, the slot's annotation must
/// have a matching `kfunc_class` and an `id` equal to `active_irq_id`.
fn validate_irq_flag_arg(
    ctx: &mut ValidationContext,
    uninit: bool,
    kfunc_class: crate::analysis::machine::stack_state::IrqKfuncClass,
) -> bool {
    let RegType::PtrToStack { frame_level } = ctx.actual else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!(
                "[Verifier] pc {}: R{} expected &irq_flag (PTR_TO_STACK), got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    };
    let Some(off) = ctx.state.domain.get_distance_fixed(ctx.reg, Reg::R10) else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!("[Verifier] pc {}: irq flag arg has non-fixed stack offset", ctx.pc),
        );
    };
    let Ok(base_off) = i16::try_from(off) else {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!("[Verifier] pc {}: irq flag arg offset {} out of i16 range", ctx.pc, off),
        );
    };

    let stack = ctx.state.stack_at(frame_level);
    let cur = stack.stack_get_irq_flag(base_off);
    if uninit {
        // Reject if this slot already carries any tracked annotation:
        // an existing IRQ flag (kernel "expected uninitialized"), an
        // iterator (kernel "irq_save_iter" rejects similarly via
        // STACK_ITER vs STACK_IRQ_FLAG mismatch), or a dynptr.
        if cur.is_some() {
            return ctx.fail_with_log(
                VerificationError::IrqState {
                    pc: ctx.pc,
                    reason: "expected uninitialized irq flag slot".into(),
                },
                "irq_save on already-saved slot",
            );
        }
        if stack.stack_get_iterator(base_off).is_some()
            || stack.stack_get_dynptr(base_off).is_some()
        {
            return ctx.fail_with_log(
                VerificationError::IrqState {
                    pc: ctx.pc,
                    reason: "expected uninitialized stack slot for irq flag".into(),
                },
                "irq_save on iterator/dynptr slot",
            );
        }
        true
    } else {
        let Some(slot) = cur else {
            return ctx.fail_with_log(
                VerificationError::IrqState {
                    pc: ctx.pc,
                    reason: "expected an initialized irq flag".into(),
                },
                "irq_restore on uninitialized slot",
            );
        };
        if slot.kfunc_class != kfunc_class {
            return ctx.fail_with_log(
                VerificationError::IrqState {
                    pc: ctx.pc,
                    reason: "irq flag acquired by different kfunc class".into(),
                },
                "irq_restore kfunc class mismatch",
            );
        }
        match ctx.state.active_irq_id() {
            Some(top) if top == slot.id => true,
            _ => ctx.fail_with_log(
                VerificationError::IrqState {
                    pc: ctx.pc,
                    reason: "cannot restore irq state out of order".into(),
                },
                "irq_restore LIFO violation",
            ),
        }
    }
}

/// Validate `ArgKind::MapValueSpecial` (W5.1).
///
/// The actual reg must be `PtrToMapValue { offset, map_idx }` where the
/// map's value BTF carries a `SpecialField` of the requested `kind` at
/// exactly `offset`. Drives `bpf_timer_*` arg validation and is reusable
/// for any kfunc/helper that takes a pointer aimed at a kernel-defined
/// embedded field (spin_lock, rb_root, list_head, refcount, ...).
fn validate_map_value_special(
    ctx: &mut ValidationContext,
    kind: crate::parsing::btf::SpecialFieldKind,
) -> bool {
    // Resolve (pointee_btf_id, byte_offset) for either:
    //   - PtrToMapValue → map value BTF + reg offset
    //   - PtrToOwnedKptr (bpf_obj_new'd struct) → pointee_btf_id + reg offset
    // Kernel `process_spin_lock` at verifier.c v6.15 L8271 accepts both
    // ("arg#0 doesn't point to map value or allocated object" is the
    // negated error). Without this, every linked_list / local_kptr_stash
    // test that calls `bpf_spin_lock(&node->lock)` after `bpf_obj_new`
    // rejects.
    let (val_type_id, off) = match ctx.actual {
        RegType::PtrToMapValue { offset, map_idx, .. } => {
            let Some(off) = offset else {
                return ctx.fail_with_log(
                    VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
                    &format!(
                        "[Verifier] pc {}: R{} {:?}-field arg has variable offset",
                        ctx.pc,
                        ctx.arg_index + 1,
                        kind
                    ),
                );
            };
            let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx) else {
                return ctx.fail_with_log(
                    VerificationError::MapNotFound { pc: ctx.pc, map_idx },
                    &format!(
                        "[Verifier] pc {}: R{} {:?}-field arg references unknown map idx {}",
                        ctx.pc,
                        ctx.arg_index + 1,
                        kind,
                        map_idx
                    ),
                );
            };
            let Some(val_type_id) = map_def.btf_val_type_id else {
                return ctx.fail_with_log(
                    VerificationError::InvalidBtfType,
                    &format!(
                        "[Verifier] pc {}: R{} {:?}-field arg's map has no value-type BTF",
                        ctx.pc,
                        ctx.arg_index + 1,
                        kind
                    ),
                );
            };
            (val_type_id, off)
        }
        RegType::PtrToOwnedKptr { pointee_btf_id: Some(btf_id), offset, .. } => {
            (btf_id, offset as i64)
        }
        _ => {
            return ctx.fail_with_log(
                VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
                &format!(
                    "[Verifier] pc {}: R{} expected PTR_TO_MAP_VALUE or PTR_TO_OWNED_KPTR aimed at {:?} field, got {:?}",
                    ctx.pc,
                    ctx.arg_index + 1,
                    kind,
                    ctx.actual
                ),
            );
        }
    };
    let fields = ctx.env.ctx.btf.find_special_fields(val_type_id);
    let matched = fields
        .iter()
        .any(|f| f.kind == kind && f.offset as i64 == off);
    if !matched {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!(
                "[Verifier] pc {}: R{} {:?}-field arg offset {} doesn't match any {:?} field in map value",
                ctx.pc,
                ctx.arg_index + 1,
                kind,
                off,
                kind
            ),
        );
    }
    true
}

/// `bpf_res_spin_lock{,_irqsave}` / `_unlock{,_irqrestore}` arg.
/// Mirrors kernel `process_spin_lock` (verifier.c v6.15 L8271+) for
/// `is_res_lock = true`:
///   - reg type must be `PtrToMapValue` or `PtrToOwnedKptr`
///     (kernel "arg#0 doesn't point to map value or allocated object");
///   - offset must be constant (we get this from the
///     `PtrToMapValue.offset: Option<u32>` shape; PtrToOwnedKptr's
///     offset is i32 always-known);
///   - for `PtrToMapValue`: the map's value-type BTF must carry a
///     `bpf_res_spin_lock` field at the constant offset (covers
///     `no_lock_map`, `bad_off`, `var_off` siblings).
///
/// PtrToOwnedKptr-side field validation is not yet wired (kptr's
/// underlying BTF id isn't on the variant); accepting it here means
/// `res_spin_lock_no_lock_kptr` flips from PASS-via-Unsupported to FA.
/// Documented as a known partial — see project memory.
fn validate_res_spin_lock_arg(ctx: &mut ValidationContext) -> bool {
    use crate::parsing::btf::SpecialFieldKind;
    match ctx.actual {
        RegType::PtrToMapValue { offset, map_idx, .. } => {
            let Some(off) = offset else {
                return ctx.fail_with_log(
                    VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
                    &format!(
                        "[Verifier] pc {}: R{} bpf_res_spin_lock arg has variable offset",
                        ctx.pc, ctx.arg_index + 1
                    ),
                );
            };
            let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx) else {
                return ctx.fail_with_log(
                    VerificationError::MapNotFound { pc: ctx.pc, map_idx },
                    "map not found",
                );
            };
            let Some(val_type_id) = map_def.btf_val_type_id else {
                return ctx.fail_with_log(
                    VerificationError::InvalidBtfType,
                    "map value-type BTF missing for res_spin_lock arg",
                );
            };
            let fields = ctx.env.ctx.btf.find_special_fields(val_type_id);
            let matched = fields
                .iter()
                .any(|f| f.kind == SpecialFieldKind::ResSpinLock && f.offset as i64 == off);
            if !matched {
                return ctx.fail_with_log(
                    VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
                    &format!(
                        "[Verifier] pc {}: R{} bpf_res_spin_lock arg offset {} doesn't match any bpf_res_spin_lock field in map value",
                        ctx.pc, ctx.arg_index + 1, off
                    ),
                );
            }
            true
        }
        RegType::PtrToOwnedKptr { .. } => {
            // Accept; field-presence validation against the kptr's BTF
            // struct is not yet plumbed — the variant doesn't carry
            // the underlying btf_id. `res_spin_lock_no_lock_kptr` is
            // the one corpus test affected.
            true
        }
        _ => ctx.fail_with_log(
            VerificationError::InvalidArgType { pc: ctx.pc, reg: ctx.reg },
            &format!(
                "[Verifier] pc {}: R{} bpf_res_spin_lock arg doesn't point to map value or allocated object (got {:?})",
                ctx.pc, ctx.arg_index + 1, ctx.actual
            ),
        ),
    }
}

fn validate_ptr_to_callback(ctx: &mut ValidationContext) -> bool {
    if !matches!(ctx.actual, RegType::PtrToCallback { .. }) {
        return ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_CALLBACK, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
    }
    true
}

/// ARG_PTR_TO_CONST_STR (kernel `verifier.c::check_reg_const_str`,
/// v6.15 ~L9405): the arg must be a `PtrToMapValue` whose map carries
/// `BPF_F_RDONLY_PROG` (i.e. `.rodata`). Used by `bpf_snprintf`'s fmt
/// arg. Note: kernel additionally validates the string content (NUL-
/// termination, format specifiers) but that's userspace-mutation-
/// dependent at load time and not modelable statically — see
/// `selftests/expectations.json` note on `test_snprintf_single`.
fn validate_ptr_to_const_str(ctx: &mut ValidationContext) -> bool {
    match ctx.actual {
        RegType::PtrToMapValue { map_idx, offset, .. } => {
            let map_def = ctx.env.ctx.map_defs.get(map_idx);
            let rdonly = map_def
                .map(|md| md.map_flags & constants::BPF_F_RDONLY_PROG != 0)
                .unwrap_or(false);
            if !rdonly {
                ctx.fail_with_log(
                    VerificationError::InvalidArgType {
                        pc: ctx.pc,
                        reg: ctx.reg,
                    },
                    &format!(
                        "[Verifier] pc {}: R{} does not point to a readonly map (ARG_PTR_TO_CONST_STR)",
                        ctx.pc,
                        ctx.arg_index + 1
                    ),
                );
                return false;
            }
            // Kernel ARG_PTR_TO_CONST_STR also requires NUL-termination
            // within the rodata map's bounds (check_mem_size_reg →
            // bpf_check_str_arg_size). Scan the rodata `initial_data`
            // from `offset` forward for a NUL byte. Closes
            // strncmp_test.c::strncmp_bad_not_null_term_target where
            // s2 = "12345678" (no NUL in 8 bytes of .rodata).
            //
            // We only enforce when we have a constant offset and the
            // map's `initial_data` is populated; otherwise (variable
            // offset, no data captured) fall back to the kernel-rdonly
            // check and accept — same shape as our existing leniency
            // around `MapValue` reads with variable offsets.
            if let (Some(off), Some(md)) = (offset, map_def)
                && let Some(data) = md.initial_data.as_ref()
                && off >= 0
            {
                let off = off as usize;
                if off >= data.len() || !data[off..].iter().any(|&b| b == 0) {
                    ctx.fail_with_log(
                        VerificationError::InvalidArgType {
                            pc: ctx.pc,
                            reg: ctx.reg,
                        },
                        &format!(
                            "[Verifier] pc {}: R{} const-string arg is not NUL-terminated within rodata bounds (offset {})",
                            ctx.pc,
                            ctx.arg_index + 1,
                            off
                        ),
                    );
                    return false;
                }
            }
            true
        }
        _ => {
            ctx.fail_with_log(
                VerificationError::InvalidArgType {
                    pc: ctx.pc,
                    reg: ctx.reg,
                },
                &format!(
                    "[Verifier] pc {}: R{} expected PTR_TO_CONST_STR, got {:?}",
                    ctx.pc,
                    ctx.arg_index + 1,
                    ctx.actual
                ),
            );
            false
        }
    }
}

fn validate_ptr_to_long(ctx: &mut ValidationContext) -> bool {
    match ctx.actual {
        RegType::PtrToStack { frame_level } => {
            let offset = ctx.state.domain.get_distance_fixed(ctx.reg, Reg::R10);
            check_stack_access(
                ctx.env,
                ctx.state,
                ctx.reg,
                offset,
                0,
                8, // PtrToLong is 8-byte access
                ctx.pc,
                AccessKind::HelperPrimitive,
                None,
                frame_level,
            );
            !ctx.env.failed()
        }
        // ARG_PTR_TO_LONG also accepts pointers into a writable map value
        // (rodata-backed maps are rejected via the BPF_F_RDONLY_PROG flag).
        RegType::PtrToMapValue { map_idx, .. } => {
            let writable = ctx
                .env
                .ctx
                .map_defs
                .get(map_idx)
                .map(|md| md.map_flags & constants::BPF_F_RDONLY_PROG == 0)
                .unwrap_or(false);
            if writable {
                true
            } else {
                ctx.env.fail(VerificationError::MapStoreForbidden {
                    pc: ctx.pc,
                    map_idx,
                });
                false
            }
        }
        _ => ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_LONG, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        ),
    }
}

// ============================================================================
// Memory Validation Helpers
// ============================================================================

/// Validates that a register points to readable memory.
pub(crate) fn validate_readable_mem(
    env: &mut VerifierEnv,
    state: &State,
    pc: usize,
    reg: Reg,
    reg_type: RegType,
    size: Option<u32>,
) -> bool {
    match reg_type {
        RegType::PtrToStack { .. } => {
            if let Some(off) = state.domain.get_distance_fixed(reg, Reg::R10) {
                if let Some(sz) = size {
                    check_stack_arg_readable(
                        env,
                        state,
                        off,
                        sz as i64,
                        pc,
                        AccessKind::HelperBuffer,
                    );
                }
                true
            } else {
                // Variable stack offset — use bounds check
                if let Some(sz) = size {
                    let (lo, hi) = state.domain.get_distance_interval(reg, Reg::R10);
                    if lo != i64::MIN && hi != i64::MAX {
                        // Check all possible offsets in the range
                        for off_candidate in lo..=hi {
                            check_stack_arg_readable(
                                env,
                                state,
                                off_candidate,
                                sz as i64,
                                pc,
                                AccessKind::HelperBuffer,
                            );
                            if env.failed() {
                                return false;
                            }
                        }
                        true
                    } else {
                        env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
                        false
                    }
                } else {
                    true
                }
            }
        }
        // Delegate the checking for these to access.rs
        RegType::PtrToMapValue { map_idx, .. } => {
            if let Some(size) = size {
                access::check_load(env, state, reg, size as i64, 0);
                if env.failed() {
                    return false;
                }
                true
            } else {
                check_map_rw(env, map_idx, pc, false);
                if env.failed() {
                    return false;
                }
                true
            }
        }
        RegType::PtrToPacket | RegType::PtrToPacketMeta => {
            if let Some(size) = size {
                access::check_load(env, state, reg, size as i64, 0);
                if env.failed() {
                    return false;
                }
                true
            } else {
                true
            }
        }
        RegType::PtrToCtx => {
            // Context can be read
            true
        }
        // Ring-buffer reservations (`bpf_ringbuf_reserve`) and arena
        // allocations carry their own bounds in `mem_size`. Kernel
        // accepts these as ARG_PTR_TO_MEM (mirrors `verifier_ringbuf::
        // passing_rb_mem_to_helpers`, which routes ringbuf-reserved
        // memory into bpf_fib_lookup's params arg).
        RegType::PtrToAllocMem { mem_size, .. } => {
            if let Some(sz) = size
                && sz as u64 > mem_size
            {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: alloc-mem {} bytes can't satisfy {}-byte read",
                    pc, mem_size, sz
                );
                return false;
            }
            true
        }
        RegType::PtrToArena { mem_size, .. } => {
            if let Some(sz) = size
                && sz as u64 > mem_size
            {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: arena-mem {} bytes can't satisfy {}-byte read",
                    pc, mem_size, sz
                );
                return false;
            }
            true
        }
        // Kernel `check_mem_access` admits PTR_TO_BTF_ID for ARG_PTR_TO_MEM
        // via PROBE_MEM (verifier.c v6.15 ~L7521): the helper reads bytes
        // from a kernel-struct pointer with fault-tolerant probing
        // (returns zero on page-fault). Permitted in tracing-class
        // contexts where probe_read semantics apply (tp_btf, fentry,
        // fexit, kprobe, raw_tp, lsm, perf_event, iter). Closes
        // task_kfunc_success::test_task_from_pid_invalid where
        // bpf_strncmp(task->comm, ...) hands a `task_struct + 1912`
        // pointer into ARG_PTR_TO_MEM.
        RegType::PtrToBtfId { .. } => {
            use crate::ast::ProgramKind;
            let probe_ok = matches!(
                env.ctx.prog_kind,
                ProgramKind::Tracing
                    | ProgramKind::Lsm
                    | ProgramKind::Kprobe
                    | ProgramKind::Tracepoint
                    | ProgramKind::RawTracepoint
                    | ProgramKind::RawTracepointWritable
                    | ProgramKind::PerfEvent
                    | ProgramKind::StructOps
            );
            if !probe_ok {
                env.fail(VerificationError::InvalidArgType { pc, reg });
                error!(
                    "[Verifier] pc {}: PtrToBtfId arg requires tracing-class context for PROBE_MEM",
                    pc
                );
                return false;
            }
            true
        }
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!("[Verifier] pc {}: {:?} not a valid memory pointer", pc, reg);
            false
        }
    }
}

/// Validates that a register points to writable memory.
pub(crate) fn validate_writable_mem(
    env: &mut VerifierEnv,
    state: &State,
    _types: &TypeState,
    pc: usize,
    reg: Reg,
    reg_type: RegType,
    size: Option<u32>,
) -> bool {
    match reg_type {
        RegType::PtrToStack { frame_level } => {
            if let Some(off) = state.domain.get_distance_fixed(reg, Reg::R10)
                && let Some(sz) = size
            {
                check_stack_access(
                    env,
                    state,
                    reg,
                    Some(off),
                    0,
                    sz as i64,
                    pc,
                    AccessKind::HelperBuffer,
                    None,
                    frame_level,
                );
            }
            true
        }
        RegType::PtrToMapValue {
            map_idx,
            offset: map_off,
            ..
        } => {
            let writable = env
                .ctx
                .map_defs
                .get(map_idx)
                .map(|md| md.map_flags & constants::BPF_F_RDONLY_PROG == 0)
                .unwrap_or(false);
            if !writable {
                env.fail(VerificationError::MapStoreForbidden { pc, map_idx });
                return false;
            }
            // "kptr cannot be accessed indirectly by helper": helper
            // write buffers must not overlap any kptr field. Reuses the
            // same overlap logic as direct stores.
            if let Some(map_def) = env.ctx.map_defs.get(map_idx)
                && let Some(sz) = size
            {
                check_kptr_field_access(
                    env,
                    state,
                    map_def,
                    map_idx,
                    reg,
                    map_off,
                    0,
                    sz as i64,
                    pc,
                    /*is_store=*/ true,
                );
                if env.failed() {
                    return false;
                }
            }
            true
        }
        RegType::PtrToPacket => {
            // Packet pointers are NOT valid for uninit_mem arguments
            // (helper would write to packet, which is not allowed this way)
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!(
                "[Verifier] pc {}: packet pointer not valid for output buffer",
                pc
            );
            false
        }
        RegType::PtrToPacketMeta => {
            // data_meta region IS writable via helpers/kfuncs (XDP only —
            // kernel's `xdp_metadata_rx_*` kfuncs write hash / rss_type /
            // vlan_tci into the meta region). Bounds-check the write size
            // against the meta-region range via the standard packet-meta
            // access check (mirrors the read path at L1470 added in
            // commit b0ac782).
            if let Some(size) = size {
                crate::analysis::transfer::memory::access::check_load(
                    env, state, reg, size as i64, 0,
                );
                if env.failed() {
                    return false;
                }
            }
            true
        }
        RegType::PtrToAllocMem { mem_size, .. } => {
            // Ringbuf-reserved (or kfunc bpf_obj_new) memory is writable.
            // Bound check: helper write-size must fit within remaining
            // bytes from this pointer's offset (mem_size already encodes
            // the post-offset remaining size after pointer arithmetic
            // through `update_ptr_arithmetic_type`).
            if let Some(sz) = size {
                if (sz as u64) > mem_size {
                    env.fail(VerificationError::InvalidArgType { pc, reg });
                    error!(
                        "[Verifier] pc {}: write size {} exceeds remaining alloc-mem size {}",
                        pc, sz, mem_size
                    );
                    return false;
                }
            }
            true
        }
        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg });
            error!(
                "[Verifier] pc {}: {:?} not a valid writable memory pointer",
                pc, reg
            );
            false
        }
    }
}

// ============================================================================
// Pointer-Size Pair Validation
// ============================================================================

/// Validates all pointer-size pairs declared on a call proto.
/// Returns true if all pairs are valid, false otherwise (error reported).
pub(crate) fn check_mem_size_pairs(
    env: &mut VerifierEnv,
    state: &State,
    proto: &CallProto,
    pc: usize,
) -> bool {
    for pair in proto.mem_size_pairs {
        if !check_single_mem_size_pair(env, proto, state, pair, pc) {
            return false;
        }
    }
    true
}

/// Validates a single pointer-size pair.
pub(crate) fn check_single_mem_size_pair(
    env: &mut VerifierEnv,
    proto: &CallProto,
    state: &State,
    pair: &super::signatures::MemSizePair,
    pc: usize,
) -> bool {
    let ptr_type = state.types.get(pair.ptr_reg);

    // Handle NULL pointer case
    if state.domain.proven_zero(pair.ptr_reg) {
        if pair.null_skips_size_check {
            // `__opt` semantics: NULL ptr means no buffer access, any
            // size is fine. Helper returns NULL on the slow path; caller
            // must null-check before deref.
            return true;
        }
        if pair.allow_zero {
            // NULL ptr is OK, but size must also be 0
            if !state.domain.proven_zero(pair.size_reg) {
                env.fail(VerificationError::InvalidArgType {
                    pc,
                    reg: pair.size_reg,
                });
                error!(
                    "[Verifier] pc {}: {:?} must be 0 when {:?} is NULL",
                    pc, pair.size_reg, pair.ptr_reg
                );
                return false;
            }
            return true;
        } else {
            // NULL not allowed for this pair
            env.fail(VerificationError::InvalidArgType {
                pc,
                reg: pair.ptr_reg,
            });
            error!("[Verifier] pc {}: {:?} cannot be NULL", pc, pair.ptr_reg);
            return false;
        }
    }

    // Get size bounds from DBM
    let (_, max_size) = state.domain.get_interval(pair.size_reg);
    if max_size == i64::MAX {
        // Size is unbounded - reject
        env.fail(VerificationError::InvalidArgType {
            pc,
            reg: pair.size_reg,
        });
        error!(
            "[Verifier] pc {}: {:?} has unbounded size",
            pc, pair.size_reg
        );
        return false;
    }

    // Size must be non-negative
    if !state.domain.proven_nonnegative(pair.size_reg) {
        env.fail(VerificationError::InvalidArgType {
            pc,
            reg: pair.size_reg,
        });
        error!(
            "[Verifier] pc {}: {:?} must be non-negative",
            pc, pair.size_reg
        );
        return false;
    }

    // Check zero size
    if max_size == 0 {
        if !pair.allow_zero {
            env.fail(VerificationError::InvalidArgType {
                pc,
                reg: pair.size_reg,
            });
            error!("[Verifier] pc {}: {:?} cannot be 0", pc, pair.size_reg);
            return false;
        }
        // Zero-size accesses are allowed by this helper, but the kernel
        // still validates that the *pointer itself* is within bounds —
        // a variable-offset stack pointer whose range escapes [-512, 0)
        // is rejected even when no byte is actually accessed
        // (`verifier_var_off::zero_sized_access_max_out_of_bound`).
        // Fall through to `check_ptr_access_size` with size=0 only for
        // pointer kinds where range validation makes sense at zero size;
        // unknown / non-memory pointers are not re-checked here.
        if matches!(ptr_type, RegType::PtrToStack { .. }) {
            let ptr_arg_type = proto.args.get(pair.ptr_reg.idx() - 2).unwrap();
            return check_ptr_access_size(
                env,
                state,
                pair.ptr_reg,
                ptr_type,
                *ptr_arg_type,
                0,
                pc,
            );
        }
        return true;
    }

    // Validate pointer can accommodate the access
    let ptr_arg_type = proto.args.get(pair.ptr_reg.idx() - 2).unwrap();
    check_ptr_access_size(
        env,
        state,
        pair.ptr_reg,
        ptr_type,
        *ptr_arg_type,
        max_size as u32,
        pc,
    )
}

pub(crate) fn checked_by_mem_size_pairs(pairs: &[MemSizePair], reg: Reg) -> bool {
    pairs.iter().any(|pair| pair.ptr_reg == reg)
}

/// Checks that a pointer can safely access `size` bytes.
pub(crate) fn check_ptr_access_size(
    env: &mut VerifierEnv,
    state: &State,
    ptr_reg: Reg,
    ptr_type: RegType,
    ptr_arg_type: ArgKind,
    size: u32,
    pc: usize,
) -> bool {
    match ptr_type {
        RegType::PtrToStack { frame_level } => {
            if let Some(off) = state.domain.get_distance_fixed(ptr_reg, Reg::R10) {
                // Stack: check [off, off + size) is within stack bounds
                // Stack grows down, so valid range is [-512, 0)
                let end_offset = off + size as i64;
                if off < -512 || end_offset > 0 {
                    env.fail(VerificationError::StackOutOfBounds {
                        pc,
                        off,
                        size: size.into(),
                    });
                    error!(
                        "[Verifier] pc {}: stack access [{}, {}) out of bounds",
                        pc, off, end_offset
                    );
                    return false;
                }
                // W3.2 / W4.2: helper buffer access (read or write) may
                // not overlap an active iter slot or dynptr body. The
                // initialization check below is skipped for PtrToUninitMem
                // (helper writes the bytes), so the opaque-body rule
                // needs its own gate here to catch e.g. probe_read_kernel
                // writing into an iter slot.
                if state
                    .stack_at(frame_level)
                    .access_overlaps_iterator(off, size as i64)
                    || state
                        .stack_at(frame_level)
                        .read_overlaps_dynptr(off, size as i64)
                {
                    env.fail(VerificationError::InvalidStackRead {
                        pc,
                        offset: off,
                    });
                    return false;
                }
                // Also check stack slots are initialized for reads
                if !matches!(
                    ptr_arg_type,
                    ArgKind::PtrToUninitMem | ArgKind::PtrToUninitMemOrNull
                ) {
                    check_stack_arg_readable(
                        env,
                        state,
                        off,
                        size as i64,
                        pc,
                        AccessKind::HelperBuffer,
                    );
                }
                !env.failed()
            } else {
                // Variable offset — use bounds for range check
                let (lo, hi) = state.domain.get_distance_interval(ptr_reg, Reg::R10);
                if lo != i64::MIN && hi != i64::MAX {
                    let end_offset = hi + size as i64;
                    if lo < -512 || end_offset > 0 {
                        env.fail(VerificationError::StackOutOfBounds {
                            pc,
                            off: lo,
                            size: size.into(),
                        });
                        return false;
                    }
                    if !matches!(
                    ptr_arg_type,
                    ArgKind::PtrToUninitMem | ArgKind::PtrToUninitMemOrNull
                ) {
                        for off_candidate in lo..=hi {
                            check_stack_arg_readable(
                                env,
                                state,
                                off_candidate,
                                size as i64,
                                pc,
                                AccessKind::HelperBuffer,
                            );
                            if env.failed() {
                                return false;
                            }
                        }
                    }
                    true
                } else {
                    env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
                    error!(
                        "[Verifier] pc {}: {:?} has unknown stack offset",
                        pc, ptr_reg
                    );
                    false
                }
            }
        }

        RegType::PtrToMapValue {
            map_idx,
            offset,
            id: _,
            ..
        } => {
            // Map value: check offset + size <= value_size
            let Some(map_def) = env.ctx.map_defs.get(map_idx) else {
                env.fail(VerificationError::MapNotFound { pc, map_idx });
                return false;
            };

            // "kptr cannot be accessed indirectly by helper": helper
            // mem-buffer args (the size comes from the paired size arg)
            // must not overlap a kptr field.
            check_kptr_field_access(
                env,
                state,
                map_def,
                map_idx,
                ptr_reg,
                offset,
                0,
                size as i64,
                pc,
                /*is_store=*/ true,
            );
            if env.failed() {
                return false;
            }
            check_map_access(
                env,
                state,
                map_def.value_size as i64,
                offset,
                map_idx,
                ptr_reg,
                map_def,
                0,
                size as i64,
                pc,
            );
            !env.failed()
        }

        RegType::PtrToPacket => {
            // Packet: need to verify against packet bounds (data_end - data)
            check_packet_access(
                env,
                state,
                ptr_reg,
                0,
                size as i64,
                pc,
                AccessKind::HelperBuffer,
            );
            !env.failed()
        }

        // Ring-buffer reservations / arena allocations / dynptr-slice
        // results carry their own bounds in `mem_size`. Kernel accepts
        // these as ARG_PTR_TO_MEM (mirrors `validate_readable_mem`'s
        // PtrToAllocMem arm). Without this, bpf_strncmp(slice_result, ...)
        // — where slice_result has RetKind::PtrToAllocMemFromArg — falls
        // through to the catch-all reject because mem_size_pair validation
        // routes through `check_ptr_access_size`, not `validate_readable_mem`.
        RegType::PtrToAllocMem { mem_size, .. } => {
            if size as u64 > mem_size {
                env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
                error!(
                    "[Verifier] pc {}: alloc-mem {} bytes can't satisfy {}-byte access",
                    pc, mem_size, size
                );
                return false;
            }
            true
        }

        // Kernel admits PTR_TO_BTF_ID for ARG_PTR_TO_MEM via PROBE_MEM
        // (see validate_readable_mem PtrToBtfId arm). Same gating: only
        // tracing-class contexts where probe_read semantics apply.
        // Closes task_kfunc_success::test_task_from_pid_invalid where
        // bpf_strncmp(task->comm, ...) routes through MemSizePair.
        RegType::PtrToBtfId { .. } => {
            use crate::ast::ProgramKind;
            let probe_ok = matches!(
                env.ctx.prog_kind,
                ProgramKind::Tracing
                    | ProgramKind::Lsm
                    | ProgramKind::Kprobe
                    | ProgramKind::Tracepoint
                    | ProgramKind::RawTracepoint
                    | ProgramKind::RawTracepointWritable
                    | ProgramKind::PerfEvent
                    | ProgramKind::StructOps
            );
            if !probe_ok {
                env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
                error!(
                    "[Verifier] pc {}: PtrToBtfId arg requires tracing-class context for PROBE_MEM",
                    pc
                );
                return false;
            }
            true
        }

        _ => {
            env.fail(VerificationError::InvalidArgType { pc, reg: ptr_reg });
            error!(
                "[Verifier] pc {}: {:?} ({:?}) not a valid memory pointer",
                pc, ptr_reg, ptr_type
            );
            false
        }
    }
}

/// Check if a helper ID is valid (within known range).
pub(crate) fn is_valid_helper_id(id: u32) -> bool {
    id <= constants::BPF_HELPER_MAX
}
