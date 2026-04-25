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
    check_map_access, check_map_rw, check_packet_access, check_stack_access,
    check_stack_arg_readable,
};
use crate::common::constants;
use log::{error, info, warn};

use super::compat::is_nullable_arg_type;
use super::signatures::{ArgKind, CallProto, MemSizePair, get_helper_proto};
use super::validators;

// ============================================================================
// MapInfo
// ============================================================================

/// Information about a BPF map needed for validation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct MapInfo {
    pub(crate) key_size: u32,
    pub(crate) value_size: u32,
}

pub(crate) fn get_map_info(map_type: RegType, env: &VerifierEnv) -> Option<MapInfo> {
    match map_type {
        RegType::PtrToMapObject { map_idx } => env.ctx.map_defs.get(map_idx).map(|md| MapInfo {
            key_size: md.key_size,
            value_size: md.value_size,
        }),
        RegType::PtrToMapValue { map_idx, .. } => env.ctx.map_defs.get(map_idx).and_then(|md| {
            if let Some(inner) = md.inner_map_idx {
                env.ctx.map_defs.get(inner).map(|inner_md| MapInfo {
                    key_size: inner_md.key_size,
                    value_size: inner_md.value_size,
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
    let map_info = if sig.args[0] == ArgKind::ConstMapPtr {
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
        ArgKind::PtrToMapKey => validators::validate_ptr_to_map_key(&mut ctx),
        ArgKind::PtrToMapValue => validators::validate_ptr_to_map_value(&mut ctx),
        ArgKind::PtrToUninitMapValue => {
            validators::map::validate_ptr_to_uninit_map_value(&mut ctx)
        }

        // ---- Memory types ----
        ArgKind::PtrToMem => validators::validate_ptr_to_mem(&mut ctx),
        ArgKind::PtrToUninitMem => validators::validate_ptr_to_uninit_mem(&mut ctx),
        ArgKind::PtrToAllocMem => validators::validate_ptr_to_alloc_mem(&mut ctx),

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
        ArgKind::PtrToStack => validate_ptr_to_stack(&mut ctx),
        ArgKind::PtrToLong => validate_ptr_to_long(&mut ctx),
        ArgKind::PtrToCallback => validate_ptr_to_callback(&mut ctx),

        // ---- Dynptr (W4.2c) ----
        ArgKind::DynptrArg { uninit, rdwr_only } => {
            validate_dynptr_arg(&mut ctx, uninit, rdwr_only)
        }

        // ---- Anything (just needs to be readable) ----
        ArgKind::Anything => true,

        // Nullable variants are handled above
        ArgKind::PtrToCtxOrNull
        | ArgKind::PtrToMemOrNull
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
    if !matches!(ctx.actual, RegType::PtrToCtx) {
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
    if !matches!(ctx.actual, RegType::PtrToBtfId { .. }) {
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
        if base.is_some() || trail.is_some() {
            return ctx.fail_with_log(
                VerificationError::InvalidArgType {
                    pc: ctx.pc,
                    reg: ctx.reg,
                },
                &format!(
                    "[Verifier] pc {}: R{} dynptr ctor target already initialized",
                    ctx.pc,
                    ctx.arg_index + 1
                ),
            );
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

fn validate_ptr_to_long(ctx: &mut ValidationContext) -> bool {
    if let RegType::PtrToStack { frame_level } = ctx.actual {
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
    } else {
        ctx.fail_with_log(
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
        )
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
        RegType::PtrToPacket => {
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
        RegType::PtrToMapValue { map_idx, .. } => {
            let writable = env
                .ctx
                .map_defs
                .get(map_idx)
                .map(|md| md.map_flags != constants::BPF_F_RDONLY_PROG)
                .unwrap_or(false);
            if writable {
                true
            } else {
                env.fail(VerificationError::MapStoreForbidden { pc, map_idx });
                false
            }
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
        if pair.allow_zero {
            return true;
        } else {
            env.fail(VerificationError::InvalidArgType {
                pc,
                reg: pair.size_reg,
            });
            error!("[Verifier] pc {}: {:?} cannot be 0", pc, pair.size_reg);
            return false;
        }
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
        RegType::PtrToStack { .. } => {
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
                // Also check stack slots are initialized for reads
                if !matches!(ptr_arg_type, ArgKind::PtrToUninitMem) {
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
                    if !matches!(ptr_arg_type, ArgKind::PtrToUninitMem) {
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
        } => {
            // Map value: check offset + size <= value_size
            let Some(map_def) = env.ctx.map_defs.get(map_idx) else {
                env.fail(VerificationError::MapNotFound { pc, map_idx });
                return false;
            };

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
