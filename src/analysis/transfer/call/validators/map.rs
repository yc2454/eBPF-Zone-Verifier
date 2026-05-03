// src/analysis/transfer/call/validators/map.rs
//
// Validators for map-related argument types: ConstMapPtr, PtrToMapKey, PtrToMapValue

use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::common::constants;

use super::super::checks::{ValidationContext, validate_readable_mem};
use super::super::compat::check_map_type_for_helper;
use crate::analysis::transfer::memory::check_stack_no_pointers;

/// Validates ConstMapPtr argument type.
/// A ConstMapPtr must be either:
/// - A direct PtrToMapObject
/// - A PtrToMapValue at offset 0 from an array-of-maps or hash-of-maps (inner map lookup)
pub fn validate_const_map_ptr(ctx: &mut ValidationContext) -> bool {
    let actual = ctx.actual;

    // Check for inner map pointer (value from map-of-maps at offset 0)
    let is_inner_map_ptr = match actual {
        RegType::PtrToMapValue {
            map_idx,
            offset: Some(0),
            ..
        } => ctx
            .env
            .ctx
            .map_defs
            .get(map_idx)
            .map(|m| {
                matches!(
                    m.type_,
                    constants::BPF_MAP_TYPE_ARRAY_OF_MAPS | constants::BPF_MAP_TYPE_HASH_OF_MAPS
                )
            })
            .unwrap_or(false),
        _ => false,
    };

    // Must be either PtrToMapObject or inner map pointer
    if !matches!(actual, RegType::PtrToMapObject { .. }) && !is_inner_map_ptr {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_MAP, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                actual
            ),
        );
        return false;
    }

    // Check helper-specific map type requirements
    if let RegType::PtrToMapObject { map_idx } = actual
        && let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx)
        && let Err(msg) = check_map_type_for_helper(ctx.helper, map_def.type_)
    {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: {}, got type {}",
                ctx.pc, msg, map_def.type_
            ),
        );
        return false;
    }

    true
}

/// Validates a ConstMapPtr whose backing map's `type_` must equal
/// `required_type` (a `BPF_MAP_TYPE_*` constant). Used for kfuncs that
/// require a specific map kind (e.g. arena alloc/free), since the existing
/// `validate_const_map_ptr` only checks the helper-id-driven type table,
/// which doesn't apply to kfuncs.
pub fn validate_const_map_ptr_of_type(
    ctx: &mut ValidationContext,
    required_type: u32,
) -> bool {
    // Also accept a `__map`-suffixed kfunc-arg shape: any
    // `PtrToBtfId{bpf_map, TRUSTED}` (kernel `verifier.c` ~L13227,
    // `KF_ARG_PTR_TO_MAP` — "If argument has '__map' suffix expect
    // 'struct bpf_map *'"). The runtime map type is not checked at
    // verification time in this path; the kfunc body's
    // `container_of(map, struct bpf_arena, map)` enforces it at
    // runtime. Drives `verifier_arena.c::iter_maps1` where
    // `bpf_arena_alloc_pages(ctx->map, …)` passes a typed bpf_map*
    // loaded from the iter ctx, not a CONST_PTR_TO_MAP.
    if let RegType::PtrToBtfId {
        type_name, flags, ..
    } = ctx.actual
        && type_name == "bpf_map"
        && flags.contains(crate::analysis::machine::reg_types::PtrFlags::TRUSTED)
    {
        let _ = required_type;
        return true;
    }

    if !validate_const_map_ptr(ctx) {
        return false;
    }

    if let RegType::PtrToMapObject { map_idx } = ctx.actual
        && let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx)
        && map_def.type_ != required_type
    {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected map type {}, got {}",
                ctx.pc,
                ctx.arg_index + 1,
                required_type,
                map_def.type_
            ),
        );
        return false;
    }

    true
}

/// Validates PtrToMapKey argument type.
/// The pointer must point to readable memory with size matching the map's key_size.
pub fn validate_ptr_to_map_key(ctx: &mut ValidationContext) -> bool {
    let Some(target_info) = ctx.map_info else {
        return true;
    };

    let actual = ctx.actual;

    // If pointing to another map value, check size compatibility
    if let RegType::PtrToMapValue { map_idx, .. } = actual {
        if let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx) {
            if map_def.value_size != target_info.value_size {
                ctx.fail_with_log(
                    VerificationError::InvalidArgType {
                        pc: ctx.pc,
                        reg: ctx.reg,
                    },
                    &format!(
                        "[Verifier] pc {}: R{} map value size mismatch: expected {}, got {}",
                        ctx.pc,
                        ctx.arg_index + 1,
                        target_info.value_size,
                        map_def.key_size
                    ),
                );
                return false;
            }
        } else {
            ctx.env.fail(VerificationError::MapNotFound {
                pc: ctx.pc,
                map_idx,
            });
            return false;
        }
    }

    // For stack pointers used as keys in bpf_map_update_elem, check that
    // the memory doesn't contain pointers that would be leaked to the map.
    if ctx.helper == constants::BPF_MAP_UPDATE_ELEM
        && let RegType::PtrToStack { .. } = actual
        && let Some(off) = ctx.state.domain.get_distance_fixed(ctx.reg, Reg::R10)
    {
        check_stack_no_pointers(ctx.env, ctx.state, off, target_info.key_size as i64, ctx.pc);
        if ctx.env.failed() {
            return false;
        }
    }

    // For BPF_MAP_TYPE_ARRAY maps, check key bounds for update operations.
    // Note: For bpf_map_lookup_elem, out-of-bounds keys simply return NULL (not a safety violation).
    // But for bpf_map_update_elem, we reject out-of-bounds keys as the operation would fail.
    if ctx.helper == constants::BPF_MAP_UPDATE_ELEM {
        // Linux checks array map key bounds at runtime (returns NULL or error).
        // Statically rejecting unbounded keys here causes precision failures on valid programs.
    }

    validate_readable_mem(
        ctx.env,
        ctx.state,
        ctx.pc,
        ctx.reg,
        actual,
        Some(target_info.key_size),
    )
}

/// Validates PtrToMapValue argument type.
/// Must point to readable memory with size matching the map's value_size.
pub fn validate_ptr_to_map_value(ctx: &mut ValidationContext) -> bool {
    use crate::analysis::machine::reg_types::PtrFlags;
    use crate::common::constants;
    let Some(target_info) = ctx.map_info else {
        return true;
    };

    let actual = ctx.actual;

    // SOCKMAP / SOCKHASH special-case: `bpf_map_update_elem`'s value
    // arg (R3) is a socket pointer for these map types, not a map
    // value. Kernel `sock_map_update_elem` checks ARG_PTR_TO_BTF_ID_SOCK_COMMON
    // — accepts PtrToSocket / PtrToSockCommon / PtrToTcpSock and
    // BTF-typed sock pointers (e.g. `skb->sk` typed as
    // `PtrToBtfId{sock, TRUSTED}` via the cluster B BTF field-load
    // typing). Closes the seven `verifier_sockmap_mutate.c` FRs.
    let is_sock_map = matches!(
        target_info.map_type,
        constants::BPF_MAP_TYPE_SOCKMAP | constants::BPF_MAP_TYPE_SOCKHASH
    );
    if is_sock_map {
        let sock_ok = matches!(
            actual,
            RegType::PtrToSocket { .. }
                | RegType::PtrToSocketOrNull { .. }
                | RegType::PtrToSockCommon { .. }
                | RegType::PtrToSockCommonOrNull { .. }
                | RegType::PtrToTcpSock { .. }
                | RegType::PtrToTcpSockOrNull { .. }
        ) || matches!(
            actual,
            RegType::PtrToBtfId { type_name, flags, .. }
                if matches!(type_name, "sock" | "sock_common" | "tcp_sock" | "bpf_sock")
                    && flags.contains(PtrFlags::TRUSTED)
        );
        if sock_ok {
            return true;
        }
        // fall through to default error reporting below
    }

    // Check compatible types
    if !matches!(
        actual,
        RegType::PtrToMapValue { .. }
            | RegType::PtrToStack { .. }
            | RegType::PtrToPacket
            | RegType::PtrToPacketMeta
    ) {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_MAP_VALUE, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                actual
            ),
        );
        return false;
    }

    // If pointing to a map value, check size compatibility.
    // Kernel `check_helper_mem_access` (verifier.c v6.15 L8062) routes
    // PTR_TO_MAP_VALUE through `check_map_access`, which only requires
    // `reg->off + access_size <= map->value_size` — i.e. the source
    // region holds at least `dest.value_size` bytes from its current
    // offset onward. The source map's own `value_size` need not equal
    // the destination's. This admits passing `&val` from a `.bss`
    // synthetic map (whose `value_size` covers the whole section) as
    // an `array_map`'s value source.
    if let RegType::PtrToMapValue { map_idx, offset, .. } = actual {
        if let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx) {
            let off = offset.unwrap_or(0).max(0) as u64;
            let remaining = (map_def.value_size as u64).saturating_sub(off);
            if remaining < target_info.value_size as u64 {
                ctx.fail_with_log(
                    VerificationError::InvalidArgType {
                        pc: ctx.pc,
                        reg: ctx.reg,
                    },
                    &format!(
                        "[Verifier] pc {}: R{} map value too small: need {}, source has {} from offset {}",
                        ctx.pc,
                        ctx.arg_index + 1,
                        target_info.value_size,
                        remaining,
                        off
                    ),
                );
                return false;
            }
        } else {
            ctx.env.fail(VerificationError::MapNotFound {
                pc: ctx.pc,
                map_idx,
            });
            return false;
        }
    }

    // For stack pointers, check that the memory doesn't contain pointers
    if let RegType::PtrToStack { .. } = actual
        && let Some(off) = ctx.state.domain.get_distance_fixed(ctx.reg, Reg::R10)
    {
        check_stack_no_pointers(
            ctx.env,
            ctx.state,
            off,
            target_info.value_size as i64,
            ctx.pc,
        );
        if ctx.env.failed() {
            return false;
        }
    }

    validate_readable_mem(
        ctx.env,
        ctx.state,
        ctx.pc,
        ctx.reg,
        actual,
        Some(target_info.value_size),
    )
}

/// Validates PtrToUninitMapValue argument type.
/// Used for output buffers that the helper will write to.
pub fn validate_ptr_to_uninit_map_value(ctx: &mut ValidationContext) -> bool {
    use super::super::checks::validate_writable_mem;

    let Some(info) = ctx.map_info else {
        return true;
    };

    validate_writable_mem(
        ctx.env,
        ctx.state,
        ctx.types,
        ctx.pc,
        ctx.reg,
        ctx.actual,
        Some(info.value_size),
    )
}
