// src/analysis/transfer/call/validators/map.rs
//
// Validators for map-related argument types: ConstMapPtr, PtrToMapKey, PtrToMapValue

use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::common::constants;
use crate::zone::domain::get_distance_fixed;

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
    if let RegType::PtrToMapObject { map_idx } = actual {
        if let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx) {
            if let Err(msg) = check_map_type_for_helper(ctx.helper, map_def.type_) {
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
        }
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
    if ctx.helper == constants::BPF_MAP_UPDATE_ELEM {
        if let RegType::PtrToStack { .. } = actual {
            if let Some(off) = get_distance_fixed(&ctx.state.dbm, ctx.reg, Reg::R10) {
                check_stack_no_pointers(
                    ctx.env,
                    ctx.state,
                    off,
                    target_info.key_size as i64,
                    ctx.pc,
                );
                if ctx.env.failed() {
                    return false;
                }
            }
        }
    }

    // For BPF_MAP_TYPE_ARRAY maps, check key bounds for update operations.
    // Note: For bpf_map_lookup_elem, out-of-bounds keys simply return NULL (not a safety violation).
    // But for bpf_map_update_elem, we reject out-of-bounds keys as the operation would fail.
    if ctx.helper == constants::BPF_MAP_UPDATE_ELEM {
        if let Some(RegType::PtrToMapObject { map_idx }) = ctx.types.get(Reg::R1).into() {
            if let Some(map_def) = ctx.env.ctx.map_defs.get(map_idx) {
                if map_def.type_ == constants::BPF_MAP_TYPE_ARRAY {
                    if let RegType::PtrToStack { .. } = actual {
                        if let Some(off) = get_distance_fixed(&ctx.state.dbm, ctx.reg, Reg::R10) {
                            let stack = ctx.state.stack_at(ctx.state.current_frame_level());
                            if let Some(spilled) = stack.get_slot(off as i16) {
                                // If the spilled key is fully initialized, check bounds against max_entries
                                if spilled.size.bytes() as u32 == map_def.key_size {
                                    let key_min = spilled.bounds.min;

                                    // BPF keys are unsigned 32-bit (for array)
                                    // Reject if statically known to be out of bounds
                                    if key_min < 0 || key_min >= map_def.max_entries as i64 {
                                        ctx.env.fail(VerificationError::MapKeyOutOfBounds {
                                            pc: ctx.pc,
                                            key_min,
                                            key_max: spilled.bounds.max,
                                            max_entries: map_def.max_entries,
                                        });
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
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
    let Some(target_info) = ctx.map_info else {
        return true;
    };

    let actual = ctx.actual;

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

    // If pointing to a map value, check size compatibility
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
                        map_def.value_size
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
    if let RegType::PtrToStack { .. } = actual {
        if let Some(off) = get_distance_fixed(&ctx.state.dbm, ctx.reg, Reg::R10) {
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
