// src/analysis/transfer/memory/stack.rs

use super::access::AccessKind;
use crate::analysis::machine::env::{VerificationError, VerifierEnv};
use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::stack_state::StackState;
use crate::analysis::machine::state::State;
use crate::common::constants;
use crate::zone::domain::get_distance_interval;
use log::error;

/// Check if a stack access at (base + off) of size bytes is safe.
/// For reads, also checks that the memory is initialized.
pub fn check_stack_access(
    env: &mut VerifierEnv,
    state: &State,
    base: Reg,
    ptr_type_offset: Option<i64>,
    instruction_offset: i64,
    size: i64,
    pc: usize,
    kind: AccessKind,
    src_type_op: Option<RegType>,
    pointer_frame_lv: FrameLevel,
) {
    if state.current_frame_level() > pointer_frame_lv {
        if matches!(kind, AccessKind::Write) && src_type_op.is_some() {
            if let Some(ty) = src_type_op {
                if matches!(ty, RegType::PtrToStack { .. }) {
                    env.fail(VerificationError::SpillToCaller { pc });
                    return;
                }
            }
        }
    }
    let current_frame_depth = -(state.total_stack_depth() as i64);
    let stack_being_accessed = state.stack_at(pointer_frame_lv);

    match ptr_type_offset {
        Some(base_off) => {
            let actual_offset = base_off + instruction_offset;
            let access_end = current_frame_depth + actual_offset + size;

            if !matches!(kind, AccessKind::HelperArg) && actual_offset % size != 0 {
                env.fail(VerificationError::MisalignedAccess {
                    pc,
                    off: actual_offset,
                });
                return;
            }

            if actual_offset < constants::BPF_STACK_MIN || access_end > constants::BPF_STACK_MAX {
                error!(target: "app", "Stack access out of bounds at pc {}: off {} size {} (Known offset)", pc, actual_offset, size);
                env.fail(VerificationError::StackOutOfBounds {
                    pc,
                    off: actual_offset,
                    size,
                });
                return;
            }

            check_stack_initialization(env, stack_being_accessed, kind, actual_offset, size, pc);
        }
        None => {
            let (lo, hi) = get_distance_interval(&state.dbm, base, Reg::R10);

            let safe = match (lo, hi) {
                (Some(lower), Some(upper)) => {
                    let min_offset = lower + instruction_offset;
                    let max_access_end =
                        current_frame_depth as i64 + upper + instruction_offset + size;
                    min_offset >= constants::BPF_STACK_MIN
                        && max_access_end <= constants::BPF_STACK_MAX
                }
                _ => false,
            };

            if !safe {
                error!(target: "app", "Stack access out of bounds at pc {}: off {} size {} (Unknown offset)", pc, instruction_offset, size);
                env.fail(VerificationError::StackOutOfBounds {
                    pc,
                    off: instruction_offset,
                    size,
                });
                return;
            }

            match (lo, hi) {
                (Some(lower), Some(upper)) => {
                    for off_candidate in lower..=upper {
                        let actual_offset = off_candidate + instruction_offset;
                        check_stack_initialization(
                            env,
                            stack_being_accessed,
                            kind,
                            actual_offset,
                            size,
                            pc,
                        );
                    }
                }
                _ => {
                    env.fail(VerificationError::UninitializedStackRead { pc, offset: 0 });
                }
            }
        }
    }
}

pub(crate) fn check_stack_initialization(
    env: &mut VerifierEnv,
    stack: &StackState,
    kind: AccessKind,
    actual_offset: i64,
    size: i64,
    pc: usize,
) {
    let allow_privileged_upper_half_read = |off: i64, sz: i64| -> bool {
        if !env.ctx.is_privileged() || sz != 4 {
            return false;
        }
        if off < i16::MIN as i64 || off > i16::MAX as i64 {
            return false;
        }
        let off = off as i16;
        if off.rem_euclid(8) != 4 {
            return false;
        }
        for i in 0..4 {
            if !stack.is_slot_initialized(off - 4 + i as i16) {
                return false;
            }
        }
        true
    };

    let allow_privileged_partial_u64_read = |off: i64, sz: i64| -> bool {
        if !env.ctx.is_privileged() || sz != 8 {
            return false;
        }
        if off < i16::MIN as i64 || off > i16::MAX as i64 {
            return false;
        }
        let off = off as i16;
        stack.is_slot_initialized(off)
    };

    match kind {
        AccessKind::Read => {
            let mut first_uninit: Option<i16> = None;
            for i in 0..size {
                let slot = (actual_offset + i) as i16;
                if !stack.is_slot_initialized(slot) {
                    first_uninit = Some(slot);
                    break;
                }
            }

            if first_uninit.is_some() {
                if allow_privileged_upper_half_read(actual_offset, size)
                    || allow_privileged_partial_u64_read(actual_offset, size)
                {
                    return;
                }
                env.fail(VerificationError::UninitializedStackRead {
                    pc,
                    offset: actual_offset,
                });
                return;
            }

            for i in 0..size {
                let slot = (actual_offset + i) as i16;
                let slot_type = stack.get_slot_type(slot);
                if slot_type.is_pointer() && size != 8 {
                    error!(target: "app", "Pointer read with invalid size at pc {}: off {} size {}", pc, actual_offset, size);
                    env.fail(VerificationError::InvalidStackRead {
                        pc,
                        offset: actual_offset,
                    });
                }
            }
        }
        AccessKind::HelperOutput | AccessKind::HelperArg => {
            let any_initialized =
                (0..size).any(|i| stack.is_slot_initialized((actual_offset + i) as i16));

            if !any_initialized {
                env.fail(VerificationError::UninitializedStackRead {
                    pc,
                    offset: actual_offset,
                });
                return;
            }
        }
        AccessKind::Write => {}
    }
}

pub fn check_stack_arg_readable(
    env: &mut VerifierEnv,
    state: &State,
    stack_offset: i64,
    size: i64,
    pc: usize,
    kind: AccessKind,
) {
    check_stack_access(
        env,
        state,
        Reg::R10,
        Some(stack_offset),
        0,
        size,
        pc,
        kind,
        None,
        state.current_frame_level(),
    )
}
