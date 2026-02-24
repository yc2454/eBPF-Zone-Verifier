// src/analysis/transfer/call/validators/memory.rs
//
// Validators for memory-related argument types: PtrToMem, PtrToUninitMem, PtrToAllocMem

use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg_types::RegType;

use super::super::checks::{
    ValidationContext, checked_by_mem_size_pairs, validate_readable_mem, validate_writable_mem,
};
use super::super::signatures::helper_rejects_packet_for_arg;

/// Validates PtrToMem argument type.
/// A PtrToMem is a pointer to valid, readable memory (stack, packet, map value).
pub fn validate_ptr_to_mem(ctx: &mut ValidationContext) -> bool {
    let actual = ctx.actual;

    // If this pointer is checked by a mem-size pair, defer to that check
    if checked_by_mem_size_pairs(ctx.helper, ctx.reg) {
        return true;
    }

    // Some helpers reject packet pointers for specific args
    if matches!(actual, RegType::PtrToPacket)
        && helper_rejects_packet_for_arg(ctx.helper, ctx.arg_index)
    {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: helper {} does not accept packet pointer for R{}",
                ctx.pc,
                ctx.helper,
                ctx.arg_index + 1
            ),
        );
        return false;
    }

    validate_readable_mem(ctx.env, ctx.state, ctx.pc, ctx.reg, actual, None)
}

/// Validates PtrToUninitMem argument type.
/// A PtrToUninitMem is a pointer to writable memory (helper will fill it).
pub fn validate_ptr_to_uninit_mem(ctx: &mut ValidationContext) -> bool {
    validate_writable_mem(
        ctx.env, ctx.state, ctx.types, ctx.pc, ctx.reg, ctx.actual, None,
    )
}

/// Validates PtrToAllocMem argument type.
/// Must be a dynamically allocated memory pointer (e.g., from bpf_ringbuf_reserve).
pub fn validate_ptr_to_alloc_mem(ctx: &mut ValidationContext) -> bool {
    if !matches!(ctx.actual, RegType::PtrToAllocMem { .. }) {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected PTR_TO_ALLOC_MEM, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                ctx.actual
            ),
        );
        return false;
    }
    true
}
