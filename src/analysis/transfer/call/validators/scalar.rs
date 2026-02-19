// src/analysis/transfer/call/validators/scalar.rs
//
// Validators for scalar argument types: ConstSize, ConstSizeOrZero, ConstAllocSizeOrZero

use crate::analysis::machine::env::VerificationError;
use crate::zone::domain::{proven_nonnegative, proven_positive};

use super::super::checks::ValidationContext;

/// Validates ConstSize argument type.
/// Value must be positive (> 0).
pub fn validate_const_size(ctx: &mut ValidationContext) -> bool {
    if !proven_positive(&ctx.state.dbm, ctx.reg) {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} (ConstSize) must be positive",
                ctx.pc,
                ctx.arg_index + 1
            ),
        );
        return false;
    }
    true
}

/// Validates ConstSizeOrZero or ConstAllocSizeOrZero argument type.
/// Value must be non-negative (>= 0).
pub fn validate_const_size_or_zero(ctx: &mut ValidationContext) -> bool {
    if !proven_nonnegative(&ctx.state.dbm, ctx.reg) {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} (ConstSizeOrZero) must be non-negative",
                ctx.pc,
                ctx.arg_index + 1
            ),
        );
        return false;
    }
    true
}
