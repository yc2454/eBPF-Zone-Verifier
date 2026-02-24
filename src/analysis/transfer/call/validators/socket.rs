// src/analysis/transfer/call/validators/socket.rs
//
// Validators for socket-related argument types: PtrToSocket, PtrToSockCommon, PtrToBTFIdSockCommon

use crate::analysis::machine::error::VerificationError;

use super::super::checks::ValidationContext;
use super::super::compat::{
    BTF_SOCK_COMMON_COMPAT, SOCK_COMMON_COMPAT, SOCKET_COMPAT, is_compatible,
};
use super::super::signatures::BpfArgType;

/// Validates socket-related argument types.
/// Handles PtrToSocket, PtrToSockCommon, and PtrToBTFIdSockCommon.
pub fn validate_socket_arg(ctx: &mut ValidationContext, expected: BpfArgType) -> bool {
    let actual = &ctx.actual;

    let (compat_table, type_name) = match expected {
        BpfArgType::PtrToSocket => (SOCKET_COMPAT, "PTR_TO_SOCKET"),
        BpfArgType::PtrToSockCommon => (SOCK_COMMON_COMPAT, "PTR_TO_SOCK_COMMON"),
        BpfArgType::PtrToBTFIdSockCommon => (BTF_SOCK_COMMON_COMPAT, "PTR_TO_BTF_ID_SOCK_COMMON"),
        _ => {
            // Should not happen if called correctly
            return true;
        }
    };

    if !is_compatible(actual, compat_table) {
        ctx.fail_with_log(
            VerificationError::InvalidArgType {
                pc: ctx.pc,
                reg: ctx.reg,
            },
            &format!(
                "[Verifier] pc {}: R{} expected {}, got {:?}",
                ctx.pc,
                ctx.arg_index + 1,
                type_name,
                actual
            ),
        );
        return false;
    }

    true
}
