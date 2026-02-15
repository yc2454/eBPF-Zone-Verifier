// src/analysis/transfer/alu/validation.rs

use crate::analysis::machine::env::{VerifierEnv};
use crate::analysis::machine::state::State;
use crate::analysis::machine::reg_types::{RegType};
use crate::ast::{AluOp, Operand, Width};
use crate::zone::domain::{Reg, get_bounds, is_zero};
use crate::zone::dbm::{INF, Dbm};
use crate::common::constants;
use log::error;

/// Pure validation of pointer arithmetic rules.
/// Returns true if the operation is legal.
pub(crate) fn check_ptr_arithmetic(
    env: &mut VerifierEnv,
    state: &State,
    op: AluOp,
    width: Width,
    dst: Reg,
    dst_type: &RegType,
    src_type: &RegType,
    src: &Operand
) -> bool {
    let dst_is_ptr = dst_type.is_pointer();
    let src_is_ptr = src_type.is_pointer();

    let src_max = match src {
        Operand::Imm(k) => *k,
        Operand::Reg(r) => {
            let (_, max_opt) = get_bounds(&state.dbm, *r);
            match max_opt {
                Some(max) => max,
                None => INF,
            }
        }
    };

    let src_min = match src {
        Operand::Imm(k) => *k,
        Operand::Reg(r) => {
            let (min_opt, _) = get_bounds(&state.dbm, *r);
            match min_opt {
                Some(min) => min,
                None => -INF,
            }
        }
    };

    let (dst_min, dst_max) = get_bounds(&state.dbm, dst);
    let dst_min = dst_min.unwrap_or(-INF);
    let dst_max = dst_max.unwrap_or(INF);

    // 1. Scalar <op> Scalar
    if !dst_is_ptr && !src_is_ptr {
        return true;
    }

    // 2. Pointer <op> Pointer
    if dst_is_ptr && src_is_ptr {
        match op {
            AluOp::Sub => {
                if env.ctx.is_privileged() {
                    return true;
                }
                RegType::is_same_pointer_type(dst_type, src_type) || 
                (matches!(dst_type, RegType::PtrToPacketEnd) && matches!(src_type, RegType::PtrToPacket { .. }))
            },
            AluOp::Mov => true,
            _ => false
        }
    }
    // 3. Pointer <op> Scalar (dst=Ptr, src=Scalar)
    else if dst_is_ptr {
        match op {
            AluOp::Add | AluOp::Sub => {
                if width == Width::W32 {
                    return true;
                }
                if src_min < -constants::MAX_VAR_OFF || src_max > constants::MAX_VAR_OFF {
                    return false;
                }
                if matches!(dst_type, RegType::PtrToMapValue { .. }) {
                    if src_max > i32::MAX as i64 {
                        error!("Forbidden offset {}", src_max);
                        return false;
                    }
                }
                if op == AluOp::Sub && matches!(dst_type, RegType::PtrToStack { .. }) {
                    return false;
                }
                true
            },
            AluOp::Neg => true,
            AluOp::Mov | AluOp::And => true, 
            _ => false
        }
    }
    // 4. Scalar <op> Pointer (dst=Scalar, src=Ptr)
    else {
        match op {
            AluOp::Add => {
                if dst_min < -constants::MAX_VAR_OFF || dst_max > constants::MAX_VAR_OFF {
                    return false;
                }
                if src_type.is_packet_ptr()
                    && (dst_min < -constants::MAX_PACKET_OFF || dst_max > constants::MAX_PACKET_OFF)
                {
                    return false;
                }
                true
            },
            AluOp::Sub => width == Width::W32,
            AluOp::Mov => true,
            _ => false
        }
    }
}

/// Check for division by zero.
pub(crate) fn is_div_by_zero(_dbm: &Dbm, src: &Operand) -> bool {
    match src {
        Operand::Imm(k) => *k == 0,
        // We don't need to report potential division by zero for register operands here.
        Operand::Reg(_) => false
    }
}
