// src/analysis/transfer/alu/validation.rs

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::reg_types::RegType;
use crate::analysis::machine::state::State;
use crate::ast::{AluOp, Operand, Width};
use crate::common::constants;
use crate::domains::dbm::INF;
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
    src: &Operand,
) -> bool {
    let dst_is_ptr = dst_type.is_pointer();
    let src_is_ptr = src_type.is_pointer();

    let src_max = match src {
        Operand::Imm(k) => *k,
        Operand::Reg(r) => {
            let (_, max) = state.domain.get_interval(*r);
            if max == i64::MAX { INF } else { max }
        }
    };

    let src_min = match src {
        Operand::Imm(k) => *k,
        Operand::Reg(r) => {
            let (min, _) = state.domain.get_interval(*r);
            if min == i64::MIN { -INF } else { min }
        }
    };

    let (dst_min, dst_max) = state.domain.get_interval(dst);
    let dst_min = if dst_min == i64::MIN { -INF } else { dst_min };
    let dst_max = if dst_max == i64::MAX { INF } else { dst_max };

    // 1. Scalar <op> Scalar
    if !dst_is_ptr && !src_is_ptr {
        return true;
    }

    // PtrToArena fast-path: kernel `verifier.c` ~L15191 (v6.15) —
    // "Any arithmetic operations are allowed on arena pointers".
    // The kernel returns 0 immediately when `dst_reg->type ==
    // PTR_TO_ARENA`, regardless of src type or op. Mirror that:
    // skip every other validation rule (MAX_VAR_OFF, op allowlist,
    // ptr-ptr-sub same-type, etc.) for PtrToArena dst. This is what
    // alloc_pages's `pg - base; >> 12` shape needs (Shr on a pointer
    // is otherwise rejected as "Invalid pointer arithmetic"), and it
    // matches arena's 4GB sparse-mapped semantics where bounds-checks
    // are intentionally permissive.
    if matches!(dst_type, RegType::PtrToArena { .. }) {
        return true;
    }

    // 2. Pointer <op> Pointer
    if dst_is_ptr && src_is_ptr {
        match op {
            AluOp::Sub => {
                if env.ctx.is_privileged() {
                    return true;
                }
                RegType::is_same_pointer_type(dst_type, src_type)
                    || (matches!(dst_type, RegType::PtrToPacketEnd)
                        && matches!(src_type, RegType::PtrToPacket))
            }
            AluOp::Mov => true,
            _ => false,
        }
    }
    // 3. Pointer <op> Scalar (dst=Ptr, src=Scalar)
    else if dst_is_ptr {
        match op {
            AluOp::Add | AluOp::Sub => {
                // Kernel `adjust_ptr_min_max_vals` (verifier.c v6.15):
                // PTR_TO_FLOW_KEYS arithmetic is allowed only with a
                // known constant offset (`if (known) break;`); a
                // variable offset falls through to "pointer arithmetic
                // on flow_keys prohibited". Closes
                // verifier_value_illegal_alu::flow_keys_illegal_variable_offset_alu.
                if matches!(
                    dst_type,
                    RegType::PtrToBtfId { type_name, .. } if *type_name == "bpf_flow_keys"
                ) {
                    // Kernel `adjust_ptr_min_max_vals` PTR_TO_FLOW_KEYS
                    // arm gates on `tnum_is_const(off_reg->var_off)`;
                    // accept only known-constant offsets. Reject when
                    //   (a) interval bounds aren't constant, OR
                    //   (b) bounds are constant but the kernel would
                    //       have lost tnum precision somewhere in the
                    //       chain (DIV / MOD / non-const shift) — our
                    //       state.kernel_tnum_imprecise side channel
                    //       tracks exactly this.
                    // Closes
                    // verifier_value_illegal_alu::flow_keys_illegal_variable_offset_alu
                    // (`r8 = 8; r8 /= 1; r8 &= 8` — our tnum stays
                    // const(8) via the div-by-1 fast path, but the
                    // kernel marks r8 imprecise at the DIV).
                    let src_kernel_imprecise = match src {
                        Operand::Imm(_) => false,
                        Operand::Reg(r) => state.kernel_tnum_imprecise.contains(r),
                    };
                    if src_min != src_max || src_kernel_imprecise {
                        error!(
                            "[Verifier] pc {}: {} pointer arithmetic on flow_keys with variable offset prohibited",
                            state.pc,
                            dst.name()
                        );
                        return false;
                    }
                }
                if width == Width::W32 {
                    return true;
                }
                // Arithmetic on const map pointer is prohibited (unless adding 0)
                if matches!(dst_type, RegType::PtrToMapObject { .. }) {
                    // Allow adding 0 (it's a no-op)
                    if src_min == 0 && src_max == 0 {
                        return true;
                    }
                    error!(
                        "[Verifier] pc {}: {} pointer arithmetic on const map pointer prohibited",
                        state.pc,
                        dst.name()
                    );
                    return false;
                }
                // PtrToArena lives in a 4GB sparse-mapped address space and
                // the kernel verifier doesn't enforce MAX_VAR_OFF on its
                // arithmetic — programs routinely walk by ARENA_SIZE-sized
                // strides (see verifier_arena_large.c::big_alloc1's
                // `base + ARENA_SIZE - PAGE_SIZE * 2`). Bounds are not checked
                // at access either (sparse pages just zero-fault), so skip
                // both the MAX_VAR_OFF and the i32::MAX MapValue clamp here.
                let is_arena = matches!(dst_type, RegType::PtrToArena { .. });
                // Kernel verifier.c L14330: PTR_TO_CTX falls through the
                // base_type switch without bounds enforcement at arith time.
                // Wide / unbounded scalars are tolerated; the actual access
                // path (ctx field load/store, or helper arg validation) is
                // what catches misuse. Mirroring this admits libbpf's
                // `(void *)ctx + arg_spec->reg_off` idiom (usdt.bpf.h:185)
                // where reg_off is sign-extended u16 with full s64 bounds.
                let is_ctx = matches!(dst_type, RegType::PtrToCtx);
                if !is_arena
                    && !is_ctx
                    && (src_min < -constants::MAX_VAR_OFF || src_max > constants::MAX_VAR_OFF)
                {
                    return false;
                }
                if matches!(dst_type, RegType::PtrToMapValue { .. }) && src_max > i32::MAX as i64 {
                    error!("Forbidden offset {}", src_max);
                    return false;
                }
                if op == AluOp::Sub && matches!(dst_type, RegType::PtrToStack { .. }) {
                    return false;
                }
                true
            }
            AluOp::Neg => true,
            AluOp::Mov | AluOp::And => true,
            _ => false,
        }
    }
    // 4. Scalar <op> Pointer (dst=Scalar, src=Ptr)
    else {
        match op {
            AluOp::Add => {
                // Arithmetic on const map pointer is prohibited (unless adding 0)
                if matches!(src_type, RegType::PtrToMapObject { .. }) {
                    // Allow adding 0 (it's a no-op)
                    if dst_min == 0 && dst_max == 0 {
                        return true;
                    }
                    error!(
                        "[Verifier] pc {}: pointer arithmetic on const map pointer prohibited",
                        state.pc
                    );
                    return false;
                }
                // Symmetry with case 3 above: PtrToArena bypasses MAX_VAR_OFF.
                let src_is_arena = matches!(src_type, RegType::PtrToArena { .. });
                if !src_is_arena
                    && (dst_min < -constants::MAX_VAR_OFF || dst_max > constants::MAX_VAR_OFF)
                {
                    return false;
                }
                if src_type.is_packet_ptr()
                    && (dst_min < -constants::MAX_PACKET_OFF || dst_max > constants::MAX_PACKET_OFF)
                {
                    return false;
                }
                true
            }
            AluOp::Sub => width == Width::W32,
            AluOp::Mov => true,
            _ => false,
        }
    }
}

/// Check for division by zero.
pub(crate) fn is_div_by_zero(src: &Operand) -> bool {
    match src {
        Operand::Imm(k) => *k == 0,
        // We don't need to report potential division by zero for register operands here.
        Operand::Reg(_) => false,
    }
}
