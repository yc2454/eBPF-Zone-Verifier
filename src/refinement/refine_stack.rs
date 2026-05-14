//! Refinement callback for the stack-OOB rejection site.
//!
//! Mirrors BCF's `bcf_refine_stack_access` (cheat-sheet §4a). Called from
//! [`crate::analysis::transfer::memory::stack`] at the two `StackOutOfBounds`
//! rejection paths (known-offset and unknown-offset). On Unsat from cvc5,
//! returns the BCF proof bytes — the caller suppresses the rejection.
//!
//! Reads the variable part of the offset directly from `bcf_expr` and the
//! constant part `K` from `state.ptr_const_off` (kernel `ptr_reg->off`,
//! verifier.c:14383-14471). Builds the kernel-shape refine_cond
//! `JSGT(var_off_expr, higher_bound - sz - (insn_off + K))` and asks
//! cvc5 to prove it unsatisfiable under the accumulated path conditions.
//! Multi-variable-contributor chains (`r1 += r0; r1 += r2`) work because
//! K is tracked explicitly, not reconstructed from interval algebra.

use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::analysis::transfer::alu::helpers::bcf_reg_bounds;
use crate::common::constants;
use crate::refinement::bcf::BPF_JSGT;
use crate::refinement::smtlib;
use crate::refinement::solver;
use crate::refinement::symbolic::{build_goal_root, SymbolicState};
use log::{debug, warn};

/// Attempt to discharge a stack-OOB rejection via cvc5. Returns the BCF
/// proof bytes on success; `None` if no refinement could be built (no bcf
/// state, no contributor, missing symbolic info) or cvc5 didn't return
/// `unsat`.
/// Returned on success: the goal-root expr-id and the symbolic-state
/// snapshot whose `exprs` table the goal lives in, plus the proof bytes.
pub struct RefineOk {
    pub proof_bytes: Vec<u8>,
    pub goal_root: u32,
    pub sym: SymbolicState,
}

pub fn try_refine_stack_oob(
    state: &State,
    base: Reg,
    instruction_offset: i64,
    size: i64,
    base_pc: Option<usize>,
) -> Option<RefineOk> {
    let bcf_ref = state.bcf.as_ref()?;
    let mut sym: SymbolicState = (**bcf_ref).clone();
    // Mirror the kernel's `bcf_track` suffix-only br_cond emission:
    // drop path_conds emitted at PCs strictly before the suffix's base
    // PC (the point at which the refine target reg's definition chain
    // has bottomed out). `None` ⇒ keep all path_conds (sound, just not
    // as tight as the kernel's runtime CONJ).
    if let Some(bp) = base_pc {
        sym.filter_path_conds_from_pc(bp);
    }

    // Step 1: get the variable part of base's offset from r10. After the
    // handle_add ptr+imm skip, base.bcf_expr no longer embeds the const
    // offset — it represents only the symbolic-variable contribution.
    let b_idx = base.bcf_idx()?;
    let var_off_expr = sym.get_reg(b_idx)?;

    // Step 2: read the constant offset K straight out of `ptr_const_off`,
    // which mirrors the kernel's `ptr_reg->off` (verifier.c:14383-14471).
    // Defaults to 0 — sound when `base = r10` (no `+= K` since mov), and
    // also when the entry was lost across a non-managed op (in which case
    // the K=0 assumption is the same one the abstract domain made when
    // it forgot, so an out-of-band rejection would have triggered first).
    let const_off = state.ptr_const_off.get(&base).copied().unwrap_or(0);

    // Step 3: build refine_cond per kernel `__bcf_refine_access_bound`
    // (verifier.c:5291). For stack accesses, `size` is always known
    // constant, so we hit case 2 of the three-way switch: ptr off
    // variable, size constant.
    //
    //   high_pred = JSGT(off_expr, higher_bound - sz - off)
    //   low_pred  = JSLT(off_expr, lower_bound - off)   (only if needed)
    //   refine_cond = high_pred  OR  DISJ(low_pred, high_pred)
    //
    // The kernel uses 32-bit BCF operations when both ptr_reg and
    // size_reg fit in s32 (verifier.c:5306-5310). For stack pointers
    // size_reg is always a constant within s32, so the deciding factor
    // is whether `base`'s 64-bit interval fits in s32.
    let ptr_bounds = bcf_reg_bounds(state, base);
    let bit32 = ptr_bounds.fit_s32();
    let off_expr_use = if bit32 {
        sym.expr32(var_off_expr)
    } else {
        var_off_expr
    };

    let total_off = const_off + instruction_offset;
    let higher_bound: i64 = 0; // stack top
    let lower_bound: i64 = constants::BPF_STACK_MIN; // -512

    // Predicate threshold: high_bound - sz - off.
    let high_thresh = higher_bound - size - total_off;
    let high_thresh_expr = sym.add_val(high_thresh as u64, bit32);
    let high_pred = sym.add_pred(BPF_JSGT, off_expr_use, high_thresh_expr);

    // Low-side check: only when the abstract domain hasn't already proven
    // safe (min_off < lower_bound). For shift_constraint this is false
    // (min_off = -16 > lower_bound = -512), so we just use high_pred.
    let (smin_base, _) = state.domain.get_interval(base);
    let min_off = smin_base + instruction_offset;
    let oob = if min_off < lower_bound {
        let low_thresh = lower_bound - total_off;
        let low_thresh_expr = sym.add_val(low_thresh as u64, bit32);
        let low_pred = sym.add_pred(crate::refinement::bcf::BPF_JSLT, off_expr_use, low_thresh_expr);
        sym.add_disj(vec![low_pred, high_pred])
    } else {
        high_pred
    };
    sym.set_refine_cond(oob);

    // 5. Encode to SMT-LIB + call cvc5.
    let smt = match smtlib::encode(&sym) {
        Ok(s) => s,
        Err(e) => {
            warn!("[bcf] SMT-LIB encode failed: {}", e);
            return None;
        }
    };
    if std::env::var("ZOVIA_BCF_DUMP_SMT").is_ok() {
        eprintln!("---- [bcf] SMT-LIB to cvc5 ----\n{}\n---- end ----", smt);
    }
    match solver::solve(&smt) {
        Ok(bytes) => {
            debug!("[bcf] stack-OOB refinement: cvc5 accepted ({} bytes)", bytes.len());
            let goal_root = build_goal_root(&mut sym, oob);
            Some(RefineOk { proof_bytes: bytes, goal_root, sym })
        }
        Err(e) => {
            debug!("[bcf] stack-OOB refinement: cvc5 declined ({})", e);
            None
        }
    }
}
