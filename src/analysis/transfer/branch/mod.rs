use crate::analysis::machine::error::VerificationError;
// src/analysis/transfer/branch/mod.rs

pub mod constraints;
pub mod interval_packet;
pub mod outcome;
pub mod refinement;

use either::Either::{Left, Right};
use log::warn;

use crate::analysis::machine::env::VerifierEnv;
use crate::analysis::machine::reg::Reg;
use crate::analysis::machine::state::State;
use crate::ast::{CmpOp, Instr, Operand, Width};

use self::constraints::apply_jmp_constraints;
use self::interval_packet::refine_packet_bounds_on_branch;
use self::outcome::condition_outcome;
use self::refinement::{propagate_scalar_links, refine_branch};
use super::common::{check_operand_readable, check_reg_readable};

/// Map an AST `CmpOp` to the (taken, not-taken) BCF/BPF jump-op byte pair.
/// Returns `None` for ops we don't yet symbolically model (JSET — encoded
/// as `(x & y) ≠ 0`, special-cased in BCF; deferred to Phase 2).
fn cmp_op_to_bcf_pair(op: CmpOp) -> Option<(u8, u8)> {
    use crate::refinement::bcf::{
        BPF_JEQ, BPF_JGE, BPF_JGT, BPF_JLE, BPF_JLT, BPF_JNE, BPF_JSGE, BPF_JSGT, BPF_JSLE,
        BPF_JSLT,
    };
    Some(match op {
        CmpOp::Eq => (BPF_JEQ, BPF_JNE),
        CmpOp::Ne => (BPF_JNE, BPF_JEQ),
        CmpOp::UGt => (BPF_JGT, BPF_JLE),
        CmpOp::UGe => (BPF_JGE, BPF_JLT),
        CmpOp::ULt => (BPF_JLT, BPF_JGE),
        CmpOp::ULe => (BPF_JLE, BPF_JGT),
        CmpOp::SGt => (BPF_JSGT, BPF_JSLE),
        CmpOp::SGe => (BPF_JSGE, BPF_JSLT),
        CmpOp::SLt => (BPF_JSLT, BPF_JSGE),
        CmpOp::SLe => (BPF_JSLE, BPF_JSGT),
        CmpOp::Test => return None,
    })
}

/// Append the taken/not-taken predicates to each side's `path_conds`.
/// Skips the hook entirely when symbolic tracking is off or when either
/// side can't be materialized as a tracked register (anchor regs, etc.).
fn record_branch_path_conds(
    state_then: &mut State,
    state_else: &mut State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: &Operand,
) {
    if state_then.bcf.is_none() {
        return;
    }
    let Some((op_then, op_else)) = cmp_op_to_bcf_pair(op) else {
        return;
    };
    let Some(l_idx) = left.bcf_idx() else {
        return;
    };
    // Both clones share the original DAG up to this point, so we can build
    // expressions on `state_then`'s `bcf` and copy the resulting indices to
    // `state_else`'s `bcf` — both DAGs are byte-identical so far. After the
    // hook runs, the only divergence is the appended path-cond.
    let then_bcf = state_then.bcf.as_mut().expect("checked above");
    let lhs = then_bcf.materialize_reg64(l_idx);
    let rhs = match right {
        Operand::Imm(c) => {
            let v = if width == Width::W32 {
                (*c as u32) as u64
            } else {
                *c as u64
            };
            then_bcf.add_val64(v)
        }
        Operand::Reg(r) => match r.bcf_idx() {
            Some(ri) => then_bcf.materialize_reg64(ri),
            None => then_bcf.add_val64(0),
        },
    };
    // For W32 compares, narrow both operands to 32 bits before the predicate.
    let (cmp_l, cmp_r) = if width == Width::W32 {
        let l = then_bcf.extract_lo(32, lhs);
        let r = then_bcf.extract_lo(32, rhs);
        (l, r)
    } else {
        (lhs, rhs)
    };
    let pred_then = then_bcf.add_pred(op_then, cmp_l, cmp_r);
    let pred_else = then_bcf.add_pred(op_else, cmp_l, cmp_r);

    // Now mirror the **whole post-hook DAG** into state_else's bcf. The
    // pre-hook DAGs were identical (state_else.bcf was cloned from state
    // before the hook), so a wholesale replace keeps both sides
    // consistent. Then append only the not-taken pred to state_else's
    // path_conds (state_then gets the taken pred).
    let snapshot = (**then_bcf).clone();
    then_bcf.add_cond(pred_then);
    if let Some(else_bcf) = state_else.bcf.as_mut() {
        **else_bcf = snapshot;
        else_bcf.add_cond(pred_else);
    }
}

/// Transfer function for conditional branch instructions.
pub(crate) fn transfer_if(
    env: &mut VerifierEnv,
    state: State,
    width: Width,
    left: Reg,
    op: CmpOp,
    right: Operand,
    target: usize,
) -> Vec<State> {
    // Check operand readability
    if !check_reg_readable(env, &state, left) {
        return vec![];
    }
    if !check_operand_readable(env, &state, &right) {
        return vec![];
    }

    // --- STEP 1: Abstract Interpretation (Constraint Refinement) ---
    let mut state_then = state.clone();
    let mut state_else = state.clone();

    state_then.pc = target;
    state_else.pc = state.pc + 1;

    // --- BCF symbolic mirror: append the branch predicate to each side's
    // path_conds (taken op on `state_then`, reversed op on `state_else`).
    // Mirrors BCF's `record_path_cond` (kernel patches set1, cheat-sheet §2).
    // Test (JSET) is skipped for Phase 1; ALU/JMP comparisons cover
    // shift_constraint's `if r1 > 4` (UGt) path-cond requirement. ---
    record_branch_path_conds(&mut state_then, &mut state_else, width, left, op, &right);

    // Apply constraints to refine the DBM in the destination states
    match &right {
        Operand::Imm(imm) => apply_jmp_constraints(
            &mut state_then,
            &mut state_else,
            left,
            op,
            width,
            Right(*imm),
        ),
        Operand::Reg(r) => {
            apply_jmp_constraints(&mut state_then, &mut state_else, left, op, width, Left(*r));
            // Interval-specific: refine packet bounds from pointer comparisons
            refine_packet_bounds_on_branch(&mut state_then, &mut state_else, left, *r, op);
        }
    }

    // Scalar ID fan-out: propagate the constraint just applied to `left` to
    // every register and stack slot sharing its scalar id.
    propagate_scalar_links(&mut state_then, &mut state_else, left);

    // a back-edge compare-to-imm is a precision sink for
    // the compared register. The kernel's `mark_chain_precision` walks
    // backward from such sinks; without it, the loop counter widens at
    // intermediate may_goto sites, the bounds derived from this compare
    // don't propagate to downstream pointer arithmetic, and accumulator-
    // style loops (test1: `*R2=R1; R2+=8; R1++`) run away in abstract
    // interp because R1 widens before the next iteration's compare.
    //
    // Gate on **back-edge** (target < state.pc) to differentiate the
    // loop-back-to-head pattern from forward-exit conditionals. A
    // forward `if r < N goto exit` doesn't need the precision (the
    // loop head's re-refinement on entry handles each iteration), and
    // marking precise there blocks widening at the may_goto inside the
    // body (cond_break1's pattern). A backward `if r != K goto head`
    // (test1) does need it.
    // Precision sink at conditional branches. Kernel
    // `check_cond_jmp_op` calls `mark_chain_precision` only after
    // `is_branch_taken` decides the branch (one side is dead). Marking
    // precise on every conditional causes precision-mark blow-up that
    // `propagate_precision` then spreads further (bits_iter
    // state-explosion).
    if let Some(hidx) = state.history_idx {
        let static_resolves = condition_outcome(&state, width, left, op, &right).is_some();
        // Back-edge compare-to-imm catches tight scalar loops where the
        // exit predicate is `if r & C goto head` — the conditional
        // doesn't statically resolve (r is imprecise), but without
        // marking r precise the back-jump's precision contract isn't
        // tracked and convergence happily prunes the loop after one
        // iteration even when the kernel rejects via complexity limit
        // (verifier_search_pruning.c::short_loop1). Suppress this
        // sink when an iter slot is active on the stack — iter loops
        // get their convergence proof from iter-id mechanics, and
        // marking the conditional reg precise causes precision blow-up
        // on bits_iter / iter_nested_deeply_iters.
        let back_edge_imm = matches!(right, Operand::Imm(_)) && target < state.pc;
        let in_iter_loop = state
            .frames
            .iter()
            .any(|f| f.stack.has_active_iterators());
        let fire = static_resolves || (back_edge_imm && !in_iter_loop);
        if fire {
            let pcid = state.parent_cache_id;
            env.mark_chain_precision_backward(hidx, pcid, left);
            if let Operand::Reg(r) = right {
                env.mark_chain_precision_backward(hidx, pcid, r);
            }
        }
    }

    // Branch Type Refinement (For map and socket pointers)
    let instr = Instr::If {
        width,
        left,
        op,
        right,
        target,
    };
    refine_branch(&mut state_then, &instr, true);
    refine_branch(&mut state_else, &instr, false);

    let backward_jump_forbidden = |st: &State| -> bool {
        if target >= st.pc {
            return false;
        }
        let on_path = st
            .history_idx
            .map(|idx| env.history.is_on_path(idx, target))
            .unwrap_or(false);
        let already_explored = env.explored_states.contains_key(&target);
        !on_path && !already_explored
    };

    // Check for statically determined branches
    if let Some(outcome) = condition_outcome(&state, width, left, op, &right) {
        return if outcome {
            if backward_jump_forbidden(&state_then) {
                env.fail(VerificationError::BackEdge {
                    pc: state.pc,
                    target,
                });
                vec![]
            } else {
                vec![state_then]
            }
        } else {
            vec![state_else]
        };
    }

    if backward_jump_forbidden(&state_then) {
        env.fail(VerificationError::BackEdge {
            pc: state.pc,
            target,
        });
        return vec![];
    }

    // Return only consistent states
    let mut out = Vec::new();
    if !state_else.domain.is_inconsistent() {
        out.push(state_else);
    } else {
        warn!("Else branch is inconsistent")
    }
    if !state_then.domain.is_inconsistent() {
        out.push(state_then);
    } else {
        warn!("Then branch is inconsistent")
    }
    out
}
