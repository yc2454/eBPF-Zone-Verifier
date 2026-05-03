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

    // Bucket F-D: a back-edge compare-to-imm is a precision sink for
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
    if let Some(hidx) = state.history_idx
        && let Some(_) = condition_outcome(&state, width, left, op, &right)
    {
        let pcid = state.parent_cache_id;
        env.mark_chain_precision_backward(hidx, pcid, left);
        if let Operand::Reg(r) = right {
            env.mark_chain_precision_backward(hidx, pcid, r);
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
