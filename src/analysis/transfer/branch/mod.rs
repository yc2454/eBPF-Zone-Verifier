// src/analysis/transfer/branch/mod.rs

pub mod outcome;
pub mod constraints;
pub mod refinement;

use log::warn;
use either::Either::{Left, Right};

use crate::analysis::machine::env::{VerifierEnv, VerificationError};
use crate::analysis::machine::state::State;
use crate::ast::{Instr, CmpOp, Operand, Width};
use crate::analysis::machine::reg::Reg;

use self::outcome::condition_outcome;
use self::constraints::apply_jmp_constraints;
use self::refinement::refine_branch;
use super::common::{check_reg_readable, check_operand_readable};

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
        Operand::Imm(imm) => 
            apply_jmp_constraints(&mut state_then, &mut state_else, left, op, width, Right(*imm)),
        Operand::Reg(r) => 
            apply_jmp_constraints(&mut state_then, &mut state_else, left, op, width, Left(*r)),
    }

    // Branch Type Refinement (For map and socket pointers)
    let instr = Instr::If { width, left, op, right: right.clone(), target };
    refine_branch(&mut state_then, &instr, true);
    refine_branch(&mut state_else, &instr, false);

    let backward_jump_forbidden = |st: &State| -> bool {
        if target >= st.pc {
            return false;
        }
        let on_path = st.history_idx
            .map(|idx| env.history.path_contains_pc(idx, target))
            .unwrap_or(false);
        let already_explored = env.explored_states.contains_key(&target);
        !on_path && !already_explored
    };

    // Check for statically determined branches
    if let Some(outcome) = condition_outcome(&state, width, left, op, &right) {
        return if outcome {
            if backward_jump_forbidden(&state_then) {
                env.fail(VerificationError::BackEdge { pc: state.pc, target });
                vec![]
            } else {
                vec![state_then]
            }
        } else {
            vec![state_else]
        };
    }

    if backward_jump_forbidden(&state_then) {
        env.fail(VerificationError::BackEdge { pc: state.pc, target });
        return vec![];
    }

    // Return only consistent states
    let mut out = Vec::new();
    if !state_else.dbm.is_inconsistent() { out.push(state_else); } else { warn!("Else branch is inconsistent") }
    if !state_then.dbm.is_inconsistent() { out.push(state_then); } else { warn!("Then branch is inconsistent") }
    out
}
