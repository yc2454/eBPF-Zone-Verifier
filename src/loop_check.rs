// src/analysis/loop_check.rs
use crate::ast::{Instr, Program};

#[derive(Clone, PartialEq, Eq)]
enum VisitState {
    Unvisited,
    Visiting, // Currently in the recursion stack (Back-edge target)
    Visited,  // Fully processed
}

/// Performs a DFS from the entry point to detect any back-edges (cycles).
/// Returns Err(msg) if a loop is detected.
pub fn check_for_loops(prog: &Program) -> Result<(), String> {
    let len = prog.instrs.len();
    if len == 0 { return Ok(()); }

    let mut state = vec![VisitState::Unvisited; len];
    
    // We only check code reachable from the entry (PC 0).
    // Unreachable loops don't hurt the analyzer, but we could check all if strictness is desired.
    check_node(0, prog, &mut state)
}

fn check_node(pc: usize, prog: &Program, state: &mut Vec<VisitState>) -> Result<(), String> {
    if pc >= prog.instrs.len() {
        // Jumping out of bounds is a different error (verification failure), 
        // but for loop checking, it's a dead end, so no loop.
        return Ok(());
    }

    match state[pc] {
        VisitState::Visited => return Ok(()),
        VisitState::Visiting => {
            // We found a node that is currently being visited -> Cycle!
            return Err(format!("Infinite loop detected at PC {} (Back-edge)", pc));
        }
        VisitState::Unvisited => {},
    }

    // Mark as currently visiting
    state[pc] = VisitState::Visiting;

    // Recurse into successors
    let successors = get_successors(pc, &prog.instrs[pc]);
    for succ in successors {
        check_node(succ, prog, state)?;
    }

    // Mark as visited
    state[pc] = VisitState::Visited;
    Ok(())
}

fn get_successors(pc: usize, instr: &Instr) -> Vec<usize> {
    match instr {
        // Unconditional jump: only 1 successor
        Instr::Jmp { target } => vec![*target],
        
        // Conditional jump: 2 successors (Fallthrough + Target)
        Instr::If { target, .. } => vec![pc + 1, *target],
        
        // Exit: 0 successors
        Instr::Exit => vec![],
        
        // Instructions that fall through to the next
        // (Call, Alu, Load, Store, etc.)
        _ => vec![pc + 1],
    }
}