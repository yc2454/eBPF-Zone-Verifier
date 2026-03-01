// src/analysis/cfg.rs
use crate::analysis::machine::env::VerifierEnv;
use crate::ast::{Instr, Program};
use crate::common::config::VerifierConfig;

#[derive(Clone, Copy, PartialEq, Eq)]
enum VisitState {
    Unvisited,
    Discovered, // On stack (Gray)
    Explored,   // Finished (Black)
}

/// Helper to mark a PC as a pruning point.
/// Mirrors `init_explored_state` in kernel.
fn init_explored_state(env: &mut VerifierEnv, pc: usize) {
    if pc < env.insn_aux_data.len() {
        env.insn_aux_data[pc].prune_point = true;
    }
}

/// Mirrors `visit_insn` from kernel/bpf/verifier.c
/// Returns a list of successors to push to the stack.
fn visit_insn(pc: usize, prog: &Program, env: &mut VerifierEnv) -> Result<Vec<usize>, String> {
    let instr = &prog.instrs[pc];
    let n = prog.instrs.len();
    let mut succs = Vec::new();

    // 1. NON-BRANCH INSTRUCTIONS (ALU, Load, Store)
    // Kernel: "All non-branch instructions have a single fall-through edge."
    // Logic: push_insn(t, t + 1, FALLTHROUGH, ...)
    if !matches!(
        instr,
        Instr::Jmp { .. }
            | Instr::If { .. }
            | Instr::Exit
            | Instr::Call { .. }
            | Instr::CallRel { .. }
    ) {
        if pc + 1 < n {
            succs.push(pc + 1);
        }
        return Ok(succs);
    }

    match instr {
        Instr::Exit => {
            // Kernel: return DONE_EXPLORING
            Ok(vec![])
        }
        Instr::Call { .. } => {
            // Kernel: visit_func_call_insn.
            // For now, we treat standard calls as falling through.
            // If we supported callbacks (timer_set_callback), we'd mark 'pc' here.
            // Assuming standard helper call:
            if pc + 1 < n {
                succs.push(pc + 1);
            }
            Ok(succs)
        }
        Instr::Jmp { target } => {
            // Kernel Case: BPF_JA
            // 1. Push successor (target)
            // "unconditional jump with single edge"
            succs.push(*target);

            // 2. Mark Target as Prune Point
            // "init_explored_state(env, t + insns[t].off + 1);"
            init_explored_state(env, *target);

            // 3. Mark Fallthrough as Prune Point (Defensive/History)
            // "if (t + 1 < insn_cnt) init_explored_state(env, t + 1);"
            if pc + 1 < n {
                init_explored_state(env, pc + 1);
            }

            Ok(succs)
        }
        Instr::If { target, .. } => {
            // Kernel Default Case: Conditional Jump
            // 1. Mark SELF as Prune Point
            // "init_explored_state(env, t);"
            init_explored_state(env, pc);

            // 2. Push Fallthrough
            if pc + 1 < n {
                succs.push(pc + 1);
            }

            // 3. Push Target
            succs.push(*target);

            Ok(succs)
        }
        Instr::CallRel { target } => {
            // 1. Push the Function Entry (The Call)
            succs.push(*target);
            init_explored_state(env, *target);

            // 2. Push the Return Point (Fallthrough)
            // We assume the function eventually returns.
            if pc + 1 < n {
                succs.push(pc + 1);
                // The return point is a convergence point (many callers return here),
                // so it's a good candidate for pruning.
                init_explored_state(env, pc + 1);
            }

            Ok(succs)
        }
        _ => {
            // Should be covered by non-branch check above, but safe fallback
            if pc + 1 < n {
                succs.push(pc + 1);
            }
            Ok(succs)
        }
    }
}

/// Get successors for a given instruction (for cycle detection).
fn get_successors(pc: usize, prog: &Program) -> Vec<usize> {
    let n = prog.instrs.len();
    if pc >= n {
        return vec![];
    }
    match &prog.instrs[pc] {
        Instr::Exit => vec![],
        Instr::Jmp { target } => vec![*target],
        Instr::If { target, .. } => {
            let mut succs = vec![*target];
            if pc + 1 < n {
                succs.push(pc + 1);
            }
            succs
        }
        _ => {
            if pc + 1 < n {
                vec![pc + 1]
            } else {
                vec![]
            }
        }
    }
}

/// Check if there's a path from `start` to `target` without going through `exit` instructions.
/// Used to detect if a backward jump is part of a real loop.
fn has_path_to(prog: &Program, start: usize, target: usize, visited: &mut Vec<bool>) -> bool {
    if start == target {
        return true;
    }
    if start >= prog.instrs.len() || visited[start] {
        return false;
    }
    visited[start] = true;

    for succ in get_successors(start, prog) {
        if has_path_to(prog, succ, target, visited) {
            return true;
        }
    }
    false
}

/// Check if a backward jump forms an actual loop (has a cycle).
/// A back-edge from B to H is a real loop if there's a path from H back to B.
fn is_real_loop(prog: &Program, back_edge_src: usize, back_edge_tgt: usize) -> bool {
    let mut visited = vec![false; prog.instrs.len()];
    has_path_to(prog, back_edge_tgt, back_edge_src, &mut visited)
}

/// Collect all back-edges that form actual loops.
/// A back-edge is a jump from a higher PC to a lower PC that creates a cycle.
/// Returns vec of (source_pc, target_pc).
fn collect_loop_back_edges(prog: &Program) -> Vec<(usize, usize)> {
    let mut back_edges = Vec::new();
    for (pc, instr) in prog.instrs.iter().enumerate() {
        let target = match instr {
            Instr::Jmp { target } if *target < pc => Some(*target),
            Instr::If { target, .. } if *target < pc => Some(*target),
            _ => None,
        };
        if let Some(tgt) = target {
            // Only include if it forms a real loop
            if is_real_loop(prog, pc, tgt) {
                back_edges.push((pc, tgt));
            }
        }
    }
    back_edges
}

/// Check if any forward jump skips over a loop head to land at the loop's
/// conditional check (back-edge source).
///
/// The kernel's bounded loop support requires single-entry loops (dominator tree).
/// The "start in the middle" pattern occurs when:
/// - There's a back-edge from B to H (loop head H < back-edge source B)
/// - There's a forward jump from A to B where A < H
/// - This means the forward jump skips over the loop head H and enters
///   at the conditional check B, causing the first iteration to skip
///   the loop body entirely.
///
/// Returns Some((from_pc, to_pc)) if such a pattern is found.
fn check_jump_into_loop_middle(prog: &Program) -> Option<(usize, usize)> {
    let back_edges = collect_loop_back_edges(prog);

    for (be_src, be_tgt) in &back_edges {
        let loop_head = *be_tgt;     // H - where the loop body starts
        let back_edge_src = *be_src; // B - where the conditional/back-edge is

        // Check for forward jumps that land at the back-edge source
        // from before the loop head
        for (pc, instr) in prog.instrs.iter().enumerate() {
            let targets: Vec<usize> = match instr {
                Instr::Jmp { target } => vec![*target],
                Instr::If { target, .. } => vec![*target],
                _ => vec![],
            };

            for target in targets {
                // Pattern: forward jump from before loop head, landing at back-edge source
                // This skips the loop body on first entry
                if pc < loop_head && target == back_edge_src {
                    return Some((pc, target));
                }
            }
        }
    }
    None
}

/// Performs DFS to validate CFG and populate prune points via visit_insn.
pub fn check_cfg(prog: &Program, env: &mut VerifierEnv, config: &VerifierConfig) -> Result<(), String> {
    let n = prog.instrs.len();
    if n == 0 {
        return Ok(());
    }

    // In kernel-mode, check for jumps into the middle of loops.
    // The kernel's bounded loop support requires single-entry loops (dominator tree).
    // Code that jumps into the middle of a loop cannot be verified.
    if config.require_single_loop_entry {
        if let Some((from_pc, to_pc)) = check_jump_into_loop_middle(prog) {
            return Err(format!("back-edge from insn {} to {}", from_pc, to_pc));
        }
    }

    let mut state = vec![VisitState::Unvisited; n];
    let mut stack = Vec::new();

    // Start at PC 0
    state[0] = VisitState::Discovered;
    stack.push(0);

    // Mark entry as prune point (implicit in kernel logic often)
    init_explored_state(env, 0);

    while let Some(&pc) = stack.last() {
        // If we haven't processed children yet (Discovered), do so now.
        // Note: Real DFS usually processes children then marks Explored.
        // We simulate this by checking if we have pushed children or not.
        // Simplified: We grab successors using visit_insn.

        let mut new_child = None;

        // This is a slight simplification of the kernel's stack-based state machine,
        // but achieves the same graph traversal coverage.
        let succs = visit_insn(pc, prog, env)?;

        for succ in succs {
            if succ >= n {
                return Err(format!("Jump out of bounds at PC {}", pc));
            }

            if state[succ] == VisitState::Unvisited {
                state[succ] = VisitState::Discovered;
                stack.push(succ);
                new_child = Some(succ);
                break; // DFS: Follow this path immediately
            } else if state[succ] == VisitState::Discovered {
                // Back-edge detected.
                // visit_insn logic handles marking, but we can double-check
                // if we strictly need to mark the loop head if visit_insn didn't.
                // Based on kernel BPF_JA/BPF_JNE logic, the points are already set.
            }
        }

        if new_child.is_none() {
            state[pc] = VisitState::Explored;
            stack.pop();
        }
    }

    // Check for unreachable instructions
    // Kernel: "unreachable insn %d" error
    for (pc, &s) in state.iter().enumerate() {
        if s == VisitState::Unvisited {
            return Err(format!("unreachable insn at pc {}", pc));
        }
    }

    Ok(())
}
