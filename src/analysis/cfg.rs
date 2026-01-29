// src/analysis/cfg.rs
use crate::ast::{Program, Instr};
use crate::analysis::env::VerifierEnv;
use std::collections::BTreeSet;

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
fn visit_insn(
    pc: usize, 
    prog: &Program, 
    env: &mut VerifierEnv
) -> Result<Vec<usize>, String> {
    let instr = &prog.instrs[pc];
    let n = prog.instrs.len();
    let mut succs = Vec::new();

    // 1. NON-BRANCH INSTRUCTIONS (ALU, Load, Store)
    // Kernel: "All non-branch instructions have a single fall-through edge."
    // Logic: push_insn(t, t + 1, FALLTHROUGH, ...)
    if !matches!(instr, Instr::Jmp { .. } | Instr::If { .. } | Instr::Exit | Instr::Call { .. }) {
        if pc + 1 < n { succs.push(pc + 1); }
        return Ok(succs);
    }

    match instr {
        Instr::Exit => {
            // Kernel: return DONE_EXPLORING
            return Ok(vec![]);
        },
        Instr::Call { .. } => {
            // Kernel: visit_func_call_insn. 
            // For now, we treat standard calls as falling through.
            // If we supported callbacks (timer_set_callback), we'd mark 'pc' here.
            // Assuming standard helper call:
            if pc + 1 < n { succs.push(pc + 1); }
            return Ok(succs);
        },
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
            
            return Ok(succs);
        },
        Instr::If { target, .. } => {
            // Kernel Default Case: Conditional Jump
            // 1. Mark SELF as Prune Point
            // "init_explored_state(env, t);"
            init_explored_state(env, pc);

            // 2. Push Fallthrough
            if pc + 1 < n { succs.push(pc + 1); }
            
            // 3. Push Target
            succs.push(*target);

            return Ok(succs);
        },
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
            
            return Ok(succs);
        },
        _ => {
            // Should be covered by non-branch check above, but safe fallback
            if pc + 1 < n { succs.push(pc + 1); }
            Ok(succs)
        }
    }
}

pub fn check_subprogs(prog: &Program) -> Result<(), String> {
    // 1. Identify all Function Entry Points
    let mut func_starts = BTreeSet::new();
    func_starts.insert(0);
    
    for insn in &prog.instrs {
        if let Instr::CallRel { target } = insn {
            func_starts.insert(*target);
        }
    }
    
    let starts: Vec<usize> = func_starts.into_iter().collect();

    // 2. Iterate over each function range
    for (i, &start) in starts.iter().enumerate() {
        let end = starts.get(i + 1).cloned().unwrap_or(prog.instrs.len());

        // A. Validate instructions within the function
        for pc in start..end {
            let insn = &prog.instrs[pc];
            
            // Helper: is target local?
            let is_local = |t: usize| t >= start && t < end;

            match insn {
                Instr::Jmp { target } => {
                    if !is_local(*target) {
                        return Err(format!(
                            "jump out of range at pc {}: target {} is outside function scope [{}, {})", 
                            pc, target, start, end
                        ));
                    }
                },
                Instr::If { target, .. } => {
                    if !is_local(*target) {
                        return Err(format!(
                            "jump out of range at pc {}: target {} is outside function scope [{}, {})", 
                            pc, target, start, end
                        ));
                    }
                },
                Instr::CallRel { target } => {
                     if *target >= prog.instrs.len() {
                         return Err(format!("call out of bounds at pc {}: target {}", pc, target));
                     }
                },
                _ => {}
            }
        }

        // B. Validate the Function Terminator (The Fallthrough Check)
        // Every function must end with JMP or EXIT. It cannot fall through to 'end'.
        // The only exception is if 'end' is the end of the program (and even then, strict BPF requires Exit).
        if end > 0 {
            let last_pc = end - 1;
            let last_insn = &prog.instrs[last_pc];

            let is_terminator = match last_insn {
                Instr::Jmp { .. } => true, // Unconditional jump
                Instr::Exit => true,       // Exit
                _ => false,                // Everything else falls through
            };

            if !is_terminator {
                return Err(format!("last insn at pc {} is not an exit or jmp", last_pc));
            }
        }
    }
    Ok(())
}

/// Performs DFS to validate CFG and populate prune points via visit_insn.
pub fn check_cfg(prog: &Program, env: &mut VerifierEnv) -> Result<(), String> {
    let n = prog.instrs.len();
    if n == 0 { return Ok(()); }

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