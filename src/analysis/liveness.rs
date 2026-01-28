// src/analysis/liveness.rs
use crate::ast::{Program, Instr, Operand};
use crate::zone::domain::Reg;
use crate::analysis::env::VerifierEnv;
use std::collections::{HashSet};

/// Computes Liveness Analysis and populates env.insn_aux_data[pc].live_regs
pub fn compute_liveness(prog: &Program, env: &mut VerifierEnv) {
    let n = prog.instrs.len();
    let mut live_in: Vec<HashSet<Reg>> = vec![HashSet::new(); n];
    let mut worklist: Vec<usize> = (0..n).collect(); // Start with all instructions

    // Standard Backward Dataflow Loop
    while let Some(pc) = worklist.pop() {
        let instr = &prog.instrs[pc];
        
        // 1. Calculate LiveOut (Union of Successors' LiveIn)
        let successors = get_successors(pc, instr, n);
        let mut live_out = HashSet::new();
        for succ in successors {
            if succ < n {
                live_out.extend(live_in[succ].iter().cloned());
            }
        }

        // 2. Calculate LiveIn = Use U (LiveOut - Def)
        let (uses, defs) = get_use_def(instr);
        
        let mut new_live_in = live_out.clone();
        for def in &defs {
            new_live_in.remove(def);
        }
        for use_reg in uses {
            new_live_in.insert(use_reg);
        }

        // 3. Update and Propagate
        if new_live_in != live_in[pc] {
            live_in[pc] = new_live_in;
            // If LiveIn changed, predecessors must update their LiveOut
            for pred in get_predecessors(pc, prog) {
                if !worklist.contains(&pred) {
                    worklist.push(pred);
                }
            }
        }
    }

    // 4. Save to Env
    for pc in 0..n {
        env.insn_aux_data[pc].live_regs = live_in[pc].clone();
    }
}

// --- Helpers ---

fn get_successors(pc: usize, instr: &Instr, n: usize) -> Vec<usize> {
    let mut succs = Vec::new();
    match instr {
        Instr::Exit => {}, // No successors
        Instr::Jmp { target } => succs.push(*target),
        Instr::If { target, .. } => {
            if pc + 1 < n { succs.push(pc + 1); } // Fallthrough
            succs.push(*target);                  // Branch
        },
        _ => {
            if pc + 1 < n { succs.push(pc + 1); }
        }
    }
    succs
}

// Naive predecessor calculation (O(N^2) but fine for BPF size limits).
// A real CFG would build this once.
fn get_predecessors(target_pc: usize, prog: &Program) -> Vec<usize> {
    let mut preds = Vec::new();
    for (pc, instr) in prog.instrs.iter().enumerate() {
        let succs = get_successors(pc, instr, prog.instrs.len());
        if succs.contains(&target_pc) {
            preds.push(pc);
        }
    }
    preds
}

fn get_use_def(instr: &Instr) -> (HashSet<Reg>, HashSet<Reg>) {
    let mut uses = HashSet::new();
    let mut defs = HashSet::new();

    match instr {
        Instr::MovArg0 { dst } => {
            defs.insert(*dst);
        }
        Instr::Alu { op, dst, src, .. } => {
            use crate::ast::AluOp;
            // "Mov" overwrites dst (Def), others read dst (Use)
            if matches!(op, AluOp::Mov) {
                defs.insert(*dst);
            } else {
                uses.insert(*dst);
                defs.insert(*dst);
            }

            if let Operand::Reg(r) = src {
                uses.insert(*r);
            }
        }
        Instr::Load { dst, base, .. } => {
            uses.insert(*base);
            defs.insert(*dst);
        }
        Instr::Store { base, src, .. } => {
            uses.insert(*base);
            if let Operand::Reg(r) = src {
                uses.insert(*r);
            }
        }
        Instr::AtomicAdd { base, src, .. } => {
            uses.insert(*base);
            uses.insert(*src);
            defs.insert(*base); // base is modified
        }
        Instr::If { left, right, .. } => {
            uses.insert(*left);
            if let Operand::Reg(r) = right {
                uses.insert(*r);
            }
        }
        Instr::Call { .. } => {
            // Helpers use R1-R5
            uses.insert(Reg::R1);
            uses.insert(Reg::R2);
            uses.insert(Reg::R3);
            uses.insert(Reg::R4);
            uses.insert(Reg::R5);
            
            // Helpers define R0 (return value) and clobber R1-R5
            defs.insert(Reg::R0);
            defs.insert(Reg::R1);
            defs.insert(Reg::R2);
            defs.insert(Reg::R3);
            defs.insert(Reg::R4);
            defs.insert(Reg::R5);
        }
        Instr::CallRel { .. } => {
            uses.insert(Reg::R1);
            uses.insert(Reg::R2);
            uses.insert(Reg::R3);
            uses.insert(Reg::R4);
            uses.insert(Reg::R5);
            
            defs.insert(Reg::R0);
            defs.insert(Reg::R1);
            defs.insert(Reg::R2);
            defs.insert(Reg::R3);
            defs.insert(Reg::R4);
            defs.insert(Reg::R5);
        }
        Instr::Exit => {
            uses.insert(Reg::R0); // Return value
        }
        Instr::PacketLoad { src, .. } => {
            if let Some(r) = src {
                uses.insert(*r);
            }
        }
        Instr::Jmp { .. } => {} // Unconditional jump uses nothing
        Instr::Endian { dst, .. } => {
            uses.insert(*dst);
            defs.insert(*dst);
        }
    }

    (uses, defs)
}
