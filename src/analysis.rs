// src/analysis.rs

// Module Declarations
pub mod context;
pub mod transfer;
pub mod access;
pub mod state;
pub mod heuristics;
pub mod reg_types;
pub mod env;
pub mod liveness;
pub mod cfg;     // NEW
pub mod pruning; // NEW

use std::collections::VecDeque;
use crate::ast::Program;
use crate::dbm::Dbm;
use crate::domain::{REG_ENV, Reg};
use crate::stats::AnalysisStats;

// Imports
use self::context::ExecContext;
use self::env::VerifierEnv;
use self::state::State;
use self::reg_types::RegType;

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    stats: &mut AnalysisStats,
) -> Vec<Dbm> {
    // 1. Initialize Verifier Environment (The "God Object")
    let mut env = VerifierEnv::new(ctx, prog);

    // 2. Run Static Analysis Passes
    println!("Running CFG Analysis...");
    if let Err(e) = cfg::check_cfg(prog, &mut env) {
        println!("CFG Error: {}", e);
        stats.abort = true;
        return vec![];
    }

    println!("Running Liveness Analysis...");
    liveness::compute_liveness(prog, &mut env);

    // 3. Initialize Entry State
    let mut initial_state = State::new(entry_dbm, 0);
    initial_state.types.set(Reg::R1, RegType::PtrToCtx);
    initial_state.types.set(ctx.r10, RegType::PtrToStack);
    // R0 is Scalar by default (representing unknown/uninitialized but safe-ish)
    initial_state.types.set(Reg::R0, RegType::ScalarValue);

    // 4. Setup Worklist (Stack for DFS)
    // DFS is preferred for Pruning: we want to fully explore one path to verify it,
    // so subsequent paths merging into it can be pruned against the history.
    let mut worklist = VecDeque::new();
    worklist.push_back(initial_state);

    // 5. Main Analysis Loop
    while let Some(state) = worklist.pop_back() {
        if stats.abort {
            println!("Analysis aborted.");
            break;
        }

        // A. Global Complexity Limit
        env.insn_processed += 1;
        if env.insn_processed > 1_000_000 {
            println!("[Verifier] Hit complexity limit (1,000,000 instructions). Aborting.");
            stats.abort = true;
            break;
        }

        // Heartbeat
        if env.insn_processed % 10_000 == 0 {
            println!("[Verifier] Processed {} instructions...", env.insn_processed);
        }

        // B. Pruning Check
        // "Have we been here before with a safer state?"
        if pruning::is_state_visited(&mut env, &state) {
            continue;
        }

        // C. Transfer Function
        if state.pc >= prog.instrs.len() {
            // Implicit exit or bug, handled by transfer usually, but safe guard here
            continue;
        }

        let instr = &prog.instrs[state.pc];
        
        // Log first few steps for debugging
        if env.insn_processed < 50 {
             let raw_pc = prog.pc_map.get(state.pc).copied().unwrap_or(0);
             println!("--- Step {}: PC {} (Raw {}) ---", env.insn_processed, state.pc, raw_pc);
        }

        let successors = transfer::transfer(&mut env, state, instr, stats);

        // D. Push Successors
        for succ in successors {
            worklist.push_back(succ);
        }
    }

    // 6. Return Results
    // The new architecture stores valid states in `env.explored_states`.
    // We construct a vector of DBMs (one per instruction) to satisfy the legacy signature.
    // We simply pick the first valid DBM found for each PC, or a fresh one if unreachable.
    let n = prog.instrs.len();
    let mut results = Vec::with_capacity(n);
    
    for i in 0..n {
        if let Some(states) = env.explored_states.get(&i) {
            // Just take the first one as representative for visualization/debug
            if !states.is_empty() {
                results.push(states[0].dbm.clone());
            } else {
                results.push(Dbm::new(REG_ENV.len()));
            }
        } else {
            results.push(Dbm::new(REG_ENV.len()));
        }
    }

    results
}
