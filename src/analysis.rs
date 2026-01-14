// src/analysis.rs

pub mod context;
pub mod transfer;
pub mod access;
pub mod state;
pub mod heuristics;
pub mod reg_types;
pub mod env;
pub mod liveness;
pub mod cfg;
pub mod pruning;
pub mod loop_check;
pub mod constants;

use std::collections::VecDeque;
use crate::ast::Program;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{REG_ENV, Reg};

use self::context::ExecContext;
use self::env::{VerifierEnv, VerificationError};
use self::state::State;
use self::reg_types::RegType;

// --- TUNABLE LOGGING CONFIGURATION ---
// 0: Quiet (Critical Errors Only)
// 1: Info  (Heartbeats every 10k, Summary)
// 2: Trace (Log every instruction execution - PC only)
// 3: Debug (Log every instruction + Register Types)
pub const VERBOSITY: u8 = 3;

// Debugging Aid: Force-enable Level 3 logging for a specific PC
pub const DEBUG_PC: Option<usize> = None; 
// -------------------------------------

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
) -> Result<Vec<Dbm>, VerificationError> {
    // 1. Initialize Verifier Environment
    let mut env = VerifierEnv::new(ctx, prog);

    if VERBOSITY >= 1 { println!("[Analysis] Running Static Analysis Passes..."); }

    if let Err(e) = cfg::check_cfg(prog, &mut env) {
        println!("[Analysis] CFG Error: {}", e);
        return Err(VerificationError::CfgError(e));
    }

    liveness::compute_liveness(prog, &mut env);

    // 2. Initialize Entry State
    let mut initial_state = State::new(entry_dbm, 0);
    initial_state.types.set(Reg::R1, RegType::PtrToCtx);
    initial_state.types.set(ctx.r10, RegType::PtrToStack);
    initial_state.types.set(Reg::R0, RegType::ScalarValue);

    // 3. Setup Worklist
    let mut worklist = VecDeque::new();
    worklist.push_back(initial_state);

    if VERBOSITY >= 1 { println!("[Analysis] Starting Abstract Interpretation..."); }

    // 4. Main Analysis Loop
    while let Some(state) = worklist.pop_back() {
        if env.failed() {
            if VERBOSITY >= 1 { println!("[Analysis] Aborted due to previous errors."); }
            break;
        }

        // A. Global Complexity Limit
        env.insn_processed += 1;
        if env.insn_processed > constants::MAX_INSN_PROCESSED {
            if VERBOSITY >= 1 {
                println!("[Verifier] Hit complexity limit ({} instructions). Aborting.", constants::MAX_INSN_PROCESSED);
            }
            env.fail(VerificationError::ComplexityLimitExceeded { limit: constants::MAX_INSN_PROCESSED });
            break;
        }

        // B. Heartbeat Logging (Level 1+)
        if VERBOSITY >= 1 && env.insn_processed % constants::LOG_HEARTBEAT_INTERVAL == 0 {
            println!("[Verifier] Processed {} instructions. Worklist size: {}", env.insn_processed, worklist.len());
        }

        // C. Pruning Check
        if pruning::is_state_visited(&mut env, &state) {
            if VERBOSITY >= 2 { println!("[Verifier] Pruned state at PC {} (already visited).", state.pc); }
            continue;
        }

        // D. Instruction Fetch
        if state.pc >= prog.instrs.len() { continue; }
        let instr = &prog.instrs[state.pc];
        
        // E. Logging
        let is_target = DEBUG_PC.map(|t| t == state.pc).unwrap_or(false);
        let show_trace = is_target || VERBOSITY >= 2 || (VERBOSITY >= 1 && env.insn_processed <= 50);
        let show_debug = is_target || VERBOSITY >= 3;

        if show_trace {
             let raw_pc = prog.pc_map.get(state.pc).copied().unwrap_or(0);
             println!("--- Step {}: PC {} (Raw {}) ---", env.insn_processed, state.pc, raw_pc);
             
             if show_debug {
                 println!("    Instr: {:?}", instr);
                 println!("    Regs:  {:?}", state.types.regs);
             }
        }

        // F. Transfer Function
        let successors = transfer::transfer(&mut env, state, instr);

        // G. Critical Failure Check
        if env.failed() {
            if VERBOSITY >= 1 {
                println!("[Verifier] Analysis halted due to critical error: {}", env.error.as_ref().unwrap().description());
            }
            break;
        }

        // H. Push Successors
        for succ in successors {
            worklist.push_back(succ);
        }
    }

    // --- FINAL REPORT ---
    if let Some(err) = env.error {
        if VERBOSITY >= 1 { println!("\n[Verifier] FAILURE: {:?}", err); }
        return Err(err);
    }
    
    if VERBOSITY >= 1 {
        println!("\n[Verifier] Success! Verified {} instructions.", env.insn_processed);
        println!("[Analysis] Finished. Total Steps: {}", env.insn_processed); 
    }

    // 5. Return Results
    let n = prog.instrs.len();
    let mut results = Vec::with_capacity(n);
    
    for i in 0..n {
        if let Some(states) = env.explored_states.get(&i) {
            if !states.is_empty() {
                results.push(states[0].dbm.clone());
            } else {
                results.push(Dbm::new(REG_ENV.len()));
            }
        } else {
            results.push(Dbm::new(REG_ENV.len()));
        }
    }

    Ok(results)
}
