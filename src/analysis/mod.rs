// src/analysis.rs

pub mod context;
pub mod transfer;
pub mod access;
pub mod state;
pub mod reg_types;
pub mod env;
pub mod liveness;
pub mod cfg;
pub mod pruning;
pub mod constants;
pub mod history;

use std::collections::VecDeque;
use crate::ast::Program;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{REG_ENV, Reg};
use log::{debug, error, info};

use self::context::ExecContext;
use self::env::VerifierEnv;
use self::state::State;
use self::reg_types::RegType;
use self::history::History;
use crate::misc::config::VerifierConfig;

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    config: &VerifierConfig,
) -> Result<Vec<Dbm>, env::VerificationError> {
    // 1. Initialize Verifier Environment
    let mut env = VerifierEnv::new(ctx, prog);

    if config.verbosity >= 1 { 
        info!(target: "app", "[Analysis] Running Static Analysis Passes..."); 
        if config.skip_dbm_check {
            info!(target: "app", "[Analysis] DBM comparison disabled (--skip-dbm)");
        }
    }

    if let Err(e) = cfg::check_subprogs(prog) {
        error!(target: "app", "[Analysis] CFG Error: {}", e);
        return Err(env::VerificationError::CfgError(e));
    }

    if let Err(e) = cfg::check_cfg(prog, &mut env) {
        error!(target: "app", "[Analysis] CFG Error: {}", e);
        return Err(env::VerificationError::CfgError(e));
    }

    liveness::compute_liveness(prog, &mut env);

    // 2. Initialize Entry State
    let mut initial_state = State::new(entry_dbm, 0);
    initial_state.types.set(Reg::R1, RegType::PtrToCtx);
    initial_state.types.set(Reg::R10, RegType::PtrToStack { offset: Some(0) });
    initial_state.types.set(Reg::R0, RegType::ScalarValue);

    // 3. Setup Worklist
    let mut worklist = VecDeque::new();
    worklist.push_back(initial_state);

    if config.verbosity >= 1 { 
        info!(target: "app", "[Analysis] Starting Abstract Interpretation..."); 
    }

    // Track pruning statistics
    let mut prune_count: usize = 0;

    // Optional History Tracking
    let mut history = if config.enable_path_trace {
        Some(History::new())
    } else {
        None
    };

    let mut pruning_mgr = pruning::PruningManager::new();

    // 4. Main Analysis Loop
    while let Some(state) = worklist.pop_back() {
        if env.failed() {
            error!(target: "app", "[Analysis] Aborted due to previous errors.");
            break;
        }

        // Fail immediately if we somehow reach the second half of LD_IMM64
        if prog.invalid_pc_set.contains(&state.pc) {
            env.fail(env::VerificationError::InvalidBPFLoadImmInsn { pc: state.pc });
            break;
        }

        // A. Pruning Check
        if pruning::is_state_visited(&mut env, &state, config, &mut pruning_mgr) {
            prune_count += 1;
            continue;
        }

        // B. Global Complexity Limit (only count non-pruned states)
        env.insn_processed += 1;
        if env.insn_processed > config.max_insn {
            // We use error! with target="analysis" to auto-trigger the crash dump
            error!(target: "analysis", "[Verifier] Hit complexity limit ({} instructions). Aborting.", config.max_insn);
            info!(target: "app", "[Verifier] (Pruned {} states before limit)", prune_count);
            info!(target: "app", "[Verifier] Tip: Try --skip-dbm or --max-insn N to increase limit");
            env.fail(env::VerificationError::ComplexityLimitExceeded { limit: config.max_insn });
            break;
        }

        // C. Heartbeat Logging (Level 1+)
        if config.verbosity >= 1 && env.insn_processed % config.log_interval == 0 {
            info!(target: "app", "[Verifier] Processed {} instructions (pruned {}). Worklist size: {}", 
                     env.insn_processed, prune_count, worklist.len());
        }

        // D. Instruction Fetch
        if state.pc >= prog.instrs.len() { continue; }
        let instr = &prog.instrs[state.pc];

        // If history is enabled, record this step using the parent index from the state.
        let current_step_idx = if let Some(h) = &mut history {
            let reg_types_str = state.types.reg_types_str();
            Some(h.record(state.pc, instr, reg_types_str, state.history_idx))
        } else {
            None
        };
        
        // E. Logging (Delegated to Global Logger)
        // We output the raw data following the protocol. The Logger filters it.
        debug!(target: "app", "|PC:{}| Instr: {:?} | Regs: {:?}", 
               state.pc, instr, state.types);
        if config.verbosity >= 2 {
            state.dbm.pretty_print();
        }

        // F. Transfer Function
        let successors = transfer::transfer(&mut env, state, instr);

        // G. Critical Failure Check
        if env.failed() {
            // This error! call triggers the RingBufferLogger to dump the last 100 steps
            error!(target: "analysis", "[Verifier] Analysis halted due to critical error: {}", 
                   env.error.as_ref().unwrap().description());
            // Additionally, if we have history tracking, reconstruct and print the crash trace
            if let Some(h) = &history {
                if let Some(crash_idx) = current_step_idx {
                    let trace = h.get_trace(crash_idx);
                    // Print directly to stdout (or error log) so it stands out
                    println!("\n=== CRASH PATH RECONSTRUCTION ({} Steps) ===", trace.len());
                    for (i, step) in trace.iter().enumerate() {
                        println!("[{:03}] PC {:<4} | {}\nReg Types: {}", i, step.pc, step.instr_str, step.reg_types_str);
                    }
                    println!("=============================================\n");
                }
            }
            break;
        }

        // H. Push Successors
        for mut succ in successors {
            succ.history_idx = current_step_idx;
            worklist.push_back(succ);
        }
    }

    // --- FINAL REPORT ---
    if let Some(err) = &env.error {
        info!(target: "app", "\n[Verifier] FAILURE: {:?}", err);
        if config.verbosity >= 1 { 
            info!(target: "app", "[Analysis] Finished. Total Steps: {}, Pruned: {}", env.insn_processed, prune_count); 
        }
        return Err(err.clone());
    }
    
    info!(target: "app", "\n[Verifier] Success! Verified {} instructions (pruned {} states).", 
             env.insn_processed, prune_count);

    if config.verbosity >= 1 { 
        info!(target: "app", "[Analysis] Finished. Total Steps: {}, Pruned: {}", env.insn_processed, prune_count); 
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