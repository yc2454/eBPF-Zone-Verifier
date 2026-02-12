// src/analysis.rs

pub mod transfer;
pub mod machine;
pub mod flow;

use std::collections::VecDeque;
use crate::analysis::machine::frame_stack::FrameLevel;
use crate::ast::Program;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{Reg, init_packet_anchors};
use log::{debug, error, info};

use self::machine::context::ExecContext;
use self::machine::env::{VerifierEnv, VerificationError};
use self::machine::state::State;
use self::machine::reg_types::RegType;
use crate::common::config::VerifierConfig;
use self::flow::{cfg, liveness, pruning, merging, subprog};

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    config: &VerifierConfig,
) -> Result<Vec<Dbm>, VerificationError> {
    // 1. Initialize Verifier Environment
    let mut env = VerifierEnv::new(ctx, prog);

    if config.verbosity >= 1 { 
        info!(target: "app", "[Analysis] Running Static Analysis Passes..."); 
        if config.skip_dbm_check {
            info!(target: "app", "[Analysis] DBM comparison disabled (--skip-dbm)");
        }
    }

    if let Err(e) = subprog::check_subprogs(prog) {
        error!(target: "app", "[Analysis] CFG Error: {}", e);
        return Err(VerificationError::SubprogError { e });
    }

    if let Err(e) = subprog::check_stack_overflow(prog) {
        error!(target: "app", "[Analysis] Stack Error: {}", e);
        return Err(VerificationError::SubprogError{e});
    }

    if let Err(e) = cfg::check_cfg(prog, &mut env) {
        error!(target: "app", "[Analysis] CFG Error: {}", e);
        return Err(VerificationError::CfgError(e));
    }

    liveness::compute_liveness(prog, &mut env);

    // 2. Initialize Entry State
    let mut initial_state = State::new(entry_dbm, 0);
    initial_state.types.set(Reg::R1, RegType::PtrToCtx);
    initial_state.types.set(Reg::R10, RegType::PtrToStack { offset: Some(0), frame_level: FrameLevel::MAIN });
    init_packet_anchors(&mut initial_state.dbm);

    // 3. Setup Worklist
    let mut worklist = VecDeque::new();
    worklist.push_back(initial_state);

    if config.verbosity >= 1 { 
        info!(target: "app", "[Analysis] Starting Abstract Interpretation..."); 
    }

    // Track pruning statistics
    let mut prune_count: usize = 0;

    // 4. Main Analysis Loop
    while let Some(state) = worklist.pop_back() {
        if env.failed() {
            error!(target: "app", "[Analysis] Aborted due to previous errors.");
            break;
        }

        // Fail immediately if we somehow reach the second half of LD_IMM64
        if prog.invalid_pc_set.contains(&state.pc) {
            env.fail(VerificationError::InvalidBPFLoadImmInsn { pc: state.pc });
            break;
        }

        // A.a TYPE COMPATIBILITY CHECK (safety - may reject program)
        if state.pc < prog.instrs.len() - 1 // No need to check last instruction
            && let Err(e) = merging::check_compatibility(&env, &state) {
            env.fail(e);
            break;
        }

        // A.b PRUNING CHECK (efficiency - may skip this path)
        if pruning::should_prune(&env, &state, config) {
            info!("Pruned state at pc {}", state.pc);
            prune_count += 1;
            continue;
        }

        // A.c RECORD STATE (must come after pruning check, before transfer)
        merging::record_state(&mut env, state.clone());

        // B. Global Complexity Limit (only count non-pruned states)
        env.insn_processed += 1;
        if env.insn_processed > config.max_insn {
            // We use error! with target="analysis" to auto-trigger the crash dump
            error!(target: "analysis", "[Verifier] Hit complexity limit ({} instructions). Aborting.", config.max_insn);
            info!(target: "app", "[Verifier] (Pruned {} states before limit)", prune_count);
            info!(target: "app", "[Verifier] Tip: Try --skip-dbm or --max-insn N to increase limit");
            env.fail(VerificationError::ComplexityLimitExceeded { limit: config.max_insn });
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
        let reg_types_str = state.types.reg_types_str();
        let current_step_idx = Some(
            env.history.record(state.pc, instr, reg_types_str, state.history_idx)
        );
        
        // E. Logging (Delegated to Global Logger)
        // We output the raw data following the protocol. The Logger filters it.
        if config.verbosity >= 2 {
            state.dbm.pretty_print();
        }
        debug!(target: "app", "|PC:{}| Instr: [[{}]]\nRegs: {:?}\nTnums: {:?}\n", 
               state.pc, instr, state.types.reg_types_str(), state.tnums_to_string());
        // debug!(target: "app", "|PC:{}| Instr: [[{}]]\n", 
        //        state.pc, instr);
        // for cf in state.frames.iter() {
        //     println!("{}: {}", cf, cf.stack);
        // }

        // F. Transfer Function
        let successors = transfer::transfer(&mut env, state, instr);

        // G. Critical Failure Check
        if env.failed() {
            // This error! call triggers the RingBufferLogger to dump the last 100 steps
            error!(target: "analysis", "[Verifier] Analysis halted due to critical error: {}", 
                   env.error.as_ref().unwrap().description());
            // Additionally, if we have history tracking, reconstruct and print the crash trace
            if config.enable_path_trace {
                if let Some(crash_idx) = current_step_idx {
                    let trace = env.history.get_trace(crash_idx);
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
        for mut succ in successors.into_iter().rev() {
            succ.history_idx = current_step_idx;
            worklist.push_back(succ);
        }
    }

    // --- FINAL REPORT ---
    if let Some(err) = &env.error {
        info!(target: "app", "\n[Verifier] FAILURE: {}", err.description());
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
                results.push(Dbm::new());
            }
        } else {
            results.push(Dbm::new());
        }
    }

    Ok(results)
}