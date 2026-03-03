use crate::analysis::machine::error::VerificationError;
// src/analysis.rs

pub mod flow;
pub mod machine;
pub mod transfer;

use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::reg::Reg;
use crate::ast::Program;
use crate::common::config::{DomainMode, VerifierConfig};
use crate::domains::dbm::Dbm;
use crate::domains::numeric::NumericDomain;
use crate::pcc::{apply_certificate_aided_refinement, program_hash};
use log::{debug, error, info};
use std::collections::VecDeque;

use self::flow::{cfg, liveness, merging, pruning, subprog};
use self::machine::context::ExecContext;
use self::machine::env::VerifierEnv;
use self::machine::reg_types::RegType;
use self::machine::state::State;

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    config: &VerifierConfig,
) -> Result<Vec<Dbm>, VerificationError> {
    // 1. Initialize Verifier Environment and control flow checks
    let mut env = VerifierEnv::new(ctx, prog, config.certificate.clone());
    if let Some(ref cert) = env.certificate
        && cert.program_hash != program_hash(prog)
    {
        info!(
            target: "app",
            "[PCC] Certificate program hash mismatch; disabling certificate-aided refinement"
        );
        env.certificate = None;
    }

    if config.verbosity >= 1 {
        info!(target: "app", "[Analysis] Running Static Analysis Passes...");
        if config.skip_dbm_check {
            info!(target: "app", "[Analysis] DBM comparison disabled (--skip-dbm)");
        }
    }

    // Check subprograms and stack overflow
    if let Err(e) = subprog::check_subprogs(prog) {
        error!(target: "app", "[Analysis] CFG Error: {}", e);
        return Err(VerificationError::SubprogError { e });
    }

    if let Err(e) = subprog::check_stack_overflow(prog) {
        error!(target: "app", "[Analysis] Stack Error: {}", e);
        return Err(VerificationError::SubprogError { e });
    }

    // Check CFG. This includes checking for unreachable code and marking prune points.
    if let Err(e) = cfg::check_cfg(prog, &mut env, config) {
        error!(target: "app", "[Analysis] CFG Error: {}", e);
        return Err(VerificationError::CfgError(e));
    }

    // Compute liveness information for all registers.
    liveness::compute_liveness(prog, &mut env);

    // 2. Initialize Entry State based on domain mode
    let initial_domain = match config.domain_mode {
        DomainMode::Zone => NumericDomain::Zone(entry_dbm),
        DomainMode::Interval => NumericDomain::new_interval(),
    };
    let mut initial_state = State::new(initial_domain, 0);
    initial_state.types.set(Reg::R1, RegType::PtrToCtx);
    initial_state.types.set(
        Reg::R10,
        RegType::PtrToStack {
            frame_level: FrameLevel::MAIN,
        },
    );
    initial_state.domain.init_packet_anchors();

    // 3. Setup Worklist
    let mut worklist = VecDeque::new();
    worklist.push_back(initial_state);

    if config.verbosity >= 1 {
        info!(target: "app", "[Analysis] Starting Abstract Interpretation...");
    }

    // Track pruning statistics
    let mut prune_count: usize = 0;

    // 4. Main Analysis Loop
    while let Some(mut state) = worklist.pop_back() {
        if env.failed() {
            error!(target: "app", "[Analysis] Aborted due to previous errors.");
            break;
        }

        // Fail immediately if we somehow reach the second half of LD_IMM64
        if prog.invalid_pc_set.contains(&state.pc) {
            env.fail(VerificationError::InvalidBPFLoadImmInsn { pc: state.pc });
            break;
        }

        // A.a TYPE CONFLICT RESOLUTION
        // Demote conflicting registers to ScalarValue.
        // If they're later used as pointers, that will fail.
        if state.pc < prog.instrs.len() - 1 {
            merging::resolve_type_conflicts(&env, &mut state);
        }

        // A.b PRUNING CHECK
        if pruning::should_prune(&env, &mut state, config, prog) {
            info!("Pruned state at pc {}", state.pc);
            prune_count += 1;
            continue;
        }

        // A.c RECORD STATE
        merging::record_state(&mut env, state.clone(), config.max_states_per_pc);

        // B. Global Complexity Limit (only count non-pruned states)
        env.insn_processed += 1;
        if env.insn_processed > config.max_insn {
            // We use error! with target="analysis" to auto-trigger the crash dump
            error!(target: "analysis", "[Verifier] Hit complexity limit ({} instructions). Aborting.", config.max_insn);
            info!(target: "app", "[Verifier] (Pruned {} states before limit)", prune_count);
            info!(target: "app", "[Verifier] Tip: Try --skip-dbm or --max-insn N to increase limit");
            env.fail(VerificationError::ComplexityLimitExceeded {
                limit: config.max_insn,
            });
            break;
        }

        // C. Heartbeat Logging (Level 1+)
        if config.verbosity >= 1 && env.insn_processed.is_multiple_of(config.log_interval) {
            info!(target: "app", "[Verifier] Processed {} instructions (pruned {}). Worklist size: {}", 
                     env.insn_processed, prune_count, worklist.len());
        }

        // D. Instruction Fetch
        if state.pc >= prog.instrs.len() {
            continue;
        }
        let instr = &prog.instrs[state.pc];

        let reg_types_str = state.types.reg_types_str();
        let current_step_idx = Some(env.history.record(
            state.pc,
            instr,
            reg_types_str,
            state.num_frames(),
            state.history_idx,
        ));

        // E. Logging
        if config.verbosity >= 2 {
            state.domain.dump();
        }
        debug!(target: "app", "|PC:{}| Instr: [[{}]]\nRegs: {:?}\nTnums: {:?}\n", 
               state.pc, instr, state.types.reg_types_str(), state.tnums_to_string());

        // F. Transfer Function
        let pre_state = state.clone();
        let mut successors = transfer::transfer(&mut env, state, instr);
        // F.1 Certificate-Aided Refinement (optional)
        // Verifies edge obligations against local transition semantics and
        // applies only sound, narrow refinements to successor states.
        if let Some(ref cert) = env.certificate {
            for succ in &mut successors {
                apply_certificate_aided_refinement(cert, &pre_state, instr, succ);
            }
        }

        // G. Critical Failure Check
        if env.failed() {
            error!(target: "analysis", "[Verifier] Analysis halted due to critical error: {}", 
                   env.error.as_ref().unwrap().description());
            if config.enable_path_trace
                && let Some(crash_idx) = current_step_idx
            {
                let trace = env.history.get_trace(crash_idx);
                // Print directly to stdout (or error log) so it stands out
                println!(
                    "\n=== CRASH PATH RECONSTRUCTION ({} Steps) ===",
                    trace.len()
                );
                for (i, step) in trace.iter().enumerate() {
                    println!(
                        "[{:03}] PC {:<4} | {}\nReg Types: {}",
                        i, step.pc, step.instr_str, step.reg_types_str
                    );
                }
                println!("=============================================\n");
            }
            break;
        }

        // H. Push Successors
        // Prioritize exit-path successors over loop-back successors.
        let mut loop_back = Vec::new();
        let mut other = Vec::new();
        for mut succ in successors.into_iter() {
            succ.history_idx = current_step_idx;
            let is_loop_back = current_step_idx
                .map(|idx| env.history.is_back_edge(idx, succ.pc, succ.num_frames()))
                .unwrap_or(false);
            if is_loop_back {
                loop_back.push(succ);
            } else {
                other.push(succ);
            }
        }
        for succ in loop_back {
            worklist.push_back(succ);
        }
        for succ in other.into_iter().rev() {
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
    // NOTE: For backwards compatibility, we return Vec<Dbm>.
    // In Interval mode, we return empty Dbms since there's no underlying DBM.
    let n = prog.instrs.len();
    let mut results = Vec::with_capacity(n);

    for i in 0..n {
        if let Some(states) = env.explored_states.get(&i) {
            if !states.is_empty() {
                // Extract Dbm from Zone domain, or return empty for Interval
                match &states[0].domain {
                    NumericDomain::Zone(dbm) => results.push(dbm.clone()),
                    NumericDomain::Interval(_) => results.push(Dbm::new()),
                }
            } else {
                results.push(Dbm::new());
            }
        } else {
            results.push(Dbm::new());
        }
    }

    Ok(results)
}
