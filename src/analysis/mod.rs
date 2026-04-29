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
use crate::pcc::{
    apply_verified_refinements, check_proof, program_hash, validate_certificate_for_program,
};
use log::{debug, error, info};
use std::collections::{HashMap, VecDeque};

use self::flow::{cfg, liveness, merging, pruning, subprog};
use self::machine::context::ExecContext;
use self::machine::env::VerifierEnv;
use self::machine::reg_types::RegType;
use self::machine::state::State;

/// Analysis results including both the DBM vector and the explored states.
pub struct AnalysisResult {
    pub dbms: Vec<Dbm>,
    pub explored_states: HashMap<usize, Vec<State>>,
    /// If analysis failed, the error is stored here. The explored_states are
    /// still populated with all states collected before the failure point.
    pub error: Option<VerificationError>,
}

pub fn analyze_program(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    config: &VerifierConfig,
) -> Result<Vec<Dbm>, VerificationError> {
    let r = analyze_program_full(ctx, prog, entry_dbm, config);
    if let Some(err) = r.error {
        Err(err)
    } else {
        Ok(r.dbms)
    }
}

/// Like `analyze_program`, but always returns explored states (even on failure).
/// Used by the PCC certificate generator which needs interval states at PCs
/// before the failure point.
pub fn analyze_program_full(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    config: &VerifierConfig,
) -> AnalysisResult {
    // 1. Initialize Verifier Environment and control flow checks
    let mut env = VerifierEnv::new(ctx, prog, config.certificate.clone());
    if let Some(ref cert) = env.certificate {
        let computed_hash = program_hash(prog);
        if cert.program_hash != computed_hash {
            info!(
                target: "app",
                "[PCC] Certificate program hash mismatch (cert={}, program={}); disabling certificate-aided refinement",
                cert.program_hash,
                computed_hash
            );
            env.certificate = None;
        } else if let Err(e) = validate_certificate_for_program(cert, prog) {
            info!(
                target: "app",
                "[PCC] Certificate validation failed ({}); disabling certificate-aided refinement",
                e
            );
            env.certificate = None;
        } else {
            let pcs: Vec<String> = cert
                .pc_annotations
                .iter()
                .map(|a| a.pc.to_string())
                .collect();
            info!(
                target: "app",
                "[PCC] Certificate accepted: v{}, hash={}, {} annotation(s) at PC(s): [{}]",
                cert.version,
                cert.program_hash,
                cert.pc_annotations.len(),
                pcs.join(", "),
            );
        }
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
        return AnalysisResult {
            dbms: vec![],
            explored_states: env.explored_states,
            error: Some(VerificationError::SubprogError { e }),
        };
    }

    if let Err(e) =
        subprog::check_stack_overflow(prog, env.ctx.prog_kind, config.enable_private_stack)
    {
        error!(target: "app", "[Analysis] Stack Error: {}", e);
        return AnalysisResult {
            dbms: vec![],
            explored_states: env.explored_states,
            error: Some(VerificationError::SubprogError { e }),
        };
    }

    // Check CFG. This includes checking for unreachable code and marking prune points.
    if let Err(e) = cfg::check_cfg(prog, &mut env, config) {
        error!(target: "app", "[Analysis] CFG Error: {}", e);
        return AnalysisResult {
            dbms: vec![],
            explored_states: env.explored_states,
            error: Some(VerificationError::CfgError(e)),
        };
    }

    // Compute liveness information for all registers.
    liveness::compute_liveness(prog, &mut env);

    // 2. Initialize Entry State based on domain mode
    let pcc_mode = config.certificate_output.is_some()
        || config.certificate_input.is_some()
        || config.certificate.is_some();

    let initial_domain = match config.domain_mode {
        DomainMode::Zone => {
            let mut dbm = entry_dbm;
            if pcc_mode {
                dbm.enable_provenance();
            }
            NumericDomain::Zone(dbm)
        }
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

    // W6.4a: struct_ops subprogs receive their args via the BPF_PROG
    // macro's ctx-array idiom — R1 stays as PtrToCtx (a `u64 *ctx`), and
    // each declared arg is unpacked at runtime via `*(u64 *)(ctx + 8*i)`.
    // The per-arg typing happens inside `validate_ctx_access` (see
    // src/common/ctx_model.rs), which consumes `ctx.entry_args` to type
    // the loaded values. No R1..Rn override is needed here.
    //
    // For struct_ops members declared with `__ref` parameters (the kmod
    // marks the arg as ref-acquired at entry — e.g.
    // bpf_testmod_ops.test_refcounted's `task__ref`), seed an outstanding
    // reference per refcounted arg. The kernel reports "Unreleased
    // reference id=N alloc_insn=0" if the program exits without releasing
    // it; here, `state.has_unreleased_refs()` at exit fires
    // `UnreleasedReference`. Programs that load the arg from ctx and call
    // the matching release kfunc (e.g. `bpf_task_release`) drop the ref
    // through the existing release path. The arg-position-to-ref-id
    // binding isn't propagated to the loaded register here; that would be
    // needed to type the loaded ctx slot as a refcounted PtrToTask, which
    // we leave for a follow-up if a corresponding success-case test
    // surfaces as a false-reject.
    for _ in 0..ctx.struct_ops_refcounted_args {
        initial_state.acquire_ref();
    }

    // 3. & 4. Run worklist analysis
    let prune_count = run_worklist(&mut env, prog, config, initial_state);

    // --- FINAL REPORT ---
    let analysis_error = if let Some(err) = &env.error {
        info!(target: "app", "\n[Verifier] FAILURE: {}", err.description());
        if config.verbosity >= 1 {
            info!(target: "app", "[Analysis] Finished. Total Steps: {}, Pruned: {}", env.insn_processed, prune_count);
        }
        Some(err.clone())
    } else {
        info!(target: "app", "\n[Verifier] Success! Verified {} instructions (pruned {} states).",
                 env.insn_processed, prune_count);
        if config.verbosity >= 1 {
            info!(target: "app", "[Analysis] Finished. Total Steps: {}, Pruned: {}", env.insn_processed, prune_count);
        }
        None
    };

    // 5. Return Results
    // NOTE: For backwards compatibility, dbms returns Vec<Dbm>.
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

    AnalysisResult {
        dbms: results,
        explored_states: env.explored_states,
        error: analysis_error,
    }
}

/// Verify the body of an `__exception_cb` callback subprog.
///
/// The cb is unreachable from main's CFG (registered via BTF decl_tag,
/// not called) so the main analysis pass never visits it. The kernel
/// handles this by force-marking the cb subprog as `called` in
/// `do_check_subprogs`, which routes it through the normal global-subprog
/// verification path. We don't have an equivalent global-subprog loop, so
/// this function plays that role: build a fresh env, seed the cb's entry
/// state (R1 = unknown SCALAR cookie, R10 = stack pointer), and run the
/// worklist.
///
/// While the env's `analyzing_exception_cb` flag is set, `transfer_exit`
/// applies the kernel's exception-cb-specific exit rule — for fentry/
/// fexit programs, R0 must be in [0, 0] at cb exit (mirrors the kernel
/// applying the main-program exit rule via `in_exception_callback_fn`).
///
/// Returns `Some(error)` if verification of the cb body fails; `None` on
/// success. Caller is expected to surface the error as the parent
/// program's failure verdict.
pub fn analyze_exception_cb(
    ctx: &ExecContext,
    prog: &Program,
    entry_dbm: Dbm,
    config: &VerifierConfig,
    cb_entry_pc: usize,
) -> Option<VerificationError> {
    let mut env = VerifierEnv::new(ctx, prog, None);
    env.analyzing_exception_cb = true;

    // Reuse program-level structural checks. These are idempotent — main
    // analysis already ran them, but `env` is fresh here so we need its
    // insn_aux_data populated (prune points, liveness) before the
    // worklist body can run safely.
    if let Err(e) = subprog::check_subprogs(prog) {
        return Some(VerificationError::SubprogError { e });
    }
    if let Err(e) =
        subprog::check_stack_overflow(prog, env.ctx.prog_kind, config.enable_private_stack)
    {
        return Some(VerificationError::SubprogError { e });
    }
    if let Err(e) = cfg::check_cfg(prog, &mut env, config) {
        return Some(VerificationError::CfgError(e));
    }
    liveness::compute_liveness(prog, &mut env);

    // Seed initial state at the cb's entry PC. The kernel's
    // `btf_prepare_func_args` produces ARG_ANYTHING for the cookie arg;
    // we mirror that with R1 = SCALAR with no interval bounds.
    let initial_domain = match config.domain_mode {
        DomainMode::Zone => NumericDomain::Zone(entry_dbm),
        DomainMode::Interval => NumericDomain::new_interval(),
    };
    let mut initial_state = State::new(initial_domain, cb_entry_pc);
    initial_state.types.set(Reg::R1, RegType::ScalarValue);
    initial_state.types.set(
        Reg::R10,
        RegType::PtrToStack {
            frame_level: FrameLevel::MAIN,
        },
    );
    initial_state.domain.init_packet_anchors();

    let _ = run_worklist(&mut env, prog, config, initial_state);

    env.error
}

/// Worklist abstract-interpretation loop. Shared between the main-program
/// analysis (`analyze_program_full`) and the exception-cb body pass
/// (`analyze_exception_cb`). Returns the number of states pruned.
fn run_worklist(
    env: &mut VerifierEnv,
    prog: &Program,
    config: &VerifierConfig,
    initial_state: State,
) -> usize {
    let mut worklist = VecDeque::new();
    worklist.push_back(initial_state);

    if config.verbosity >= 1 {
        info!(target: "app", "[Analysis] Starting Abstract Interpretation...");
    }

    let mut prune_count: usize = 0;

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
        merging::record_state(env, state.clone(), config.max_states_per_pc);

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
        let reg_ranges_str = state.reg_ranges_str();
        let current_step_idx = Some(env.history.record(
            state.pc,
            instr,
            reg_types_str,
            reg_ranges_str,
            state.num_frames(),
            state.history_idx,
        ));

        // E. Logging
        if config.verbosity >= 3 {
            // Full DBM matrix — only at highest verbosity to avoid flooding logs.
            // The structured Ranges/Zone/Tnums lines below (v>=2) are logged first;
            // the matrix adds the raw cell values for deep debugging.
            let matrix = state.domain.matrix_full_str();
            if !matrix.is_empty() {
                debug!(target: "app", "[DBM@PC:{}]\n{}", state.pc, matrix);
            }
        }
        if config.verbosity >= 2 || config.debug_pc == Some(state.pc) {
            let ranges = state.reg_ranges_str();
            let rel    = state.domain.relations_str();
            let tnums  = state.reg_tnums_compact_str();

            let rel_line = if rel.is_empty() {
                String::new()
            } else {
                format!("\n  Rel:    {}", rel)
            };
            let tnum_line = if tnums.is_empty() {
                String::new()
            } else {
                format!("\n  Tnums:  {}", tnums)
            };

            debug!(target: "app",
                "[PC:{}] {}\n  Types:  {}\n  Ranges: {}{}{}",
                state.pc, instr,
                state.types.reg_types_str(),
                ranges, rel_line, tnum_line
            );
        }

        // F. Transfer Function
        state.domain.set_current_pc(state.pc);
        let mut successors = transfer::transfer(env, state, instr);
        // F.1 Certificate-Aided Refinement (optional)
        // Replay-verify proof chains for each successor PC using explored_states.
        if let Some(ref cert) = env.certificate {
            for succ in &mut successors {
                let succ_pc = succ.pc;
                let mut verified = Vec::new();
                for ann in &cert.pc_annotations {
                    if ann.pc != succ_pc {
                        continue;
                    }
                    for entry in &ann.entries {
                        if let Some(v) =
                            check_proof(entry, ann.pc, &env.explored_states, prog)
                        {
                            verified.push(v);
                        }
                    }
                }
                apply_verified_refinements(succ, &verified);
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
                        "[{:03}] PC {:<4} | {}\n       Types:  {}\n       Ranges: {}",
                        i, step.pc, step.instr_str,
                        step.reg_types_str,
                        step.reg_ranges_str,
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

    prune_count
}
