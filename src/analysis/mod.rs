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
        subprog::check_stack_overflow(
            prog,
            env.ctx.prog_kind,
            config.enable_private_stack
                && match env.ctx.prog_kind {
                    crate::ast::ProgramKind::StructOps => env.ctx.priv_stack_requested,
                    _ => true,
                },
        )
    {
        error!(target: "app", "[Analysis] Stack Error: {}", e);
        return AnalysisResult {
            dbms: vec![],
            explored_states: env.explored_states,
            error: Some(VerificationError::SubprogError { e }),
        };
    }

    // Kernel `check_map_prog_compatibility` (verifier.c L19910): tracing
    // prog kinds (kprobe, tracepoint, raw_tp[_writable], perf_event)
    // cannot use maps whose value record carries bpf_spin_lock,
    // bpf_timer, bpf_list_head, or bpf_rb_root. Socket filter cannot
    // use bpf_spin_lock. Closes the test_helper_restricted FA cluster.
    if let Some(err) = check_map_prog_compatibility(&env) {
        error!(target: "app", "[Analysis] Map/prog incompatibility: {}", err.description());
        return AnalysisResult {
            dbms: vec![],
            explored_states: env.explored_states,
            error: Some(err),
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
    if config.bcf_enabled {
        initial_state.bcf = Some(Box::new(crate::refinement::symbolic::SymbolicState::new()));
    }

    // freplace target inheritance: for `SEC("freplace/<target>")`, the
    // EXT program receives its declared args *directly* in R1..Rn (the
    // extension takes the place of a regular subprog call). Override
    // the default `R1 = PtrToCtx` from above with per-arg typing
    // populated by the runner via `BtfContext::resolve_func_args`. The
    // arg whose type matches the target's ctx struct (`__sk_buff`,
    // `xdp_md`, ...) gets `PtrToCtx`; other pointer args become
    // unknown trusted pointers; scalars become initialized
    // `ScalarValue`. Without this, multi-arg freplace functions like
    // `new_get_skb_ifindex(int val, struct __sk_buff *skb, int var)`
    // hit `R2 !read_ok` at the first `If R2, ...` because R2 was
    // never typed at entry.
    if let Some(args) = ctx.freplace_arg_types.as_ref() {
        use crate::analysis::machine::context::EntryArg;
        use crate::analysis::machine::reg_types::PtrFlags;
        // Reset R1 (default PtrToCtx) before re-typing per declared arg.
        initial_state.types.set(Reg::R1, RegType::NotInit);
        let arg_regs = [Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
        let ctx_struct_for_kind = |kind: ProgramKind| -> Option<&'static str> {
            match kind {
                ProgramKind::SchedCls
                | ProgramKind::SchedAct
                | ProgramKind::SocketFilter
                | ProgramKind::SkSkb
                | ProgramKind::CgroupSkb
                | ProgramKind::FlowDissector => Some("__sk_buff"),
                ProgramKind::Xdp => Some("xdp_md"),
                ProgramKind::SockOps => Some("bpf_sock_ops"),
                ProgramKind::CgroupSockAddr => Some("bpf_sock_addr"),
                ProgramKind::CgroupSockopt => Some("bpf_sockopt"),
                ProgramKind::CgroupSock => Some("bpf_sock"),
                ProgramKind::SkMsg => Some("sk_msg_md"),
                ProgramKind::SkLookup => Some("bpf_sk_lookup"),
                ProgramKind::SkReuseport => Some("sk_reuseport_md"),
                _ => None,
            }
        };
        let ctx_struct = ctx_struct_for_kind(ctx.prog_kind);
        for (i, arg) in args.iter().enumerate().take(arg_regs.len()) {
            let reg = arg_regs[i];
            let ty = match arg {
                EntryArg::Scalar => RegType::ScalarValue,
                EntryArg::TrustedPtrBtfId { type_name, .. } => {
                    if Some(*type_name) == ctx_struct {
                        RegType::PtrToCtx
                    } else {
                        RegType::PtrToBtfId {
                            type_name,
                            flags: PtrFlags::TRUSTED,
                            ref_id: None,
                        }
                    }
                }
                EntryArg::BoundedScalar { .. } => RegType::ScalarValue,
                // freplace doesn't currently emit this; struct_ops uses
                // the BPF_PROG ctx-array idiom, not this R1..Rn path.
                // Map for completeness so the match stays exhaustive.
                EntryArg::TrustedRefcountedTask { ref_id } => RegType::PtrToTask {
                    ref_id: Some(*ref_id),
                },
            };
            initial_state.types.set(reg, ty);
        }
    }

    // Non-sleepable tracing programs (kprobe, tracepoint, raw_tp,
    // perf_event) run with an implicit RCU read-side critical section
    // held by the kernel before invoking the BPF prog. The kernel
    // verifier records this via `env->cur_state->active_rcu_lock` set
    // at program init for those types (verifier.c v6.15 ~L5803 comment
    // "non-sleepable programs and sleepable programs with explicit
    // bpf_rcu_read_lock()"). KF_RCU_PROTECTED iters initialized in
    // such a prog see in_rcu_cs at `_new` time and get MEM_RCU (trusted)
    // slot status. Sleepable variants (`fentry.s`, `iter.s`, `lsm.s`)
    // do NOT auto-hold; they must call `bpf_rcu_read_lock` explicitly.
    use crate::ast::ProgramKind;
    let auto_rcu = matches!(
        env.ctx.prog_kind,
        ProgramKind::Kprobe
            | ProgramKind::Tracepoint
            | ProgramKind::RawTracepoint
            | ProgramKind::RawTracepointWritable
            | ProgramKind::PerfEvent
    );
    if auto_rcu {
        initial_state.rcu_read_lock();
        initial_state.implicit_rcu_at_entry = true;
    }

    // struct_ops subprogs receive their args via the BPF_PROG
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
    // Seed outstanding refs for entry-acquired struct_ops args. Each
    // `EntryArg::TrustedRefcountedTask` carries a pre-allocated ref_id
    // (alloc'd in `struct_ops_entry_args` so the per-arg load site can
    // type the load as `PtrToTask{ref_id: Some(rid)}`); insert each
    // into active_refs so the matching `bpf_task_release(task)`
    // release-path balances out before exit.
    if let Some(args) = ctx.entry_args.as_ref() {
        use crate::analysis::machine::context::EntryArg;
        for arg in args {
            if let EntryArg::TrustedRefcountedTask { ref_id } = arg {
                initial_state.active_refs.insert(*ref_id);
            }
        }
    }

    // 3. & 4. Run worklist analysis
    let prune_count = run_worklist(&mut env, prog, config, initial_state);

    // Audit hook: dump per-PC subsumption-miss histogram.
    // Gated on `ZOVIA_DUMP_PRUNING=1` so it stays out of the sweep
    // path entirely. Used to pinpoint the dominant miss reason on
    // timeout-prone tests — see audit notes in the precision/liveness
    // workstream.
    if std::env::var("ZOVIA_DUMP_PRUNING").ok().as_deref() == Some("1") {
        dump_subsumption_miss_histogram(&env);
    }

    // --- BCF bundle emit ---
    if let Some(path) = config.bcf_bundle_out.as_deref() {
        if !env.bcf_proofs.is_empty() && env.error.is_none() {
            match crate::refinement::bundle::write_bundle(
                std::path::Path::new(path),
                &env.bcf_proofs,
            ) {
                Ok(bytes) => info!(
                    target: "app",
                    "[bcf] wrote bundle: {} ({} entries, {} bytes)",
                    path,
                    env.bcf_proofs.len(),
                    bytes
                ),
                Err(e) => error!(target: "app", "[bcf] bundle write failed ({}): {}", path, e),
            }
        }
    }

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
        subprog::check_stack_overflow(
            prog,
            env.ctx.prog_kind,
            config.enable_private_stack
                && match env.ctx.prog_kind {
                    crate::ast::ProgramKind::StructOps => env.ctx.priv_stack_requested,
                    _ => true,
                },
        )
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

/// Kernel `check_map_prog_compatibility` (verifier.c L19910–L19950):
/// reject the program at load time if any map it references has a
/// record-field that is incompatible with the program type.
///
/// - Tracing prog kinds (kprobe, tracepoint, raw_tp, raw_tp_writable,
///   perf_event) cannot use maps with `bpf_spin_lock`,
///   `bpf_res_spin_lock`, `bpf_timer`, `bpf_list_head`, or `bpf_rb_root`
///   special fields in their value record.
/// - Socket filter cannot use `bpf_spin_lock` / `bpf_res_spin_lock`.
///
/// Maps actually used by this program are derived from `pc_to_reloc`
/// (RelocKind::MapPtr / MapValue), so other progs in the same ELF that
/// reference different maps are unaffected.
fn check_map_prog_compatibility(env: &VerifierEnv) -> Option<VerificationError> {
    use crate::ast::ProgramKind;
    use crate::parsing::btf::SpecialFieldKind;
    use crate::parsing::elf::RelocKind;
    use std::collections::HashSet;

    let kind = env.ctx.prog_kind;
    // `?raw_tp/`, `?tp/`, `?kprobe`, `?perf_event` SECs are intentionally
    // parsed as ProgramKind::Unknown by `from_section` (preserves the
    // current-Unknown kfunc-rejection contract for `?fentry/` / `?fexit/`
    // siblings). The runner stashes the leading SEC token in
    // `attach_flavor` regardless, so we can recover the tracing nature
    // here without altering the global SEC parser.
    let flavor = env.ctx.attach_flavor.as_deref().unwrap_or("");
    let flavor_is_tracing = matches!(
        flavor,
        "kprobe" | "kretprobe" | "tracepoint" | "tp" | "raw_tracepoint"
            | "raw_tp" | "raw_tp.w" | "perf_event"
    );
    let is_tracing = flavor_is_tracing
        || matches!(
            kind,
            ProgramKind::Kprobe
                | ProgramKind::Tracepoint
                | ProgramKind::RawTracepoint
                | ProgramKind::RawTracepointWritable
                | ProgramKind::PerfEvent
        );
    let is_socket_filter = matches!(kind, ProgramKind::SocketFilter) || flavor == "socket";
    if !is_tracing && !is_socket_filter {
        return None;
    }

    let mut used: HashSet<usize> = HashSet::new();
    for reloc in env.ctx.pc_to_reloc.values() {
        if matches!(reloc.kind, RelocKind::MapPtr | RelocKind::MapValue) {
            used.insert(reloc.map_idx);
        }
    }

    for map_idx in used {
        let Some(map_def) = env.ctx.map_defs.get(map_idx) else { continue };
        let Some(btf_id) = map_def.btf_val_type_id else { continue };
        for field in env.ctx.btf.find_special_fields(btf_id) {
            let (rejects_tracing, rejects_socket_filter, name): (bool, bool, &'static str) =
                match field.kind {
                    SpecialFieldKind::SpinLock => (true, true, "bpf_spin_lock"),
                    SpecialFieldKind::ResSpinLock => (true, true, "bpf_res_spin_lock"),
                    SpecialFieldKind::Timer => (true, false, "bpf_timer"),
                    SpecialFieldKind::ListHead => (true, false, "bpf_list_head"),
                    SpecialFieldKind::RbRoot => (true, false, "bpf_rb_root"),
                    _ => continue,
                };
            if (is_tracing && rejects_tracing) || (is_socket_filter && rejects_socket_filter) {
                return Some(VerificationError::MapProgIncompat {
                    map_name: map_def.name.clone(),
                    field: name,
                    kind,
                });
            }
        }
    }
    None
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

    let diag_pcs = crate::analysis::machine::env::diag_pcs();
    let mut diag_arrivals: HashMap<usize, usize> = HashMap::new();

    while let Some(mut state) = worklist.pop_back() {
        // Per-instruction scope for the BCF `detect_conflict_eq`
        // path-unreachable flag: only the instruction that set it (its
        // own transfer) consumes it. Reset here so a set from a
        // helper-arg `check_load` (mem_checks) can't leak forward.
        env.bcf_path_unreachable = false;
        let diag_hit = diag_pcs
            .as_ref()
            .map(|s| s.contains(&state.pc))
            .unwrap_or(false);
        let (diag_r4_pre, diag_r6_pre) = if diag_hit {
            (
                Some(format!("{:?}", state.types.get(Reg::R4))),
                Some(format!("{:?}", state.types.get(Reg::R6))),
            )
        } else {
            (None, None)
        };
        if diag_hit {
            let n = diag_arrivals.entry(state.pc).or_insert(0);
            *n += 1;
            eprintln!(
                "[DIAG ENTER] pc={} arrival#{} frames={} parent_cache={:?}\n  R4={} R6={}\n  Ranges: {}\n  Tnums:  {}",
                state.pc, n, state.num_frames(), state.parent_cache_id,
                diag_r4_pre.as_deref().unwrap_or("?"),
                diag_r6_pre.as_deref().unwrap_or("?"),
                state.reg_ranges_str(),
                state.reg_tnums_compact_str(),
            );
        }
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

        if diag_hit {
            let r4_post = format!("{:?}", state.types.get(Reg::R4));
            let r6_post = format!("{:?}", state.types.get(Reg::R6));
            if Some(&r4_post) != diag_r4_pre.as_ref()
                || Some(&r6_post) != diag_r6_pre.as_ref()
            {
                eprintln!(
                    "[DIAG DEMOTE] pc={} R4: {} -> {}  R6: {} -> {}",
                    state.pc,
                    diag_r4_pre.as_deref().unwrap_or("?"), r4_post,
                    diag_r6_pre.as_deref().unwrap_or("?"), r6_post,
                );
            }
        }

        // A.b PRUNING CHECK
        if pruning::should_prune(env, &mut state, config, prog) {
            if diag_hit {
                eprintln!("[DIAG PRUNE] pc={} pruned=true", state.pc);
            }
            info!("Pruned state at pc {}", state.pc);
            prune_count += 1;
            continue;
        }
        if diag_hit {
            eprintln!("[DIAG PRUNE] pc={} pruned=false (recorded)", state.pc);
        }

        // A.c RECORD STATE
        // Cache the cur state and link the continuing state's parent
        // chain to the just-cached entry. Subsequent path forks
        // inherit this `parent_cache_id` until the next checkpoint.
        let cache_id = merging::record_state(env, state.clone(), config.max_states_per_pc);
        state.parent_cache_id = Some(cache_id);

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
        let diag_cur_pc = state.pc;
        state.domain.set_current_pc(state.pc);
        let mut successors = transfer::transfer(env, state, instr);
        if diag_hit {
            let succ_dump: Vec<String> = successors
                .iter()
                .map(|s| {
                    format!(
                        "pc{}[R4={:?} R6={:?}]",
                        s.pc,
                        s.types.get(Reg::R4),
                        s.types.get(Reg::R6)
                    )
                })
                .collect();
            eprintln!(
                "[DIAG SUCC] pc={} -> [{}]",
                diag_cur_pc,
                succ_dump.join(", ")
            );
        }
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

/// Tiny helper for the audit dump.
fn pct(n: u64, d: u64) -> f64 {
    if d == 0 {
        0.0
    } else {
        (n as f64 / d as f64) * 100.0
    }
}

/// Audit dump: per-PC subsumption-miss histogram + global totals.
/// Triggered by `ZOVIA_DUMP_PRUNING=1`. Output goes to stderr (so it
/// doesn't tangle with verifier stdout when piping). Format is
/// hand-rolled tabular text — the consumer is a human reading one
/// test's audit output, not a machine.
fn dump_subsumption_miss_histogram(env: &VerifierEnv) {
    use crate::analysis::machine::env::SubsumptionMissReason;

    // Global totals across all PCs.
    let mut global = [0u64; 9];
    for buckets in env.subsumption_misses.values() {
        for i in 0..9 {
            global[i] = global[i].saturating_add(buckets[i]);
        }
    }
    let total_misses: u64 = global.iter().sum();

    // Use the lifetime counters, NOT `state_metrics.hit_cnt`. The
    // per-state hit/miss counters disappear when the state is evicted
    // by `record_state`'s max_states_per_pc drain (cap = 8 by
    // default), so reading them at end-of-run undercounts wildly on
    // workloads with > 8 distinct cached states per PC.
    let total_hits: u64 = env.pruning_stats.lifetime_hits;
    let total_misses_lifetime: u64 = env.pruning_stats.lifetime_misses;
    let _ = env.state_metrics.values().flatten().count(); // keep import path used
    let total_cached: u64 = env
        .state_metrics
        .values()
        .map(|v| v.len() as u64)
        .sum();
    let n_pcs = env.subsumption_misses.len();

    let ps = &env.pruning_stats;
    eprintln!("\n=== ZOVIA pruning audit ===");
    eprintln!(
        "  insn_processed: {}    distinct PCs cached: {}    total cached states: {}",
        env.insn_processed,
        env.explored_states.len(),
        total_cached
    );
    eprintln!(
        "  should_prune calls: {}",
        ps.should_prune_calls
    );
    eprintln!(
        "    not a prune point:    {:>10}  ({:>5.1}%)",
        ps.not_prune_point,
        pct(ps.not_prune_point, ps.should_prune_calls)
    );
    eprintln!(
        "    on-path re-entry:     {:>10}  ({:>5.1}%)",
        ps.on_path_skip,
        pct(ps.on_path_skip, ps.should_prune_calls)
    );
    eprintln!(
        "    no prev states (1st): {:>10}  ({:>5.1}%)",
        ps.no_prev_states,
        pct(ps.no_prev_states, ps.should_prune_calls)
    );
    eprintln!(
        "    standard subsumption: {:>10}  ({:>5.1}%)",
        ps.std_pruning_calls,
        pct(ps.std_pruning_calls, ps.should_prune_calls)
    );
    eprintln!(
        "    loop subsumption:     {:>10}  ({:>5.1}%)",
        ps.loop_pruning_calls,
        pct(ps.loop_pruning_calls, ps.should_prune_calls)
    );
    eprintln!(
        "      of which bailed (no_cond_exit):    {} ({:.1}% of loop calls)",
        ps.loop_no_cond_exit,
        pct(ps.loop_no_cond_exit, ps.loop_pruning_calls)
    );
    eprintln!(
        "      of which actually walked prev_states: {}",
        ps.loop_walks_attempted
    );
    eprintln!(
        "        no_prev / hit / miss / convergence-pruned: {} / {} / {} / {}",
        ps.loop_walks_no_prev,
        ps.loop_walks_hit,
        ps.loop_walks_miss,
        ps.loop_walks_pruned_via_convergence,
    );
    eprintln!(
        "    may_goto RANGE_WITHIN hits: {}",
        ps.may_goto_range_within_hits
    );
    eprintln!(
        "  cache hits: {total_hits}    cache misses: {total_misses_lifetime} (per-reason histogram below sums to {total_misses})    miss-PCs: {n_pcs}"
    );
    eprintln!("  miss reasons (first-rejecting check, % of total misses):");
    let mut ranked: Vec<(SubsumptionMissReason, u64)> = SubsumptionMissReason::ALL
        .iter()
        .map(|&r| (r, global[r.idx()]))
        .collect();
    ranked.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
    let denom = total_misses.max(1) as f64;
    for (r, c) in &ranked {
        eprintln!(
            "    {:>16}  {:>10}   ({:>5.1}%)",
            r.label(),
            c,
            (*c as f64 / denom) * 100.0
        );
    }

    // Top-5 PCs by miss count, with their per-PC reason breakdown.
    let mut by_pc: Vec<(usize, u64, [u64; 9])> = env
        .subsumption_misses
        .iter()
        .map(|(&pc, buckets)| (pc, buckets.iter().sum::<u64>(), *buckets))
        .collect();
    by_pc.sort_by_key(|(_, total, _)| std::cmp::Reverse(*total));
    eprintln!("  top PCs by miss count:");
    for (pc, total, buckets) in by_pc.iter().take(8) {
        let dom = SubsumptionMissReason::ALL
            .iter()
            .max_by_key(|r| buckets[r.idx()])
            .unwrap();
        let dom_share = buckets[dom.idx()] as f64 / (*total as f64).max(1.0) * 100.0;
        let cached_at_pc = env
            .state_metrics
            .get(pc)
            .map(|v| v.len())
            .unwrap_or(0);
        eprintln!(
            "    pc={pc:<5}  misses={total:<8}  cached={cached_at_pc:<3}  dominant={} ({:.0}%)",
            dom.label(),
            dom_share
        );
    }
    eprintln!();
}
