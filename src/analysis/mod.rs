use crate::analysis::machine::error::VerificationError;
// src/analysis.rs

pub mod flow;
pub mod machine;
pub mod transfer;

use crate::analysis::machine::frame_stack::FrameLevel;
use crate::analysis::machine::reg::Reg;
use crate::ast::{Instr, Program};
use crate::common::config::{DomainMode, VerifierConfig};
use crate::domains::dbm::Dbm;
use crate::domains::numeric::NumericDomain;
use crate::pcc::{
    apply_verified_refinements, check_proof, program_hash, validate_certificate_for_program,
};
use log::{debug, error, info};
use std::collections::{HashMap, VecDeque};

use self::flow::{cfg, liveness, merging, pruning, scc, subprog};
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

    // Compute SCCs over the CFG. Annotates `insn_aux_data[pc].scc_id`
    // (1+ for multi-vertex SCCs / singletons-with-self-edge, 0
    // otherwise — kernel convention from `compute_scc`,
    // verifier.c v6.15 L25809). Read by `maybe_enter_scc` /
    // `maybe_exit_scc` / `add_scc_backedge` / `incomplete_read_marks`
    // to drive SCC-scoped backedge precision propagation.
    scc::compute_scc(prog, &mut env);

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
    if std::env::var("ZOVIA_DUMP_VISITS").ok().as_deref() == Some("1") {
        dump_pc_visit_count(&env);
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
        // Per-path counter bump for the kernel-engine sparse-cache
        // heuristic (`ZOVIA_KERNEL_ENGINE=1`). Counts THIS path's
        // progress (not env-wide), so worklist interleaving doesn't
        // pollute the deltas with other paths' work.
        state.path_insn_count = state.path_insn_count.saturating_add(1);
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

        // Audit probe: dump compact state at the requested PC(s). Gated on
        // `ZOVIA_DUMP_STATES_AT_PC=N[,M,...]`. Used to inspect why many
        // "equivalent" states accumulate at a single pc (path-explosion
        // diagnostic). Comma-separated list, e.g.
        // `ZOVIA_DUMP_STATES_AT_PC=1587,1856`. Each line includes R0..R9 +
        // their precision marks + a few key stack slot scalars so we can
        // compare what changes across visits to a loop head.
        if let Ok(s) = std::env::var("ZOVIA_DUMP_STATES_AT_PC") {
            let targets: Vec<usize> = s
                .split(',')
                .filter_map(|t| t.trim().parse::<usize>().ok())
                .collect();
            if targets.iter().any(|&t| t == state.pc) {
                use crate::analysis::machine::reg_types::RegType;
                let mut row = format!("pc={} ", state.pc);
                for r in [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5,
                          Reg::R6, Reg::R7, Reg::R8, Reg::R9] {
                    let ty = state.types.get(r);
                    let (ilo, ihi) = state.domain.get_interval(r);
                    let sid = state.scalar_ids.get(&r).copied().unwrap_or(0);
                    let p = if state.precise_regs.contains(&r) { "P" } else { "_" };
                    // Compact-print: SV[lo..hi]sid=N {P|_}  for scalars,
                    // or ptr-type tag for pointers.
                    let tag = match ty {
                        RegType::ScalarValue => format!("SV[{}..{}]", ilo, ihi),
                        RegType::PtrToMapValue { offset, map_idx, .. } => {
                            format!("MV(m{},off={:?})", map_idx, offset)
                        }
                        RegType::PtrToCtx => "Ctx".into(),
                        RegType::PtrToStack { .. } => format!("Stk[{}..{}]", ilo, ihi),
                        RegType::PtrToPacket => "Pkt".into(),
                        RegType::PtrToPacketEnd => "PktEnd".into(),
                        RegType::NotInit => "NI".into(),
                        _ => format!("{:?}", ty),
                    };
                    let r_index = (r as u8).saturating_sub(1);
                    row.push_str(&format!(
                        "r{}={}{}sid={} ",
                        r_index, tag, p, sid,
                    ));
                }
                // Append the top frame's spilled scalar slots (off, bounds,
                // precise) up to ~10 most-recent for sanity. We're interested
                // in fp-336 (proto-byte spill) and fp-400 in particular.
                let frame = state.frames.current();
                let mut slot_keys: Vec<i16> = frame.stack.slot_offsets().into_iter().collect();
                slot_keys.sort();
                let mut sn = 0;
                for off in slot_keys.iter().rev() {
                    let Some(slot) = frame.stack.slots.get(off) else { continue; };
                    if !matches!(slot.reg_type, RegType::ScalarValue) {
                        continue;
                    }
                    row.push_str(&format!(
                        "fp{}=SV[{}..{}]sid={}{} ",
                        off, slot.bounds.min, slot.bounds.max,
                        slot.scalar_id.unwrap_or(0),
                        if slot.precise { "P" } else { "_" },
                    ));
                    sn += 1;
                    if sn >= 8 { break; }
                }
                eprintln!("[STATE@PC] {}", row);
            }
        }

        // A.b PRUNING CHECK
        if pruning::should_prune(env, &mut state, config, prog) {
            if diag_hit {
                eprintln!("[DIAG PRUNE] pc={} pruned=true", state.pc);
            }
            info!("Pruned state at pc {}", state.pc);
            prune_count += 1;
            // SCC: this DFS path is done (subsumed by a cached state).
            // Decrement parent.branches up the chain; if a parent's
            // branches hits 0 propagate its loop_entry to its parent.
            env.complete_dfs_branch(state.parent_cache_id);
            continue;
        }
        if diag_hit {
            eprintln!("[DIAG PRUNE] pc={} pruned=false (recorded)", state.pc);
        }

        // A.c RECORD STATE — kernel-faithful `is_state_visited` shape.
        // Gated by `ZOVIA_KERNEL_ENGINE=1`. Two kernel-shape gates layered:
        //   (1) Outer: cache only at PRUNE POINTS (kernel `do_check` only
        //       calls `is_state_visited` when is_prune_point fires).
        //       zovia's dense default mode caches at EVERY popped state;
        //       that produces a parent_cache_id chain with consecutive-pc
        //       deltas the kernel never has. Gate fixes that.
        //   (2) Inner: `add_new_state` heuristic (verifier.c v6.15
        //       L18998-L19013): force_new_state || (jmps_delta>=2 &&
        //       insns_delta>=8). Counters are PER-PATH on State.
        let kernel_engine =
            std::env::var("ZOVIA_KERNEL_ENGINE").ok().as_deref() == Some("1");
        let at_prune_point = pruning::widening::is_prune_point(env, state.pc);
        let insn_aux_force = env
            .insn_aux_data
            .get(state.pc)
            .map(|a| a.force_checkpoint)
            .unwrap_or(false);
        // Kernel L18999-L19013 uses ENV-WIDE counters. But zovia's
        // worklist interleaves paths, so env-wide deltas are noisy:
        // they can be inflated (other paths' work) OR understated
        // (after a cache event, the same path may re-pop with no
        // env increment between). Neither alone exactly matches the
        // kernel's linear-DFS env behavior. Solution: OR env-wide
        // and per-path heuristics — fire if EITHER triggers. This
        // produces a SUPERSET cache pattern (more entries than
        // either alone), maximising bundle coverage. The kernel
        // matches by HASH; extra entries are ignored.
        let env_jmps_delta = env
            .jmps_processed
            .saturating_sub(env.prev_jmps_processed);
        let env_insns_delta = env
            .insn_processed
            .saturating_sub(env.prev_insn_processed);
        let path_jmps_delta = state
            .path_jmp_count
            .saturating_sub(state.prev_jmp_at_cache);
        let path_insns_delta = state
            .path_insn_count
            .saturating_sub(state.prev_insn_at_cache);
        // Kernel L18998-L19000: long-history safety valve. Fire when
        // either env-wide or per-path window > 40 insns since last
        // cache event.
        let long_history = env_insns_delta > 40 || path_insns_delta > 40;
        let force_new_state = insn_aux_force || long_history;
        let env_heuristic =
            env_jmps_delta >= 2 && env_insns_delta >= 8;
        let path_heuristic =
            path_jmps_delta >= 2 && path_insns_delta >= 8;
        let outer_gate = !kernel_engine || at_prune_point;
        let add_new_state = !kernel_engine
            || force_new_state
            || env_heuristic
            || path_heuristic;
        if outer_gate && add_new_state {
            let cache_id =
                merging::record_state(env, state.clone(), config.max_states_per_pc);
            state.parent_cache_id = Some(cache_id);
            env.prev_jmps_processed = env.jmps_processed;
            env.prev_insn_processed = env.insn_processed;
            state.prev_jmp_at_cache = state.path_jmp_count;
            state.prev_insn_at_cache = state.path_insn_count;
        }

        // B. Global Complexity Limit (only count non-pruned states)
        env.insn_processed += 1;
        // Per-PC visit counter (audit hook, ZOVIA_DUMP_VISITS=1). Bumped
        // ONLY on non-pruned expansions so the count reflects state
        // expansions per pc, comparable to the kernel verifier's
        // per-insn visit count in the log_level-2 trace.
        if std::env::var("ZOVIA_DUMP_VISITS").ok().as_deref() == Some("1") {
            *env.pc_visit_count.entry(state.pc).or_insert(0) += 1;
        }
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
        // The reject insn's own breadcrumb — the reactive
        // path-unreachable discharge's `bcf_suffix_base_pc` walk must
        // start here (kernel `backtrack_states` `last_idx =
        // cur->insn_idx`, skip_first), not from the in-flight state's
        // parent `history_idx`.
        env.current_step_idx = current_step_idx;

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
        // SCC: save fields needed after `state` is moved into transfer.
        let cur_dfs_depth = state.dfs_depth;
        let cur_parent_cache_id = state.parent_cache_id;
        state.domain.set_current_pc(state.pc);
        // Kernel `env->jmps_processed++` (verifier.c L19553): bump on
        // JMP-class insn for the add_new_state sparse-cache heuristic.
        // Bumped on BOTH env-wide and per-path counters; the heuristic
        // uses the per-path one. The env-wide field stays for any
        // downstream consumer that wants the cumulative figure.
        let is_jmp_class = matches!(
            instr,
            Instr::If { .. } | Instr::Jmp { .. } | Instr::MayGoto { .. }
                | Instr::Call { .. } | Instr::CallRel { .. } | Instr::Exit
        );
        if is_jmp_class {
            env.jmps_processed += 1;
            state.path_jmp_count = state.path_jmp_count.saturating_add(1);
        }
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
        let succ_count = successors.len();
        for mut succ in successors.into_iter() {
            succ.history_idx = current_step_idx;
            // SCC: child inherits its DFS depth from parent + 1, and its
            // initial branches=1 (this one in-flight path through succ).
            // The parent's branches gets bumped once per pushed successor
            // below.
            succ.dfs_depth = cur_dfs_depth.saturating_add(1);
            succ.branches = 1;
            let is_loop_back = current_step_idx
                .map(|idx| env.history.is_back_edge(idx, succ.pc, succ.num_frames()))
                .unwrap_or(false);
            if is_loop_back {
                loop_back.push(succ);
            } else {
                other.push(succ);
            }
        }
        // SCC: bump parent.branches once per pushed successor (kernel
        // `push_stack` L2045). state.parent_cache_id is the just-recorded
        // cache_id at this pc (set at A.c above), so each successor is a
        // new in-flight DFS path through it.
        //
        // ALSO bump parent.dfs_paths kernel-faithfully: only by
        // (succ_count - 1), because the kernel's push_stack is invoked
        // once per ALT — i.e. once per fork-extra, NOT per total
        // successor. The cur continuation is already counted by
        // dfs_paths=1 at cache creation. Linear chains (succ_count==1)
        // get no bump. This is the load-bearing signal for the inf-loop
        // trap gate (`prev.dfs_paths == 0` skip).
        if succ_count > 0
            && let Some(pcid) = cur_parent_cache_id
            && let Some(&(ppc, pidx)) = env.cache_loc_by_id.get(&pcid)
            && let Some(p) = env.explored_states.get_mut(&ppc).and_then(|v| v.get_mut(pidx))
        {
            p.branches = p.branches.saturating_add(succ_count as u32);
            if succ_count > 1 {
                p.dfs_paths = p.dfs_paths.saturating_add((succ_count - 1) as u32);
            }
        }
        if succ_count == 0 {
            // No successors (e.g. Exit): this DFS path terminated.
            // Decrement parent chain analogously to the prune-hit path.
            env.complete_dfs_branch(cur_parent_cache_id);
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

/// Audit dump: per-PC non-pruned state-expansion count.
/// Triggered by `ZOVIA_DUMP_VISITS=1`. Used to localize path-explosion
/// hotspots by diffing against the kernel verifier's per-PC visit
/// count from the log_level-2 trace (`<pc>: (...) <insn>` lines).
fn dump_pc_visit_count(env: &VerifierEnv) {
    let mut pairs: Vec<(usize, u64)> =
        env.pc_visit_count.iter().map(|(&pc, &n)| (pc, n)).collect();
    pairs.sort_by_key(|&(_, n)| std::cmp::Reverse(n));
    eprintln!("\n=== ZOVIA per-PC visit count (non-pruned expansions) ===");
    eprintln!("  total expansions: {}    distinct pcs: {}", env.insn_processed, pairs.len());
    eprintln!("  top 100 pcs by visit count:");
    for (pc, n) in pairs.iter().take(100) {
        eprintln!("    pc={:<5} visits={}", pc, n);
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
        "    children_unsafe skips:    {:>10}    ← BCF-discharge cache invalidations",
        ps.children_unsafe_skips
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
