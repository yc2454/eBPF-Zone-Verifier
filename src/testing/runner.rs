// src/runner.rs

use crate::analysis;
use crate::analysis::machine::context::{
    EntryArg, default_exec_ctx, intern_btf_type_name, intern_btf_type_name_strict,
};
use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::ast::ProgramKind;
use crate::common::config::VerifierConfig;
use crate::domains::dbm::Dbm;
use crate::domains::domain::assign_zero;
use crate::parsing::btf::{self, BtfContext, StructOpsArg};
use crate::parsing::elf;
use crate::parsing::elf::struct_ops::{StructOpsBinding, extract_bindings};
use crate::parsing::elf::{
    BpfFuncInfo, BpfMapDef, get_functions_in_section, list_section_names, load_data_section_maps,
    load_maps, load_raw_programs, load_relocations_for_function,
};
use crate::parsing::elf::{
    program_kind_for_object, try_load_combined_program_from_elf, try_load_function_from_elf,
    try_load_function_with_subprogs_from_elf,
    try_load_program_from_elf,
};
use std::path::Path;

/// W6.4c: per-(ops_struct, member, arg_idx) PTR_MAYBE_NULL table.
/// See doc comment on `Analyzer::struct_ops_entry_args` for sourcing.
const STRUCT_OPS_MAYBE_NULL_ARGS: &[(&str, &str, u8)] = &[
    ("sched_ext_ops", "dispatch", 1), // prev
    ("sched_ext_ops", "yield", 1),    // to
];

fn is_struct_ops_arg_maybe_null(ops_struct: &str, member: &str, arg_idx: u8) -> bool {
    STRUCT_OPS_MAYBE_NULL_ARGS
        .iter()
        .any(|(s, m, i)| *s == ops_struct && *m == member && *i == arg_idx)
}

/// Per-(ops_struct, member, arg_idx) refcounted-arg table. The kernel
/// marks struct_ops member parameters as "ref-acquired at entry" via the
/// `__ref` suffix on the kmod-side parameter name (e.g.
/// `bpf_testmod_ops__test_refcounted(int dummy, struct task_struct *task__ref)`).
/// That suffix lives in the kmod's BTF — not in the BPF program's BTF —
/// so we mirror it here as a static table, the same way
/// STRUCT_OPS_MAYBE_NULL_ARGS mirrors per-arg PTR_MAYBE_NULL.
///
/// The verifier acquires a ref at function entry for each refcounted arg;
/// failure to release it before exit fires UnreleasedReference, matching
/// the kernel's "Unreleased reference id=N alloc_insn=0" rejection on
/// programs like struct_ops_refcounted_fail__ref_leak.
const STRUCT_OPS_REFCOUNTED_ARGS: &[(&str, &str, u8)] = &[
    ("bpf_testmod_ops", "test_refcounted", 1),     // task__ref
    ("bpf_testmod_ops", "test_return_ref_kptr", 1), // task__ref
];

fn is_struct_ops_arg_refcounted(ops_struct: &str, member: &str, arg_idx: u8) -> bool {
    STRUCT_OPS_REFCOUNTED_ARGS
        .iter()
        .any(|(s, m, i)| *s == ops_struct && *m == member && *i == arg_idx)
}

/// Per-(ops_struct, member) table of struct_ops members the kernel module
/// marks unsupported for BPF attach. The kmod's `bpf_struct_ops` registration
/// validates this via `bpf_struct_ops_check_member`/`check_member` callbacks
/// and per-struct allowlists. Without inspecting the kmod we mirror the
/// known-unsupported entries here, matching the kernel's
/// "attach to unsupported member <member> of struct <ops_struct>" rejection.
const UNSUPPORTED_STRUCT_OPS_MEMBERS: &[(&str, &str)] = &[
    ("bpf_testmod_ops", "unsupported_ops"),
];

fn is_unsupported_struct_ops_member(ops_struct: &str, member: &str) -> bool {
    UNSUPPORTED_STRUCT_OPS_MEMBERS
        .iter()
        .any(|(s, m)| *s == ops_struct && *m == member)
}

/// Number of refcounted args declared on this subprog's struct_ops binding.
/// Returns 0 when the subprog has no struct_ops binding or none of its
/// args are refcounted. Consumed by `analyze_program_full` to seed
/// `state.active_refs` at function entry — every refcounted arg becomes
/// an outstanding reference the program must release before exit.
pub(crate) fn struct_ops_refcounted_arg_count(
    bindings: &[StructOpsBinding],
    func_name: &str,
) -> usize {
    let Some(binding) = bindings.iter().find(|b| b.subprog == func_name) else {
        return 0;
    };
    let mut n = 0;
    // The arg_idx in STRUCT_OPS_REFCOUNTED_ARGS is the FUNC_PROTO position
    // (0-based, including any leading scalars). Iterating the table here is
    // O(k) for k=2; same ergonomics as the MAYBE_NULL lookup.
    for (s, m, _) in STRUCT_OPS_REFCOUNTED_ARGS {
        if *s == binding.ops_struct && *m == binding.member {
            n += 1;
        }
    }
    n
}

/// Result of analyzing a single section
#[derive(Debug)]
pub enum AnalysisResult {
    Pass,
    Fail(VerificationError),
    Timeout,
    LoadError(String),
}

impl AnalysisResult {
    pub fn is_pass(&self) -> bool {
        matches!(self, AnalysisResult::Pass)
    }
}

/// Cluster E: LSM hooks the kernel's `lsm/disabled_hooks_list` rejects at
/// attach time. Mirrors `BPF_LSM_DISABLED_HOOKS` in `kernel/bpf/bpf_lsm.c`.
/// Names match the SEC suffix (`SEC("lsm/<hook>")`).
fn lsm_hook_is_disabled(hook: &str) -> bool {
    matches!(
        hook,
        "vm_enough_memory"
            | "inode_need_killpriv"
            | "inode_getsecurity"
            | "inode_setsecurity"
            | "inode_listsecurity"
            | "inode_copy_up_xattr"
            | "getselfattr"
            | "getprocattr"
            | "setprocattr"
            | "ismaclabel"
            | "secid_to_secctx"
            | "secctx_to_secid"
            | "release_secctx"
            | "d_instantiate"
            | "ipc_getsecid"
            | "key_getsecurity"
            | "audit_rule_match"
            | "audit_rule_init"
            | "audit_rule_free"
            | "module_request"
    )
}

/// Kernel `__noreturn` functions the verifier rejects as fexit/fmod_ret
/// attach targets ("Attaching fexit/fmod_ret to __noreturn functions is
/// rejected."). Mirrors the kernel's `noreturn` attribute set walked by
/// `check_attach_btf_id` — fexit fires on return, so attaching it to a
/// function that never returns is a guaranteed loss-of-control. fentry
/// is allowed; only the post-return tracers are rejected.
fn is_noreturn_kernel_fn(name: &str) -> bool {
    matches!(
        name,
        "__module_put_and_kthread_exit"
            | "__kthread_exit"
            | "__x64_sys_exit"
            | "__x64_sys_exit_group"
            | "__ia32_sys_exit"
            | "__ia32_sys_exit_group"
            | "do_exit"
            | "do_group_exit"
            | "do_task_dead"
            | "kthread_complete_and_exit"
            | "kthread_exit"
            | "make_task_dead"
            | "rewind_stack_and_make_dead"
    )
}

fn make_entry_state() -> Dbm {
    let mut dbm = Dbm::new();
    assign_zero(&mut dbm, Reg::R10);
    dbm
}

/// Register every `RelocKind::KfuncCall` entry as `name → synthetic btf_id`
/// in the analysis-context BTF. The kfunc dispatcher resolves call sites by
/// looking up the call's btf_id in this map, so without this step kfuncs
/// emitted by clang as ELF externs would mis-route as helper(213).
fn register_kfunc_relocs(
    btf: &mut BtfContext,
    pc_to_reloc: &std::collections::HashMap<usize, elf::RelocInfo>,
) {
    for reloc in pc_to_reloc.values() {
        if matches!(reloc.kind, elf::RelocKind::KfuncCall)
            && let Some(name) = &reloc.kfunc_name
        {
            btf.register_kfunc(name, reloc.helper_id);
        }
    }
}

#[derive(Clone)]
pub struct Analyzer {
    pub path: String,
    pub config: VerifierConfig,
    pub maps: Vec<BpfMapDef>,
    pub btf: BtfContext,
    /// W6.4a: cached `subprog → (ops_struct, member)` bindings extracted
    /// from `.struct_ops*` data sections + relocations. Empty for ELFs
    /// without struct_ops content. Used to seed entry-state arg types
    /// for SEC("struct_ops*") subprograms.
    pub struct_ops_bindings: Vec<StructOpsBinding>,
}

impl Analyzer {
    fn derive_program_kind(&self, section: &str) -> ProgramKind {
        if let Ok(kind) = program_kind_for_object(Path::new(&self.path)) {
            return kind;
        }

        let direct = ProgramKind::from_section(section);
        if direct != ProgramKind::Unknown {
            return direct;
        }

        // Fallback for numeric/anonymous sections (e.g., "2/3"):
        // infer from other code sections in the same object.
        let mut inferred: Option<ProgramKind> = None;
        if let Ok(sections) = list_section_names(&self.path) {
            for s in sections {
                if !is_code_section(&s) {
                    continue;
                }
                let k = ProgramKind::from_section(&s);
                if k == ProgramKind::Unknown {
                    continue;
                }
                inferred = match inferred {
                    None => Some(k),
                    Some(prev) if prev == k => Some(prev),
                    // Mixed program kinds in one object: keep conservative behavior.
                    Some(_) => return ProgramKind::Unknown,
                };
            }
        }

        inferred.unwrap_or(ProgramKind::Unknown)
    }

    /// Initialize analyzer for a specific ELF file.
    /// Loads shared resources (Maps, BTF) once.
    pub fn new(path: &str, config: VerifierConfig) -> Self {
        // Load maps (explicit + data sections)
        let explicit_maps = load_maps(path).unwrap_or_default();
        let data_maps = load_data_section_maps(path).unwrap_or_default();
        let mut all_maps = explicit_maps;
        all_maps.extend(data_maps);

        // Apply map size overrides from config
        for m in &mut all_maps {
            if let Some(&new_size) = config.map_overrides.get(&m.name) {
                if config.verbosity > 0 {
                    println!(
                        "Overriding map '{}' size: {} -> {}",
                        m.name, m.value_size, new_size
                    );
                }
                m.value_size = new_size;
            }
        }

        // Load BTF
        let btf_bytes = elf::prog::load_section_bytes(path, ".BTF", false).unwrap_or_default();
        let btf = if !btf_bytes.is_empty() {
            btf::parse_btf(&btf_bytes).unwrap_or_else(|e| {
                if config.verbosity > 0 {
                    println!("BTF Parse Warning: {}", e);
                }
                btf::BtfContext::new()
            })
        } else {
            btf::BtfContext::new()
        };

        // W6.4a: extract struct_ops bindings once per ELF. Cheap; we
        // already have the BTF parsed and re-parse the ELF here.
        let struct_ops_bindings = match std::fs::read(path) {
            Ok(bytes) => match goblin::elf::Elf::parse(&bytes) {
                Ok(elf) => extract_bindings(&bytes, &elf, &btf),
                Err(_) => Vec::new(),
            },
            Err(_) => Vec::new(),
        };

        Analyzer {
            path: path.to_string(),
            config,
            maps: all_maps,
            btf,
            struct_ops_bindings,
        }
    }

    // (W6.4c) PTR_MAYBE_NULL flags on specific struct_ops callback args.
    //
    // The kernel verifier marks a few struct_ops callback arguments as
    // PTR_MAYBE_NULL based on hand-maintained tables in the kernel
    // (real upstream sched_ext doesn't use BTF decl_tags for this — see
    // the kernel's `scx_kf_allowed_args`-style lookups in ext.c). We
    // mirror that here with a small static table; entries should match
    // what the kernel asserts in its prog-load `__failure` selftests.
    //
    // (ops_struct, member, arg_idx) — arg_idx is 0-based across the
    // FUNC_PROTO params (NOT the BPF_PROG ctx[] index, since the
    // ctx-load idiom is what consumes this via validate_ctx_access).
    //
    // sched_ext_ops:
    //   .dispatch(s32 cpu, struct task_struct *prev) — `prev` may be NULL.
    //   .yield(struct task_struct *from, struct task_struct *to) — `to`
    //                                                              may be NULL.
    // Both confirmed against `selftests/sched_ext/maybe_null_fail_*.bpf.c`
    // which assert load failure when the program derefs without checking.

    /// Build the entry-arg type vector for a struct_ops subprog by name.
    /// Returns None if no binding matches (e.g., a non-struct_ops subprog
    /// or one whose ops_struct/member can't be resolved in BTF).
    ///
    /// A subprog can appear in multiple bindings when the same function
    /// is wired into more than one ops-struct variable in the same ELF
    /// (e.g. bpf_dctcp_init → both dctcp_nouse.init and dctcp.init); the
    /// resolved arg vector is identical, so we take the first match.
    fn struct_ops_entry_args(&self, func_name: &str) -> Option<Vec<EntryArg>> {
        let binding = self
            .struct_ops_bindings
            .iter()
            .find(|b| b.subprog == func_name)?;
        let resolved = self
            .btf
            .resolve_struct_ops_method(&binding.ops_struct, &binding.member)?;
        Some(
            resolved
                .into_iter()
                .enumerate()
                .map(|(idx, a)| {
                    let nullable = is_struct_ops_arg_maybe_null(
                        &binding.ops_struct,
                        &binding.member,
                        idx as u8,
                    );
                    match a {
                        StructOpsArg::Scalar => EntryArg::Scalar,
                        // OpaquePtr falls back to a generic typed pointer rather
                        // than scalar — the verifier should treat it as a pointer
                        // so dereferences are at least size-checked, even if the
                        // pointee type is unknown.
                        StructOpsArg::OpaquePtr => EntryArg::TrustedPtrBtfId {
                            type_name: "struct",
                            nullable,
                        },
                        StructOpsArg::TrustedPtr(name) => EntryArg::TrustedPtrBtfId {
                            type_name: intern_btf_type_name(&name),
                            nullable,
                        },
                    }
                })
                .collect(),
        )
    }

    /// Analyze a single section by name.
    /// If the section contains multiple independent functions (detected via STT_FUNC symbols),
    /// each function is verified independently.
    pub fn analyze_section(&self, section: &str) -> AnalysisResult {
        // Check if section has multiple functions
        let functions = get_functions_in_section(&self.path, section).unwrap_or_default();

        if functions.len() > 1 {
            // Multiple functions in section - verify each independently
            if self.config.verbosity > 0 {
                println!(
                    "Section '{}' contains {} functions, verifying each independently",
                    section,
                    functions.len()
                );
            }

            for func in &functions {
                if self.config.verbosity > 0 {
                    println!("  Analyzing function '{}' ({} bytes)", func.name, func.size);
                }
                let result = self.analyze_function_with_info(section, func);
                if !result.is_pass() {
                    return result;
                }
            }
            return AnalysisResult::Pass;
        }

        // Single function or no symbol info - use original behavior
        self.analyze_section_as_single_program(section)
    }

    /// Analyze a single named function within a section. Used by callers
    /// that need per-function verdicts (e.g. the modern selftest runner,
    /// where each `SEC()`-tagged program in a `.c` file gets its own
    /// pass/fail expectation). Returns `LoadError` if the function isn't
    /// found in the section.
    pub fn analyze_function(&self, section: &str, func_name: &str) -> AnalysisResult {
        self.analyze_function_with_flags(section, func_name, 0)
    }

    /// Variant of [`analyze_function`] that ORs `extra_flags` into the
    /// program's `ExecContext::flags` before analysis. Used by the
    /// modern selftest runner to honor `__flag(...)` annotations such
    /// as `BPF_F_STRICT_ALIGNMENT`.
    pub fn analyze_function_with_flags(
        &self,
        section: &str,
        func_name: &str,
        extra_flags: u32,
    ) -> AnalysisResult {
        // First try the section the caller asked for.
        let funcs = get_functions_in_section(&self.path, section).unwrap_or_default();
        if let Some(func) = funcs.iter().find(|f| f.name == func_name) {
            let func = func.clone();
            return self.analyze_function_with_info_flags(section, &func, extra_flags);
        }

        // Fallback: clang sometimes emits a program under a section name
        // that doesn't match the scraped `SEC("…")` literal — modern SEC
        // aliases (`tcx/ingress` → `classifier`-ish), libbpf's optional
        // `?` prefix handling, multi-section-per-file files, etc. Walk
        // every section and dispatch on the first match. If we find the
        // function under a different section, that's not a bug — the
        // verdict is what matters.
        let all_sections = list_section_names(&self.path).unwrap_or_default();
        for s in &all_sections {
            if !is_code_section(s) || s == section {
                continue;
            }
            let funcs = get_functions_in_section(&self.path, s).unwrap_or_default();
            if let Some(func) = funcs.iter().find(|f| f.name == func_name) {
                let func = func.clone();
                return self.analyze_function_with_info_flags(s, &func, extra_flags);
            }
        }

        AnalysisResult::LoadError(format!(
            "function '{func_name}' not found (looked in '{section}' and {} other sections)",
            all_sections.len()
        ))
    }

    /// Analyze a specific function within a section, using pre-computed function info.
    ///
    /// Phase 7 wrap-up: loads `func` as the entry plus every static
    /// `__noinline` subprog it transitively calls. CallRel-typed BPF
    /// calls now resolve to in-program PCs, so the verifier follows
    /// the chain instead of treating them as opaque helper calls.
    fn analyze_function_with_info(&self, section: &str, func: &BpfFuncInfo) -> AnalysisResult {
        self.analyze_function_with_info_flags(section, func, 0)
    }

    fn analyze_function_with_info_flags(
        &self,
        section: &str,
        func: &BpfFuncInfo,
        extra_flags: u32,
    ) -> AnalysisResult {
        // Pre-resolve any `__exception_cb(<cb>)` decl_tag on this main
        // FUNC. The cb is unreachable from main's CFG (no BpfCall reloc
        // points to it), so the combiner won't pull it in by default.
        // We pass it as an extra root so its body lands in `prog` and
        // `func_offsets` exposes its entry PC, enabling the post-main
        // exception-cb analysis pass below.
        let cb_extra_roots: Vec<(String, String)> = self
            .btf
            .exception_callback_tags(&func.name)
            .into_iter()
            .next()
            .and_then(|cb_name| {
                find_section_for_func(&self.path, &cb_name)
                    .map(|cb_section| (cb_section, cb_name))
            })
            .into_iter()
            .collect();
        let (prog, pc_to_reloc, func_offsets) = match try_load_function_with_subprogs_from_elf(
            &self.path,
            section,
            &func.name,
            &self.maps,
            &cb_extra_roots,
        ) {
            Ok(t) => t,
            Err(e) => {
                // Fall back to per-function load on combiner failure
                // (e.g. cross-section reloc errors). Preserves prior
                // behavior for files where the new path can't apply.
                let pc_to_reloc = load_relocations_for_function(
                    &self.path,
                    &self.maps,
                    section,
                    func.offset,
                    func.size,
                )
                .unwrap_or_default();
                let prog = match try_load_function_from_elf(
                    &self.path,
                    section,
                    &func.name,
                    Some(&pc_to_reloc),
                ) {
                    Ok(p) => p,
                    Err(_) => return AnalysisResult::LoadError(e),
                };
                (prog, pc_to_reloc, std::collections::HashMap::new())
            }
        };
        if prog.instrs.is_empty() {
            return AnalysisResult::LoadError(format!("Empty function '{}'", func.name));
        }

        println!(
            "Test 'prog: {}, section: {}, func: {}': Lowered Program AST:",
            self.path, section, func.name
        );
        for (instr, idx) in prog.instrs.iter().zip(0..) {
            println!("  {:04}: {:?}", idx, instr);
        }

        if self.config.verbosity > 0 {
            println!(
                "Analyzing Function: '{}' ({} insns)",
                func.name,
                prog.instrs.len()
            );
        }

        // Build context
        let mut ctx = default_exec_ctx();
        ctx.map_defs = self.maps.clone();
        ctx.btf = self.btf.clone();
        register_kfunc_relocs(&mut ctx.btf, &pc_to_reloc);
        ctx.pc_to_reloc = pc_to_reloc;
        // Invert func_offsets (name → entry PC) into entry PC → name
        // so the call-rel transfer can resolve a target PC to a
        // function name and look up its BTF FUNC linkage.
        ctx.pc_to_subprog_name = func_offsets
            .iter()
            .map(|(name, pc)| (*pc, name.clone()))
            .collect();
        ctx.flags |= extra_flags;

        // Load-time validation of `__exception_cb(<cb>)` decl-tags on the
        // main subprog. libbpf encodes the annotation as a DECL_TAG named
        // `"exception_callback:<cb>"` targeting the main FUNC. The kernel
        // rejects:
        //   * more than one tag per main subprog,
        //   * a cb whose FUNC_PROTO doesn't return a scalar integer,
        //   * a cb whose FUNC_PROTO doesn't take exactly one integer arg.
        // All three are flagged before analysis runs — the runtime
        // `bpf_set_exception_callback` plumbing is unaffected.
        let cb_tags = ctx.btf.exception_callback_tags(&func.name);
        if cb_tags.len() > 1 {
            return AnalysisResult::Fail(VerificationError::ExceptionCallbackInvalid {
                reason: "multiple exception callback tags for main subprog".to_string(),
            });
        }
        if let Some(cb_name) = cb_tags.into_iter().next() {
            if let Err(reason) = ctx.btf.validate_exception_cb_signature(&cb_name) {
                return AnalysisResult::Fail(VerificationError::ExceptionCallbackInvalid {
                    reason,
                });
            }
            // Static-scan the cb's body for `bpf_throw` kfunc relocations.
            // The kernel marks an exception callback's frame as a callback
            // subprog and rejects any `bpf_throw` from inside it
            // (kernel: "cannot be called from callback subprog"). The cb
            // is unreachable from main's CFG (registered via decl_tag,
            // not called), so abstract interp never visits it — relocs
            // give us the throw sites without needing a parallel
            // analysis pass.
            if cb_subprog_throws(&self.path, &self.maps, &cb_name) {
                return AnalysisResult::Fail(VerificationError::ExceptionCallbackInvalid {
                    reason: "cannot be called from callback subprog".to_string(),
                });
            }
            ctx.exception_callback = Some(cb_name);
        }

        // Determine program kind
        ctx.prog_kind = self.derive_program_kind(section);
        // Subtype is the SEC suffix after the first delimiter — '/' for
        // hook-bound sections (`cgroup/recvmsg6`, `lsm/file_mprotect`),
        // or '.' for attach-flavored sections that carry no explicit
        // hook (`kprobe.session`, `uprobe.session`). Falls through to
        // None when neither is present (`raw_tp`, `tc`, ...).
        ctx.attach_subtype = match section.to_lowercase().split_once('/') {
            Some((_, sub)) => Some(sub.to_string()),
            None => section
                .to_lowercase()
                .split_once('.')
                .map(|(_, sub)| sub.to_string()),
        };
        // Companion to `attach_subtype`: capture the SEC's flavor
        // prefix (`fentry`, `fexit`, `fmod_ret`, ...) so transfer
        // checks can dispatch on tracing flavor without re-parsing.
        ctx.attach_flavor = section
            .to_lowercase()
            .strip_prefix('?')
            .unwrap_or(&section.to_lowercase())
            .split_once('/')
            .map(|(prefix, _)| prefix.trim_end_matches(".s").to_string());

        // Cluster E: reject SEC("lsm/<hook>") for hooks the kernel's
        // BPF_LSM_DISABLED_HOOKS list excludes from BPF attach.
        if ctx.prog_kind == ProgramKind::Lsm
            && let Some(hook) = ctx.attach_subtype.as_deref()
            && lsm_hook_is_disabled(hook)
        {
            return AnalysisResult::Fail(VerificationError::LsmHookDisabled {
                hook: hook.to_string(),
            });
        }

        // Reject SEC("fexit/<noreturn>") and SEC("fmod_ret/<noreturn>")
        // — fexit/fmod_ret fire after the attached function returns, so
        // attaching them to a `__noreturn` kernel function is a kernel
        // attach-time error ("Attaching fexit/fmod_ret to __noreturn
        // functions is rejected."). fentry on the same target is fine.
        let sec_lower = section.to_lowercase();
        if (sec_lower.starts_with("fexit/")
            || sec_lower.starts_with("fexit.s/")
            || sec_lower.starts_with("fmod_ret/")
            || sec_lower.starts_with("fmod_ret.s/"))
            && let Some(target) = ctx.attach_subtype.as_deref()
            && is_noreturn_kernel_fn(target)
        {
            return AnalysisResult::Fail(VerificationError::NoreturnAttachTarget {
                target: target.to_string(),
            });
        }

        // W6.4a: for struct_ops subprogs, seed R1..Rn from the resolved
        // ops-struct member signature. derive_program_kind already
        // matched SEC("struct_ops*") to ProgramKind::StructOps; the
        // bindings cache resolves func_name → (ops_struct, member).
        if ctx.prog_kind == ProgramKind::StructOps {
            // Reject SEC("struct_ops/<member>") whose <member> is on the
            // kmod's unsupported list before any analysis runs. Mirrors
            // the kernel's "attach to unsupported member ... of struct ..."
            // (e.g. bpf_testmod_ops.unsupported_ops).
            if let Some(binding) = self
                .struct_ops_bindings
                .iter()
                .find(|b| b.subprog == func.name)
                && is_unsupported_struct_ops_member(&binding.ops_struct, &binding.member)
            {
                return AnalysisResult::Fail(VerificationError::UnsupportedStructOpsMember {
                    ops_struct: binding.ops_struct.clone(),
                    member: binding.member.clone(),
                });
            }
            ctx.entry_args = self.struct_ops_entry_args(&func.name);
            // Also note whether the matched method returns void; the
            // analysis layer relaxes the exit-time R0-readability check
            // for void methods. Take the same first-binding-wins rule
            // as struct_ops_entry_args (a subprog wired into multiple
            // ops-struct vars resolves identically).
            let binding = self
                .struct_ops_bindings
                .iter()
                .find(|b| b.subprog == func.name);
            ctx.entry_returns_void = binding
                .and_then(|b| {
                    self.btf
                        .struct_ops_method_returns_void(&b.ops_struct, &b.member)
                })
                .unwrap_or(false);
            // W6.4c: pass the (ops_struct, member) pair into the analysis
            // context so transfer_kfunc_proto can enforce per-(ops, member)
            // kfunc-context allowlists.
            ctx.struct_ops_member = binding.map(|b| (b.ops_struct.clone(), b.member.clone()));
            ctx.struct_ops_refcounted_args =
                struct_ops_refcounted_arg_count(&self.struct_ops_bindings, &func.name);
        } else if matches!(
            ctx.prog_kind,
            ProgramKind::Lsm
                | ProgramKind::Tracing
                | ProgramKind::Tracepoint
                | ProgramKind::RawTracepoint
                | ProgramKind::RawTracepointWritable
        ) {
            // Phase 7 wrap-up: extend the W6.4a struct_ops ctx-load idiom
            // to fentry/fexit/tp_btf/lsm/tracepoint. clang's BPF_PROG()
            // wrapper unpacks the kernel-passed args via `r1 = *(u64*)(r1 + 8*idx)`;
            // we type each ctx slot from the function's BTF FUNC_PROTO.
            // No per-arg MAYBE_NULL table for these kinds (the kernel
            // marks fentry/LSM args as trusted/non-null by convention).
            // For non-struct_ops tracing kinds, a bare `void *ctx`
            // signature (e.g. `int handler(void *ctx)`) carries no real
            // arg-type info — the program will be unpacked at runtime
            // against the *attach target's* BTF, which we don't ship.
            // Skip populating entry_args in that case so
            // `validate_ctx_access` falls back to the static
            // MAYBE_NULL table keyed by attach_subtype (the only path
            // that surfaces nullable trusted-args for tp_btf raw-tp
            // targets).
            // When the SEC-tagged entry point is a `BPF_PROG()` wrapper —
            // signature `void *ctx` — its outer BTF FUNC_PROTO is a bare
            // void-ctx, useless for typing the ctx-array slot loads the
            // wrapper emits. The macro's inner static function carries the
            // user-declared typed args; libbpf names it
            // `____<entry>` (4 underscores) and that's what BTF stores
            // *unless* clang inlined it (the BPF_PROG inner is
            // `static __always_inline`, so no separate FUNC entry
            // survives in `-O2`). Try the inner first; if missing, fall
            // back to the outer's signature, then to a static
            // (prog_kind, attach_subtype) → arg-types table keyed off
            // the BPF section name. The static table is the only thing
            // that lets us type LSM/tp_btf hook args without shipping
            // vmlinux BTF — what the kernel verifier resolves at attach
            // time from the hook's vmlinux signature.
            let bpf_prog_inner = format!("____{}", func.name);
            let resolved = self
                .btf
                .resolve_func_args(&bpf_prog_inner)
                .or_else(|| self.btf.resolve_func_args(&func.name));
            ctx.entry_args = resolved.and_then(|args| {
                let bare_void_ctx = args.len() == 1
                    && matches!(args[0], StructOpsArg::OpaquePtr);
                if bare_void_ctx {
                    return None;
                }
                Some(
                    args.into_iter()
                        .map(|a| match a {
                            StructOpsArg::Scalar => EntryArg::Scalar,
                            StructOpsArg::OpaquePtr => EntryArg::TrustedPtrBtfId {
                                type_name: "struct",
                                nullable: false,
                            },
                            StructOpsArg::TrustedPtr(name) => EntryArg::TrustedPtrBtfId {
                                // Strict variant: kfunc validators
                                // (`validate_ptr_to_task` matching
                                // `"task_struct"`) require the real
                                // BTF type name on Lsm/Tracing/tp_btf
                                // entry-arg pointers. struct_ops keeps
                                // the lax `"unknown"` (see line 352)
                                // because its handlers commonly write
                                // through these args to embedded state
                                // that mem_region_model doesn't
                                // describe.
                                type_name: intern_btf_type_name_strict(&name),
                                nullable: false,
                            },
                        })
                        .collect(),
                )
            });

            // Static (prog_kind, attach_subtype) → BPF_PROG entry-args
            // fallback for the BPF_PROG()-wrapped LSM/tp_btf/tracing
            // hooks whose inner typed function is `__always_inline` and
            // therefore has no surviving FUNC entry in BTF (so the BPF
            // path above's bpf_prog_inner lookup misses). The kernel
            // resolves these from the attach target's vmlinux BTF — we
            // mirror only the hooks our test corpus actually attaches to.
            if ctx.entry_args.is_none() {
                if let Some(target) = ctx.attach_subtype.as_deref() {
                    let flavor = ctx.attach_flavor.as_deref();
                    let table_args = match (ctx.prog_kind, flavor, target) {
                        // LSM hooks. Args from include/linux/lsm_hooks.h's
                        // `LSM_HOOK(...)` declarations. Trailing scalar
                        // args (int, unsigned, etc.) are dropped — only
                        // the BTF-typed pointer prefix matters; the
                        // ctx-array load typing only fires for 8-byte
                        // pointer fields, scalars fall through to
                        // ScalarValue and pose no soundness issue.
                        (ProgramKind::Lsm, _, "file_open") => {
                            Some(vec![("file", false)])
                        }
                        (ProgramKind::Lsm, _, "task_alloc") => {
                            Some(vec![("task_struct", false)])
                        }
                        (ProgramKind::Lsm, _, "inode_getattr") => {
                            Some(vec![("path", false)])
                        }
                        (ProgramKind::Lsm, _, "inode_unlink") => {
                            Some(vec![("inode", false), ("dentry", false)])
                        }
                        (ProgramKind::Lsm, _, "inode_rename") => Some(vec![
                            ("inode", false),
                            ("dentry", false),
                            ("inode", false),
                            ("dentry", false),
                        ]),
                        (ProgramKind::Lsm, _, "socket_bind") => Some(vec![
                            ("socket", false),
                            ("sockaddr", false),
                        ]),
                        (ProgramKind::Lsm, _, "socket_post_create") => {
                            Some(vec![("socket", false)])
                        }
                        (ProgramKind::Lsm, _, "bprm_committed_creds") => {
                            Some(vec![("linux_binprm", false)])
                        }
                        // tp_btf raw-tracepoint targets. Args from
                        // include/trace/events/<sub>.h's TRACE_EVENT
                        // declarations. clang `__always_inline`s the
                        // BPF_PROG inner so we mirror the kernel's
                        // attach-time vmlinux-BTF resolution with a
                        // static table for hooks our corpus exercises.
                        (ProgramKind::Tracing, Some("tp_btf"), "task_newtask") => {
                            Some(vec![("task_struct", false)])
                        }
                        (ProgramKind::Tracing, Some("tp_btf"), "tcp_probe") => {
                            Some(vec![("sock", false), ("sk_buff", false)])
                        }
                        _ => None,
                    };
                    if let Some(arg_specs) = table_args {
                        ctx.entry_args = Some(
                            arg_specs
                                .into_iter()
                                .map(|(name, nullable)| EntryArg::TrustedPtrBtfId {
                                    type_name: intern_btf_type_name_strict(name),
                                    nullable,
                                })
                                .collect(),
                        );
                    }
                }
            }
        }

        if self.config.verbosity > 0 {
            println!("  Program kind: {:?}", ctx.prog_kind);
            if let Some(args) = &ctx.entry_args {
                println!("  Entry args: {:?}", args);
            }
        }

        // Run analysis
        let entry = make_entry_state();
        let result = analysis::analyze_program(&ctx, &prog, entry, &self.config);

        match result {
            Ok(_) => {
                // Verify the body of any registered `__exception_cb`.
                // Mirrors the kernel's `do_check_subprogs` force-marking the
                // cb subprog as called: the cb is unreachable from main's
                // CFG, so we drive a separate analysis pass over its body.
                // The cb's entry PC lives in `func_offsets` (built by the
                // combined-prog ELF loader); if the cb isn't in this map
                // (e.g. fallback per-function load path), we skip — the
                // static reloc-scan and signature checks already ran.
                if let Some(cb_name) = ctx.exception_callback.as_deref()
                    && let Some(&cb_entry_pc) = func_offsets.get(cb_name)
                {
                    let cb_entry = make_entry_state();
                    if let Some(err) = analysis::analyze_exception_cb(
                        &ctx,
                        &prog,
                        cb_entry,
                        &self.config,
                        cb_entry_pc,
                    ) {
                        return if err.description().contains("Complexity limit") {
                            AnalysisResult::Timeout
                        } else {
                            AnalysisResult::Fail(err)
                        };
                    }
                }
                AnalysisResult::Pass
            }
            Err(e) => {
                if e.description().contains("Complexity limit") {
                    AnalysisResult::Timeout
                } else {
                    AnalysisResult::Fail(e)
                }
            }
        }
    }

    /// Section analysis - treats entire section as one program
    /// If the section has cross-section BPF calls, subprograms are combined.
    fn analyze_section_as_single_program(&self, section: &str) -> AnalysisResult {
        // Load program with combined subprograms if needed
        let (prog, pc_to_reloc) =
            match try_load_combined_program_from_elf(&self.path, section, &self.maps) {
                Ok((p, r)) => (p, r),
                Err(e) => return AnalysisResult::LoadError(e),
            };
        if prog.instrs.is_empty() {
            return AnalysisResult::LoadError("Empty program or section not found".to_string());
        }
        println!(
            "Test 'prog: {}, section: {}': Lowered Program AST:",
            self.path, section
        );
        for (instr, idx) in prog.instrs.iter().zip(0..) {
            println!("  {:04}: {:?}", idx, instr);
        }

        if self.config.verbosity > 0 {
            println!(
                "Analyzing Section: '{}' ({} insns)",
                section,
                prog.instrs.len()
            );
        }

        // Build context
        let mut ctx = default_exec_ctx();
        ctx.map_defs = self.maps.clone();
        ctx.btf = self.btf.clone();
        register_kfunc_relocs(&mut ctx.btf, &pc_to_reloc);
        ctx.pc_to_reloc = pc_to_reloc;

        // Determine program kind
        ctx.prog_kind = self.derive_program_kind(section);
        // Subtype is the SEC suffix after the first delimiter — '/' for
        // hook-bound sections (`cgroup/recvmsg6`, `lsm/file_mprotect`),
        // or '.' for attach-flavored sections that carry no explicit
        // hook (`kprobe.session`, `uprobe.session`). Falls through to
        // None when neither is present (`raw_tp`, `tc`, ...).
        ctx.attach_subtype = match section.to_lowercase().split_once('/') {
            Some((_, sub)) => Some(sub.to_string()),
            None => section
                .to_lowercase()
                .split_once('.')
                .map(|(_, sub)| sub.to_string()),
        };
        // Companion to `attach_subtype`: capture the SEC's flavor
        // prefix (`fentry`, `fexit`, `fmod_ret`, ...) so transfer
        // checks can dispatch on tracing flavor without re-parsing.
        ctx.attach_flavor = section
            .to_lowercase()
            .strip_prefix('?')
            .unwrap_or(&section.to_lowercase())
            .split_once('/')
            .map(|(prefix, _)| prefix.trim_end_matches(".s").to_string());

        // Cluster E: reject SEC("lsm/<hook>") for hooks the kernel's
        // BPF_LSM_DISABLED_HOOKS list excludes from BPF attach.
        if ctx.prog_kind == ProgramKind::Lsm
            && let Some(hook) = ctx.attach_subtype.as_deref()
            && lsm_hook_is_disabled(hook)
        {
            return AnalysisResult::Fail(VerificationError::LsmHookDisabled {
                hook: hook.to_string(),
            });
        }

        // Reject SEC("fexit/<noreturn>") and SEC("fmod_ret/<noreturn>")
        // — fexit/fmod_ret fire after the attached function returns, so
        // attaching them to a `__noreturn` kernel function is a kernel
        // attach-time error ("Attaching fexit/fmod_ret to __noreturn
        // functions is rejected."). fentry on the same target is fine.
        let sec_lower = section.to_lowercase();
        if (sec_lower.starts_with("fexit/")
            || sec_lower.starts_with("fexit.s/")
            || sec_lower.starts_with("fmod_ret/")
            || sec_lower.starts_with("fmod_ret.s/"))
            && let Some(target) = ctx.attach_subtype.as_deref()
            && is_noreturn_kernel_fn(target)
        {
            return AnalysisResult::Fail(VerificationError::NoreturnAttachTarget {
                target: target.to_string(),
            });
        }

        // Section-mode path: no per-subprog identity, so we don't seed
        // struct_ops entry_args here. For struct_ops we always go through
        // analyze_function instead (one program per ops-struct member).

        if self.config.verbosity > 0 {
            println!("  Program kind: {:?}", ctx.prog_kind);
        }

        // Run analysis
        let entry = make_entry_state();
        let result = analysis::analyze_program(&ctx, &prog, entry, &self.config);

        match result {
            Ok(_) => AnalysisResult::Pass,
            Err(e) => {
                // Detect Complexity Limit
                if e.description().contains("Complexity limit") {
                    AnalysisResult::Timeout
                } else {
                    AnalysisResult::Fail(e)
                }
            }
        }
    }

    /// Analyze all code sections in the file
    pub fn analyze_all(&self) -> (bool, Vec<(String, AnalysisResult)>) {
        let sections = list_section_names(&self.path).unwrap_or_default();
        let mut results = Vec::new();
        let mut all_pass = true;

        for section in sections {
            if !is_code_section(&section) {
                continue;
            }

            // Skip loading if program is empty or fails to load (optimization)
            let prog_check = match try_load_program_from_elf(&self.path, &section, None) {
                Ok(p) => p,
                Err(_) => continue, // Skip sections that fail to load
            };
            if prog_check.instrs.is_empty() {
                continue;
            }

            let result = self.analyze_section(&section);

            if !result.is_pass() {
                all_pass = false;
            }
            results.push((section.to_string(), result));
        }
        (all_pass, results)
    }
}

/// True if the named subprog's body contains a `bpf_throw` kfunc call.
/// Walks every section in the .o looking for the function symbol, then
/// scans that function's relocations for any `KfuncCall` whose
/// `kfunc_name` is `"bpf_throw"`. Used to enforce the kernel's
/// "cannot be called from callback subprog" rule against an
/// `__exception_cb`-registered handler that the main program's CFG
/// never reaches.
fn cb_subprog_throws(path: &str, maps: &[BpfMapDef], cb_name: &str) -> bool {
    let Ok(sections) = list_section_names(path) else {
        return false;
    };
    for sec in &sections {
        let Ok(funcs) = get_functions_in_section(path, sec) else {
            continue;
        };
        let Some(func) = funcs.iter().find(|f| f.name == cb_name) else {
            continue;
        };
        let Ok(relocs) = load_relocations_for_function(path, maps, sec, func.offset, func.size)
        else {
            return false;
        };
        return relocs
            .values()
            .any(|r| r.kfunc_name.as_deref() == Some("bpf_throw"));
    }
    false
}

/// Helper: Find section name for a given function symbol
pub fn find_section_for_func(path: &str, func_name: &str) -> Option<String> {
    let progs = load_raw_programs(path).ok()?;
    let target = progs.iter().find(|p| p.name == func_name)?;
    let sections = list_section_names(path).ok()?;
    sections.get(target.section_idx).map(|s| s.to_string())
}

/// Check if a section contains BPF code
pub fn is_code_section(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    if name.starts_with('.') {
        return false;
    }
    if name == "license" || name == "version" || name == "maps" {
        return false;
    }
    true
}
