// src/runner.rs

use crate::analysis;
use crate::analysis::machine::context::{EntryArg, default_exec_ctx, intern_btf_type_name};
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
        // First try the section the caller asked for.
        let funcs = get_functions_in_section(&self.path, section).unwrap_or_default();
        if let Some(func) = funcs.iter().find(|f| f.name == func_name) {
            let func = func.clone();
            return self.analyze_function_with_info(section, &func);
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
                return self.analyze_function_with_info(s, &func);
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
        let (prog, pc_to_reloc, func_offsets) = match try_load_function_with_subprogs_from_elf(
            &self.path,
            section,
            &func.name,
            &self.maps,
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
        let _ = &func_offsets;

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

        // Determine program kind
        ctx.prog_kind = self.derive_program_kind(section);
        ctx.attach_subtype = section
            .to_lowercase()
            .split_once('/')
            .map(|(_, sub)| sub.to_string());

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

        // W6.4a: for struct_ops subprogs, seed R1..Rn from the resolved
        // ops-struct member signature. derive_program_kind already
        // matched SEC("struct_ops*") to ProgramKind::StructOps; the
        // bindings cache resolves func_name → (ops_struct, member).
        if ctx.prog_kind == ProgramKind::StructOps {
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
            ctx.entry_args = self.btf.resolve_func_args(&func.name).map(|args| {
                args.into_iter()
                    .map(|a| match a {
                        StructOpsArg::Scalar => EntryArg::Scalar,
                        StructOpsArg::OpaquePtr => EntryArg::TrustedPtrBtfId {
                            type_name: "struct",
                            nullable: false,
                        },
                        StructOpsArg::TrustedPtr(name) => EntryArg::TrustedPtrBtfId {
                            type_name: intern_btf_type_name(&name),
                            nullable: false,
                        },
                    })
                    .collect()
            });
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
            Ok(_) => AnalysisResult::Pass,
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
        ctx.attach_subtype = section
            .to_lowercase()
            .split_once('/')
            .map(|(_, sub)| sub.to_string());

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
