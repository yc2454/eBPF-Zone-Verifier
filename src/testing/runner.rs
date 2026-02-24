// src/runner.rs

use crate::analysis;
use crate::analysis::machine::context::default_exec_ctx;
use crate::analysis::machine::error::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::ast::ProgramKind;
use crate::common::config::VerifierConfig;
use crate::common::utils::{
    program_kind_for_object, try_load_combined_program_from_elf, try_load_function_from_elf,
    try_load_program_from_elf,
};
use crate::parsing::btf::{self, BtfContext};
use crate::parsing::elf;
use crate::parsing::elf::{
    BpfFuncInfo, BpfMapDef, get_functions_in_section, list_section_names, load_data_section_maps,
    load_maps, load_raw_programs, load_relocations_for_function,
};
use crate::zone::dbm::Dbm;
use crate::zone::domain::assign_zero;
use std::path::Path;

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

fn make_entry_state() -> Dbm {
    let mut dbm = Dbm::new();
    assign_zero(&mut dbm, Reg::R10);
    dbm
}

pub struct Analyzer {
    pub path: String,
    pub config: VerifierConfig,
    pub maps: Vec<BpfMapDef>,
    pub btf: BtfContext,
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

        Analyzer {
            path: path.to_string(),
            config,
            maps: all_maps,
            btf,
        }
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

    /// Analyze a specific function within a section, using pre-computed function info
    fn analyze_function_with_info(&self, section: &str, func: &BpfFuncInfo) -> AnalysisResult {
        // Load relocations adjusted for this function's offset within the section
        let pc_to_reloc =
            load_relocations_for_function(&self.path, &self.maps, section, func.offset, func.size)
                .unwrap_or_default();

        // Load only this function's bytes
        let prog =
            match try_load_function_from_elf(&self.path, section, &func.name, Some(&pc_to_reloc)) {
                Ok(p) => p,
                Err(e) => return AnalysisResult::LoadError(e),
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
        ctx.pc_to_reloc = pc_to_reloc;

        // Determine program kind
        ctx.prog_kind = self.derive_program_kind(section);

        if self.config.verbosity > 0 {
            println!("  Program kind: {:?}", ctx.prog_kind);
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
        ctx.pc_to_reloc = pc_to_reloc;

        // Determine program kind
        ctx.prog_kind = self.derive_program_kind(section);

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
