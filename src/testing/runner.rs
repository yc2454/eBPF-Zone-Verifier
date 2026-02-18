// src/runner.rs

use crate::analysis;
use crate::analysis::machine::context::default_exec_ctx;
use crate::analysis::machine::env::VerificationError;
use crate::analysis::machine::reg::Reg;
use crate::ast::ProgramKind;
use crate::common::config::VerifierConfig;
use crate::common::utils::{load_program_from_elf, program_kind_for_object};
use crate::parsing::btf::{self, BtfContext};
use crate::parsing::elf;
use crate::parsing::elf::{
    BpfMapDef, list_section_names, load_data_section_maps, load_maps, load_raw_programs,
    load_relocations,
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

    /// Analyze a single section by name
    pub fn analyze_section(&self, section: &str) -> AnalysisResult {
        // Load relocations specific to this section
        let pc_to_reloc = load_relocations(&self.path, &self.maps, section).unwrap_or_default();

        // Load program with relocations
        let prog = load_program_from_elf(&self.path, section, Some(&pc_to_reloc));
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
        ctx.prog_kind = match program_kind_for_object(Path::new(&self.path)) {
            Ok(kind) => kind,
            Err(_) => ProgramKind::from_section(section),
        };

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

            // Skip loading if program is empty (optimization)
            let prog_check = load_program_from_elf(&self.path, &section, None);
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
