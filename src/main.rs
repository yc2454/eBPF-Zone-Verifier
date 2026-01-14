// src/main.rs - Enhanced for multi-program ELF files

mod ast;
mod analysis;
mod parsing;
mod zone;
mod misc;

use crate::analysis::context::{ExecContext, default_exec_ctx};
use crate::analysis::env::VerificationError;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{REG_ENV, assign_zero};
use crate::misc::utils::load_program_from_elf;
use crate::parsing::elf_loader::{load_maps, load_relocations, load_raw_programs, list_section_names};
use crate::parsing::elf_loader::{self, BpfMapDef};
use crate::parsing::btf::{self, BtfContext};
use crate::ast::ProgramKind;

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- elf-list        <elf_path>                 # List all sections and programs");
    eprintln!("  cargo run -- elf-analyze     <elf_path> <section_name>  # Analyze a section by name");
    eprintln!("  cargo run -- elf-analyze-func <elf_path> <func_name>   # Analyze a function by name");
    eprintln!("  cargo run -- elf-analyze-all <elf_path>                 # Analyze all sections");
}

fn make_entry_state(ctx: &ExecContext) -> Dbm {
    let mut dbm = Dbm::new(REG_ENV.len());
    assign_zero(&mut dbm, ctx.r10, ctx.zero);
    dbm
}

/// Result of analyzing a single section
#[derive(Debug)]
enum AnalysisResult {
    Pass,
    Fail(VerificationError),
    LoadError(String),
}

/// Analyze a single section, returning the result
fn analyze_section(
    path: &str,
    section: &str,
    map_defs: &[BpfMapDef],
    btf_ctx: &BtfContext,
    verbose: bool,
) -> AnalysisResult {
    // Build context
    let mut cctx = default_exec_ctx();
    cctx.map_defs = map_defs.to_vec();
    cctx.pc_to_map_idx = load_relocations(path, map_defs, section).unwrap_or_default();
    cctx.btf = btf_ctx.clone();
    cctx.prog_kind = match section {
        "xdp" => ProgramKind::Xdp,
        s if s.starts_with("xdp") => ProgramKind::Xdp,
        _ => ProgramKind::Tc,
    };

    // Load program
    let prog = load_program_from_elf(path, section);
    if prog.instrs.is_empty() {
        return AnalysisResult::LoadError("Empty program".to_string());
    }

    if verbose {
        println!("  Program size: {} instructions", prog.instrs.len());
    }

    // Run analysis
    let entry = make_entry_state(&cctx);
    let result = analysis::analyze_program(&cctx, &prog, entry);

    match result {
        Ok(_) => AnalysisResult::Pass,
        Err(e) => AnalysisResult::Fail(e),
    }
}

/// Build a map from section index to function name
fn build_section_to_func_map(path: &str) -> std::collections::HashMap<usize, String> {
    let mut map = std::collections::HashMap::new();
    if let Ok(progs) = load_raw_programs(path) {
        for p in progs {
            map.insert(p.section_idx, p.name);
        }
    }
    map
}

/// Check if a section contains BPF code (not metadata/debug sections)
fn is_code_section(name: &str) -> bool {
    // Skip empty names
    if name.is_empty() {
        return false;
    }
    // Skip standard ELF metadata sections
    if name.starts_with('.') {
        return false;
    }
    // Skip license and version sections
    if name == "license" || name == "version" || name == "maps" {
        return false;
    }
    true
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        usage();
        return;
    }

    let cmd = &args[1];

    match cmd.as_str() {
        // ============================================================
        // List all sections and programs in an ELF
        // ============================================================
        "elf-list" => {
            if args.len() < 3 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &args[2];

            println!("=== ELF Contents: '{}' ===\n", path);

            // 1. List Sections
            println!("--- SECTIONS ---");
            match list_section_names(path) {
                Ok(sections) => {
                    for (i, name) in sections.iter().enumerate() {
                        if is_code_section(name) {
                            println!("  [{}] {}", i, name);
                        }
                    }
                    println!("\n  (Showing code sections. Use section name with elf-analyze)");
                }
                Err(e) => eprintln!("  Error listing sections: {:?}", e),
            }

            // 2. List Programs (Functions from Symbol Table)
            println!("\n--- BPF PROGRAMS (Functions) ---");
            match load_raw_programs(path) {
                Ok(progs) => {
                    if progs.is_empty() {
                        println!("  No function symbols found.");
                    } else {
                        for (i, p) in progs.iter().enumerate() {
                            let insn_count = p.data.len() / 8;
                            println!("  [{}] {} ({} instructions)", i, p.name, insn_count);
                        }
                    }
                }
                Err(e) => eprintln!("  Error loading programs: {:?}", e),
            }

            // 3. List Maps
            println!("\n--- BPF MAPS ---");
            match load_maps(path) {
                Ok(maps) => {
                    if maps.is_empty() {
                        println!("  No maps found.");
                    } else {
                        for (i, m) in maps.iter().enumerate() {
                            println!("  [{}] {} (key: {} bytes, value: {} bytes)", 
                                     i, m.name, m.key_size, m.value_size);
                        }
                    }
                }
                Err(e) => eprintln!("  Error loading maps: {:?}", e),
            }

            println!("\n=== Done ===");
        }

        // ============================================================
        // Analyze by section name
        // ============================================================
        "elf-analyze" => {
            if args.len() < 4 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &args[2];
            let section = &args[3];

            println!("=== ELF analyze: file='{}', section='{}' ===", path, section);
            
            // Load shared resources
            let map_defs = load_maps(path).unwrap_or_default();
            println!("Loaded {} maps", map_defs.len());

            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
            let btf_ctx = if !btf_bytes.is_empty() {
                btf::parse_btf(&btf_bytes).unwrap_or_else(|e| {
                    println!("BTF Parse Error: {}", e);
                    btf::BtfContext::new()
                })
            } else {
                println!("No .BTF section found.");
                btf::BtfContext::new()
            };

            let result = analyze_section(path, section, &map_defs, &btf_ctx, true);
            
            match result {
                AnalysisResult::Pass => println!("\n=== PASS ==="),
                AnalysisResult::Fail(e) => println!("\n=== FAIL: {:?} ===", e),
                AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
            }
        }

        // ============================================================
        // Analyze by function name
        // ============================================================
        "elf-analyze-func" => {
            if args.len() < 4 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &args[2];
            let func_name = &args[3];

            println!("=== ELF analyze function: file='{}', func='{}' ===", path, func_name);

            let progs = match load_raw_programs(path) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("Error loading programs: {:?}", e);
                    return;
                }
            };

            let target_prog = progs.iter().find(|p| p.name == *func_name);
            if target_prog.is_none() {
                eprintln!("Error: Function '{}' not found.", func_name);
                eprintln!("Available functions:");
                for p in &progs {
                    eprintln!("  - {}", p.name);
                }
                return;
            }
            let target_prog = target_prog.unwrap();
            
            println!("Found function '{}' ({} instructions)", 
                     func_name, target_prog.data.len() / 8);

            // Get section name for this function
            let sections = list_section_names(path).unwrap_or_default();
            let section_name = if target_prog.section_idx < sections.len() {
                &sections[target_prog.section_idx]
            } else {
                "unknown"
            };
            println!("Function is in section: '{}'", section_name);

            // Load shared resources
            let map_defs = load_maps(path).unwrap_or_default();
            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
            let btf_ctx = if !btf_bytes.is_empty() {
                btf::parse_btf(&btf_bytes).unwrap_or_default()
            } else {
                btf::BtfContext::new()
            };

            let result = analyze_section(path, section_name, &map_defs, &btf_ctx, true);
            
            match result {
                AnalysisResult::Pass => println!("\n=== PASS ==="),
                AnalysisResult::Fail(e) => println!("\n=== FAIL: {:?} ===", e),
                AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
            }
        }

        // ============================================================
        // NEW: Analyze all sections
        // ============================================================
        "elf-analyze-all" => {
            if args.len() < 3 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &args[2];

            println!("=== ELF analyze all: '{}' ===\n", path);

            // Load shared resources once
            let map_defs = load_maps(path).unwrap_or_default();
            println!("Loaded {} maps", map_defs.len());

            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
            let btf_ctx = if !btf_bytes.is_empty() {
                btf::parse_btf(&btf_bytes).unwrap_or_default()
            } else {
                btf::BtfContext::new()
            };

            // Get sections and function name mapping
            let sections = list_section_names(path).unwrap_or_default();
            let section_to_func = build_section_to_func_map(path);

            // Filter to code sections
            let code_sections: Vec<(usize, &String)> = sections.iter()
                .enumerate()
                .filter(|(_, name)| is_code_section(name))
                .collect();

            println!("Found {} code sections\n", code_sections.len());

            // Track results
            let mut results: Vec<(String, String, AnalysisResult)> = Vec::new();
            let mut pass_count = 0;
            let mut fail_count = 0;
            let mut error_count = 0;

            // Analyze each section
            for (idx, section_name) in &code_sections {
                let func_name = section_to_func.get(idx)
                    .map(|s| s.as_str())
                    .unwrap_or("-");
                
                print!("Analyzing section '{}' ({})... ", section_name, func_name);
                
                let result = analyze_section(path, section_name, &map_defs, &btf_ctx, false);
                
                match &result {
                    AnalysisResult::Pass => {
                        println!("PASS");
                        pass_count += 1;
                    }
                    AnalysisResult::Fail(e) => {
                        println!("FAIL");
                        fail_count += 1;
                    }
                    AnalysisResult::LoadError(e) => {
                        println!("ERROR ({})", e);
                        error_count += 1;
                    }
                }
                
                results.push((section_name.to_string(), func_name.to_string(), result));
            }

            // Print summary
            println!("\n========================================");
            println!("                SUMMARY");
            println!("========================================");
            println!("Total:  {}", code_sections.len());
            println!("Pass:   {}", pass_count);
            println!("Fail:   {}", fail_count);
            println!("Errors: {}", error_count);

            // Print failures
            if fail_count > 0 {
                println!("\n--- FAILURES ---");
                for (section, func, result) in &results {
                    if let AnalysisResult::Fail(e) = result {
                        println!("  {} ({}): {}", section, func, e.description());
                    }
                }
            }

            // Print errors
            if error_count > 0 {
                println!("\n--- ERRORS ---");
                for (section, func, result) in &results {
                    if let AnalysisResult::LoadError(e) = result {
                        println!("  {} ({}): {}", section, func, e);
                    }
                }
            }

            println!("\n=== Done ===");
        }

        _ => {
            eprintln!("Unknown command: {}", cmd);
            usage();
        }
    }
}