// src/main.rs - With configurable verifier options

mod ast;
mod analysis;
mod parsing;
mod zone;
mod misc;
mod logging;

use crate::analysis::context::{ExecContext, default_exec_ctx};
use crate::analysis::env::VerificationError;
use crate::misc::config::VerifierConfig;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{REG_ENV, assign_zero};
use crate::misc::utils::{load_program_from_elf, program_kind_for_object};
use crate::parsing::elf_loader::{
    load_maps, load_relocations, load_data_section_maps,
    load_raw_programs, list_section_names};
use crate::parsing::elf_loader::{self};
use crate::parsing::btf::{self, BtfContext};
use crate::ast::ProgramKind;
use crate::logging::{FilterConfig};

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- [flags] elf-list        <elf_path>");
    eprintln!("  cargo run -- [flags] elf-analyze     <elf_path> <section_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-func <elf_path> <func_name>");
    eprintln!("  cargo run -- [flags] analyze-batch   <elf_path>");
    eprintln!("");
    VerifierConfig::print_help();
    eprintln!("");
    eprintln!("Examples:");
    eprintln!("  cargo run -- elf-list ./bpf_host.o");
    eprintln!("  cargo run -- elf-analyze ./bpf_host.o tc");
    eprintln!("  cargo run -- --skip-dbm analyze-batch ./bpf_host.o");
    eprintln!("  cargo run -- --max-insn 2000000 -v elf-analyze ./bpf_host.o tc");
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
    btf_ctx: &BtfContext,
    config: &VerifierConfig,
    verbose: bool,
) -> AnalysisResult {
    // Load maps (explicit + data sections)
    let explicit_maps = load_maps(path).unwrap_or_default();
    let data_maps = load_data_section_maps(path).unwrap_or_default();
    let mut all_maps = explicit_maps;
    all_maps.extend(data_maps);
    // Load relocations
    let pc_to_reloc = 
        load_relocations(path, &all_maps, section).unwrap_or_default();
        
    // Apply map size overrides from config
    for m in &mut all_maps {
        if let Some(&new_size) = config.map_overrides.get(&m.name) {
            println!("Overriding map '{}' size: {} -> {}", m.name, m.value_size, new_size);
            m.value_size = new_size;
        }
    }
    
    // Build context
    let mut ctx = default_exec_ctx();
    ctx.map_defs = all_maps;
    ctx.pc_to_reloc = pc_to_reloc;
    ctx.btf = btf_ctx.clone();
    ctx.prog_kind = match program_kind_for_object(std::path::Path::new(path)) {
        Ok(kind) => {
            println!("  Detected program kind: {:?}", kind);
            kind
        },
        Err(_) => ProgramKind::Unknown,
    };

    // Load program
    let prog = load_program_from_elf(path, section);
    if prog.instrs.is_empty() {
        return AnalysisResult::LoadError("Empty program".to_string());
    }

    if verbose {
        println!("  Program size: {} instructions", prog.instrs.len());
    }

    // Run analysis with config
    let entry = make_entry_state(&ctx);
    let result = analysis::analyze_program(&ctx, &prog, entry, config);

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

/// Check if a section contains BPF code
fn is_code_section(name: &str) -> bool {
    if name.is_empty() { return false; }
    if name.starts_with('.') { return false; }
    if name == "license" || name == "version" || name == "maps" { return false; }
    true
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        usage();
        return;
    }

    // Parse config flags and get remaining positional args
    let (config, remaining) = VerifierConfig::from_args(&args[1..]);

    // Initialize logging
    logging::VerifierLogger::init(config.verbosity);

    // If debug_pc is set, configure logging filter
    if let Some(target_pc) = config.debug_pc {
        let filter = FilterConfig {
            // Buffer logs in a window around the target PC
            pc_range: Some(target_pc.saturating_sub(10)..=target_pc + 10),
            interesting_regs: vec![], // All regs
        };
        logging::VerifierLogger::set_config(filter);
    }
    
    if remaining.is_empty() {
        usage();
        return;
    }

    let cmd = &remaining[0];

    match cmd.as_str() {
        // ============================================================
        // List all sections and programs in an ELF
        // ============================================================
        "elf-list" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &remaining[1];

            println!("=== ELF Contents: '{}' ===\n", path);

            println!("--- SECTIONS ---");
            match list_section_names(path) {
                Ok(sections) => {
                    for (i, name) in sections.iter().enumerate() {
                        if is_code_section(name) {
                            println!("  [{}] {}", i, name);
                        }
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }

            println!("\n--- BPF PROGRAMS ---");
            match load_raw_programs(path) {
                Ok(progs) => {
                    for (i, p) in progs.iter().enumerate() {
                        println!("  [{}] {} ({} insns)", i, p.name, p.data.len() / 8);
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }

            println!("\n--- BPF MAPS ---");
            match load_maps(path) {
                Ok(maps) => {
                    for (i, m) in maps.iter().enumerate() {
                        println!("  [{}] {} (k:{}, v:{})", i, m.name, m.key_size, m.value_size);
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }
        }

        // ============================================================
        // Analyze by section name
        // ============================================================
        "elf-analyze" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &remaining[1];
            let section = &remaining[2];

            println!("=== Analyzing: '{}' section '{}' ===", path, section);

            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
            let btf_ctx = if !btf_bytes.is_empty() {
                btf::parse_btf(&btf_bytes).unwrap_or_else(|e| {
                    println!("BTF Parse Error: {}", e);
                    btf::BtfContext::new()
                })
            } else {
                btf::BtfContext::new()
            };

            let result = analyze_section(path, section, &btf_ctx, &config, true);
            
            match result {
                AnalysisResult::Pass => println!("\n=== PASS ==="),
                AnalysisResult::Fail(e) => println!("\n=== FAIL: {} ===", e.description()),
                AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
            }
        }

        // ============================================================
        // Analyze by function name
        // ============================================================
        "elf-analyze-func" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &remaining[1];
            let func_name = &remaining[2];

            println!("=== Analyzing function: '{}' in '{}' ===", func_name, path);

            let progs = match load_raw_programs(path) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("Error: {:?}", e);
                    return;
                }
            };

            let target = progs.iter().find(|p| p.name == *func_name);
            if target.is_none() {
                eprintln!("Function '{}' not found. Available:", func_name);
                for p in &progs { eprintln!("  - {}", p.name); }
                return;
            }
            let target = target.unwrap();

            let sections = list_section_names(path).unwrap_or_default();
            let section_name = sections.get(target.section_idx).map(|s| s.as_str()).unwrap_or("unknown");

            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
            let btf_ctx = if !btf_bytes.is_empty() {
                btf::parse_btf(&btf_bytes).unwrap_or_default()
            } else {
                btf::BtfContext::new()
            };

            let result = analyze_section(path, section_name, &btf_ctx, &config, true);
            
            match result {
                AnalysisResult::Pass => println!("\n=== PASS ==="),
                AnalysisResult::Fail(e) => println!("\n=== FAIL: {} ===", e.description()),
                AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
            }
        }

        // ============================================================
        // Batch analyze all sections
        // ============================================================
        "analyze-batch" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &remaining[1];

            println!("=== Batch Analysis: '{}' ===\n", path);
            println!("Config: max_insn={}, skip_dbm={}, verbosity={}", 
                     config.max_insn, config.skip_dbm_check, config.verbosity);

            let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
            let btf_ctx = if !btf_bytes.is_empty() {
                btf::parse_btf(&btf_bytes).unwrap_or_default()
            } else {
                btf::BtfContext::new()
            };

            let sections = list_section_names(path).unwrap_or_default();
            let section_to_func = build_section_to_func_map(path);

            let code_sections: Vec<(usize, &String)> = sections.iter()
                .enumerate()
                .filter(|(_, name)| is_code_section(name))
                .collect();

            println!("Found {} code sections\n", code_sections.len());

            let mut results: Vec<(String, String, AnalysisResult)> = Vec::new();
            let mut pass_count = 0;
            let mut fail_count = 0;
            let mut error_count = 0;

            for (idx, section_name) in &code_sections {
                let func_name = section_to_func.get(idx).map(|s| s.as_str()).unwrap_or("-");
                
                print!("[{}/{}] '{}' ({})... ", 
                       results.len() + 1, code_sections.len(), section_name, func_name);
                
                let result = analyze_section(path, section_name, &btf_ctx, &config, false);
                
                match &result {
                    AnalysisResult::Pass => {
                        println!("PASS");
                        pass_count += 1;
                    }
                    AnalysisResult::Fail(_) => {
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

            // Summary
            println!("\n========================================");
            println!("              SUMMARY");
            println!("========================================");
            println!("Total:  {}", code_sections.len());
            println!("Pass:   {} ({:.1}%)", pass_count, 100.0 * pass_count as f64 / code_sections.len() as f64);
            println!("Fail:   {}", fail_count);
            println!("Errors: {}", error_count);

            if fail_count > 0 {
                println!("\n--- FAILURES ---");
                for (section, func, result) in &results {
                    if let AnalysisResult::Fail(e) = result {
                        println!("  {} ({}): {}", section, func, e.description());
                    }
                }
            }

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
