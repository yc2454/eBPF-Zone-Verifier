// src/main.rs - With configurable verifier options

mod ast;
mod analysis;
mod parsing;
mod zone;
mod misc;
mod logging;
mod runner;
mod benchmark;

use crate::misc::config::VerifierConfig;
use crate::parsing::elf_loader::{load_maps, load_raw_programs, list_section_names};
use crate::logging::{FilterConfig};
use crate::runner::{Analyzer, AnalysisResult, find_section_for_func, is_code_section};
use crate::benchmark::analyze_benchmark;

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- [flags] elf-list        <elf_path>");
    eprintln!("  cargo run -- [flags] elf-analyze     <elf_path> <section_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-func <elf_path> <func_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-prog <elf_path>");
    eprintln!("  cargo run -- [flags] elf-analyze-benchmark <dir_path>");
    eprintln!("");
    VerifierConfig::print_help();
    eprintln!("");
    eprintln!("Examples:");
    eprintln!("  cargo run -- elf-list ./bpf_host.o");
    eprintln!("  cargo run -- elf-analyze ./bpf_host.o tc");
    eprintln!("  cargo run -- elf-analyze-benchmark ./bpf-progs --project cilium");
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
            pc_range: Some(target_pc.saturating_sub(10)..=target_pc + 10),
            interesting_regs: vec![],
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
        "elf-analyze-section" | "elf-analyze" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &remaining[1];
            let section = &remaining[2];

            println!("=== Analyzing: '{}' section '{}' ===", path, section);
            
            let analyzer = Analyzer::new(path, config);
            let result = analyzer.analyze_section(section);
            
            match result {
                AnalysisResult::Pass => println!("\n=== PASS ==="),
                AnalysisResult::Fail(e) => println!("\n=== FAIL: {} ===", e.description()),
                AnalysisResult::Timeout => println!("\n=== TIMEOUT: Complexity limit reached ==="),
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

            if let Some(section_name) = find_section_for_func(path, func_name) {
                let analyzer = Analyzer::new(path, config);
                let result = analyzer.analyze_section(&section_name);
                
                match result {
                    AnalysisResult::Pass => println!("\n=== PASS ==="),
                    AnalysisResult::Fail(e) => println!("\n=== FAIL: {} ===", e.description()),
                    AnalysisResult::Timeout => println!("\n=== TIMEOUT: Complexity limit reached ==="),
                    AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
                }
            } else {
                eprintln!("Function '{}' not found or section lookup failed.", func_name);
            }
        }

        // ============================================================
        // Batch analyze all sections in an ELF
        // ============================================================
        "elf-analyze-prog" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &remaining[1];

            println!("=== Batch Analysis: '{}' ===\n", path);
            println!("Config: max_insn={}, skip_dbm={}, verbosity={}", 
                     config.max_insn, config.skip_dbm_check, config.verbosity);

            let analyzer = Analyzer::new(path, config);
            let (_, results) = analyzer.analyze_all();

            let mut pass_count = 0;
            let mut fail_count = 0;
            let mut timeout_count = 0;
            let mut error_count = 0;

            for (section, res) in &results {
                print!("Section '{}'... ", section);
                match res {
                    AnalysisResult::Pass => {
                        println!("PASS");
                        pass_count += 1;
                    },
                    AnalysisResult::Fail(_) => {
                        println!("FAIL");
                        fail_count += 1;
                    },
                    AnalysisResult::Timeout => {
                        println!("TIMEOUT");
                        timeout_count += 1;
                    },
                    AnalysisResult::LoadError(e) => {
                        println!("ERROR ({})", e);
                        error_count += 1;
                    }
                }
            }

            println!("\n========================================");
            println!("              SUMMARY");
            println!("========================================");
            println!("Total:  {}", results.len());
            if !results.is_empty() {
                println!("Pass:   {} ({:.1}%)", pass_count, 100.0 * pass_count as f64 / results.len() as f64);
            }
            println!("Fail:   {}", fail_count);
            println!("Timeout: {}", timeout_count);
            println!("Errors: {}", error_count);

            if fail_count > 0 {
                println!("\n--- FAILURES ---");
                for (section, res) in &results {
                    if let AnalysisResult::Fail(e) = res {
                        println!("  {}: {}", section, e.description());
                    }
                }
            }
            println!("\n=== Done ===");
        }

        // ============================================================
        // BENCHMARK COMMAND (Recursive directory analysis)
        // ============================================================
        "elf-analyze-benchmark" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing benchmark directory path");
                usage();
                return;
            }
            let dir_path = &remaining[1];
            analyze_benchmark(dir_path, &config);
        }

        _ => {
            eprintln!("Unknown command: {}", cmd);
            usage();
        }
    }
}