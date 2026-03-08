// src/main.rs - With configurable verifier options

mod analysis;
mod ast;
mod common;
mod domains;
mod parsing;
mod pcc;
mod testing;

use crate::ast::ProgramKind;
use crate::common::config::{DomainMode, VerifierConfig};
use crate::parsing::elf::program_kind_for_object;
use crate::parsing::elf::{list_section_names, load_maps, load_raw_programs};
use crate::pcc::ProgramCertificate;
use crate::testing::bcf_benchmark::analyze_benchmark;
use crate::testing::logging;
use crate::testing::pcc_test::{pcc_cert_run, pcc_test_single};
use crate::testing::prevail::{prevail_benchmark, prevail_list, prevail_run, prevail_single};
use crate::testing::runner::{AnalysisResult, Analyzer, find_section_for_func, is_code_section};
use crate::testing::selftest::{selftest_list, selftest_run, selftest_single, selftest_suite};
use std::path::Path;

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- [flags] elf-list        <elf_path>");
    eprintln!("  cargo run -- [flags] elf-analyze     <elf_path> <section_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-func <elf_path> <func_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-prog <elf_path>");
    eprintln!("  cargo run -- [flags] bcf-benchmark   <dir_path>");
    eprintln!("  cargo run -- [flags] selftest-list   <json_file>");
    eprintln!("  cargo run -- [flags] selftest-single <json_file> <test_name>");
    eprintln!("  cargo run -- [flags] selftest-run    <json_file>");
    eprintln!("  cargo run -- [flags] selftest-suite  <json_dir>");
    eprintln!("  cargo run -- [flags] pcc-gen         <json_file> <test_name> [cert_out]");
    eprintln!("  cargo run -- [flags] pcc-check       <json_file> <test_name> <cert_path>");
    eprintln!("  cargo run -- [flags] pcc-cycle       <json_file> <test_name> [cert_out]");
    eprintln!("  cargo run -- [flags] pcc-regress     [cert_cases.json]");
    eprintln!("  cargo run -- [flags] prevail-list    <catalogue.json>");
    eprintln!("  cargo run -- [flags] prevail-run     <catalogue.json>");
    eprintln!("  cargo run -- [flags] prevail-single  <catalogue.json> <test_name>");
    eprintln!("  cargo run -- [flags] prevail-benchmark <dir_path>");
    eprintln!("  cargo run -- [flags] benchmark-scan    <dir_path> <output.json>");
    eprintln!();
    VerifierConfig::print_help();
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  cargo run -- elf-list ./bpf_host.o");
    eprintln!("  cargo run -- elf-analyze ./bpf_host.o tc");
    eprintln!("  cargo run -- bcf-benchmark ./bpf-progs --project cilium");
    eprintln!("  cargo run -- prevail-benchmark ~/ebpf-samples --project cilium");
    eprintln!("  cargo run -- selftest-list <json_file>");
    eprintln!("  cargo run -- selftest-single <json_file> <test_name>");
    eprintln!("  cargo run -- selftest-run <json_file>");
    eprintln!("  cargo run -- selftest-suite <json_dir>");
    eprintln!("  cargo run -- pcc-gen pcc-tests/pcc_examples.json \"pcc motivating: var add packet access (zone ok, kernel reject)\"");
    eprintln!("  cargo run -- pcc-check pcc-tests/pcc_examples.json \"pcc motivating: var add packet access (zone ok, kernel reject)\" pcc-tests/certs/pcc_examples.valid.cert.json");
    eprintln!("  cargo run -- pcc-cycle pcc-tests/pcc_examples.json \"pcc motivating: var add packet access (zone ok, kernel reject)\"");
    eprintln!("  cargo run -- pcc-regress");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        usage();
        return;
    }

    // Parse config flags and get remaining positional args
    let (mut config, remaining) = VerifierConfig::from_args(&args[1..]);

    if config.certificate_output.is_some() && config.certificate_input.is_some() {
        eprintln!(
            "Error: --generate-certificate and --certificate-aided-analysis cannot be used together"
        );
        return;
    }
    if config.certificate_output.is_some() && config.domain_mode != DomainMode::Zone {
        eprintln!("Error: --generate-certificate currently requires --zone-mode");
        return;
    }

    if let Some(path) = &config.certificate_input {
        match ProgramCertificate::load_from_path(path) {
            Ok(cert) => config.certificate = Some(cert),
            Err(e) => {
                eprintln!("Error: invalid certificate file '{}': {e:#}", path);
                return;
            }
        };
    }

    // Initialize logging
    logging::VerifierLogger::init(config.verbosity);

    // If debug_pc is set, configure logging filter
    if let Some(target_pc) = config.debug_pc {
        let filter = logging::FilterConfig {
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

    if config.certificate_output.is_some() && cmd != "pcc-gen" && cmd != "pcc-cycle" {
        eprintln!(
            "Error: --generate-certificate is supported only with pcc-gen or pcc-cycle"
        );
        return;
    }

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
                            let kind = match program_kind_for_object(Path::new(path)) {
                                Ok(k) => k,
                                Err(_) => ProgramKind::from_section(name),
                            };
                            println!("  [{}] {} (Kind: {:?})", i, name, kind);
                        }
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }
            println!("\n--- BPF PROGRAMS ---");
            match load_raw_programs(path) {
                Ok(progs) => {
                    let mut sections = Vec::new();
                    if let Ok(s) = list_section_names(path) {
                        sections = s;
                    }

                    for (i, p) in progs.iter().enumerate() {
                        let section_name = sections
                            .get(p.section_idx)
                            .map(|s| s.as_str())
                            .unwrap_or("");
                        let kind = match program_kind_for_object(Path::new(path)) {
                            Ok(k) => k,
                            Err(_) => ProgramKind::from_section(section_name),
                        };
                        println!(
                            "  [{}] {} ({} insns) [Section: {}, Kind: {:?}]",
                            i,
                            p.name,
                            p.data.len() / 8,
                            section_name,
                            kind
                        );
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }
            println!("\n--- BPF MAPS ---");
            match load_maps(path) {
                Ok(maps) => {
                    for (i, m) in maps.iter().enumerate() {
                        println!(
                            "  [{}] {} (k:{}, v:{})",
                            i, m.name, m.key_size, m.value_size
                        );
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
                    AnalysisResult::Timeout => {
                        println!("\n=== TIMEOUT: Complexity limit reached ===")
                    }
                    AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
                }
            } else {
                eprintln!(
                    "Function '{}' not found or section lookup failed.",
                    func_name
                );
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
            println!(
                "Config: max_insn={}, skip_dbm={}, verbosity={}",
                config.max_insn, config.skip_dbm_check, config.verbosity
            );

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
                    }
                    AnalysisResult::Fail(_) => {
                        println!("FAIL");
                        fail_count += 1;
                    }
                    AnalysisResult::Timeout => {
                        println!("TIMEOUT");
                        timeout_count += 1;
                    }
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
                println!(
                    "Pass:   {} ({:.1}%)",
                    pass_count,
                    100.0 * pass_count as f64 / results.len() as f64
                );
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
        // BCF BENCHMARK COMMAND (Recursive directory analysis)
        // ============================================================
        "bcf-benchmark" | "elf-analyze-benchmark" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing benchmark directory path");
                usage();
                return;
            }
            let dir_path = &remaining[1];
            analyze_benchmark(dir_path, &config);
        }

        // ============================================================
        // Selftest: Run single JSON test file
        // ============================================================
        "selftest-run" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing JSON test file path");
                usage();
                return;
            }
            let json_path = &remaining[1];
            let output_dir = Some("./results/selftest");

            selftest_run(json_path, &config, output_dir);
        }

        // ============================================================
        // Selftest: Run all JSON files in directory
        // ============================================================
        "selftest-suite" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing JSON test directory path");
                usage();
                return;
            }
            let json_dir = &remaining[1];
            let output_dir = Some("./results/selftest");

            selftest_suite(json_dir, &config, output_dir);
        }

        // ============================================================
        // Selftest: List all tests in a JSON file
        // ============================================================
        "selftest-list" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing JSON test file path");
                usage();
                return;
            }
            let json_path = &remaining[1];

            selftest_list(json_path);
        }

        // ============================================================
        // Selftest: Run a single test by name
        // ============================================================
        "selftest-single" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                eprintln!("Usage: selftest-single <json_file> <test_name>");
                return;
            }
            let json_path = &remaining[1];
            let test_name = &remaining[2];

            selftest_single(json_path, test_name, &config);
        }

        // ============================================================
        // PCC: generate certificate (zone mode enforced)
        // ============================================================
        "pcc-gen" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                eprintln!("Usage: pcc-gen <json_file> <test_name> [cert_out]");
                return;
            }
            let mut cfg = config.clone();
            cfg.domain_mode = DomainMode::Zone;
            cfg.detect_bounded_loops = true;
            cfg.require_single_loop_entry = false;
            cfg.certificate = None;
            cfg.certificate_input = None;
            cfg.certificate_output = remaining.get(3).cloned();
            pcc_test_single(&remaining[1], &remaining[2], &cfg);
        }

        // ============================================================
        // PCC: cert-aided check (kernel mode enforced)
        // ============================================================
        "pcc-check" => {
            if remaining.len() < 4 {
                eprintln!("Error: Missing arguments");
                eprintln!("Usage: pcc-check <json_file> <test_name> <cert_path>");
                return;
            }
            let cert = match ProgramCertificate::load_from_path(&remaining[3]) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("Error: invalid certificate file '{}': {e:#}", &remaining[3]);
                    return;
                }
            };
            let mut cfg = config.clone();
            cfg.domain_mode = DomainMode::Interval;
            cfg.detect_bounded_loops = false;
            cfg.require_single_loop_entry = true;
            cfg.certificate_output = None;
            cfg.certificate_input = None;
            cfg.certificate = Some(cert);
            pcc_test_single(&remaining[1], &remaining[2], &cfg);
        }

        // ============================================================
        // PCC: generate + check in one command
        // ============================================================
        "pcc-cycle" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                eprintln!("Usage: pcc-cycle <json_file> <test_name> [cert_out]");
                return;
            }
            let cert_out = remaining
                .get(3)
                .cloned()
                .unwrap_or_else(|| "/tmp/pcc_cycle.cert.json".to_string());

            let mut gen_cfg = config.clone();
            gen_cfg.domain_mode = DomainMode::Zone;
            gen_cfg.detect_bounded_loops = true;
            gen_cfg.require_single_loop_entry = false;
            gen_cfg.certificate = None;
            gen_cfg.certificate_input = None;
            gen_cfg.certificate_output = Some(cert_out.clone());

            pcc_test_single(&remaining[1], &remaining[2], &gen_cfg);

            if !Path::new(&cert_out).exists() {
                eprintln!(
                    "Error: certificate was not generated at '{}'; skipping cert-aided check",
                    cert_out
                );
                return;
            }

            let cert = match ProgramCertificate::load_from_path(&cert_out) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("Error: generated certificate is invalid '{}': {e:#}", cert_out);
                    return;
                }
            };

            let mut check_cfg = config.clone();
            check_cfg.domain_mode = DomainMode::Interval;
            check_cfg.detect_bounded_loops = false;
            check_cfg.require_single_loop_entry = true;
            check_cfg.certificate_output = None;
            check_cfg.certificate_input = None;
            check_cfg.certificate = Some(cert);

            pcc_test_single(&remaining[1], &remaining[2], &check_cfg);
        }

        // ============================================================
        // PCC: run regression manifest
        // ============================================================
        "pcc-regress" => {
            let manifest = remaining
                .get(1)
                .map(|s| s.as_str())
                .unwrap_or("pcc-tests/cert_cases.json");
            pcc_cert_run(manifest, &config);
        }

        // ============================================================
        // PREVAIL: List all tests in catalogue
        // ============================================================
        "prevail-list" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing catalogue path");
                usage();
                return;
            }
            let catalogue_path = &remaining[1];
            prevail_list(catalogue_path);
        }

        // ============================================================
        // PREVAIL: Run all tests in catalogue
        // ============================================================
        "prevail-run" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing catalogue path");
                usage();
                return;
            }
            let catalogue_path = &remaining[1];
            let output_dir = Some("./results/prevail");

            prevail_run(catalogue_path, &config, output_dir);
        }

        // ============================================================
        // PREVAIL: Run a single test by name
        // ============================================================
        "prevail-single" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                eprintln!("Usage: prevail-single <catalogue.json> <test_name>");
                return;
            }
            let catalogue_path = &remaining[1];
            let test_name = &remaining[2];

            prevail_single(catalogue_path, test_name, &config);
        }

        // ============================================================
        // PREVAIL: Run benchmark on all ELF files in a directory
        // ============================================================
        "prevail-benchmark" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing directory path");
                eprintln!("Usage: prevail-benchmark <dir_path> [--project <name>]");
                return;
            }
            let dir_path = &remaining[1];
            let output_dir = Some("./results/prevail");

            prevail_benchmark(dir_path, &config, output_dir);
        }

        // ============================================================
        // Benchmark Scan: Export ELF metadata to JSON
        // ============================================================
        "benchmark-scan" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                eprintln!("Usage: benchmark-scan <dir_path> <output.json>");
                return;
            }
            let dir_path = &remaining[1];
            let output_json = &remaining[2];
            if let Err(e) = crate::testing::scanner::scan_benchmark_dir(dir_path, output_json) {
                eprintln!("Error: {:?}", e);
            }
        }

        _ => {
            eprintln!("Unknown command: {}", cmd);
            usage();
        }
    }
}
