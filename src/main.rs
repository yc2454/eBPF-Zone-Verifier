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
use crate::testing::legacy_selftest::{selftest_list, selftest_run, selftest_single, selftest_suite};
use std::path::Path;

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- [flags] elf-list        <elf_path>");
    eprintln!("  cargo run -- [flags] elf-analyze     <elf_path> <section_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-func <elf_path> <func_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-prog <elf_path>");
    eprintln!("  cargo run -- [flags] bcf-benchmark   <dir_path>");
    eprintln!("  cargo run -- [flags] selftest-suite          <progs_dir>");
    eprintln!("  cargo run -- [flags] selftest-file           <prog.c> [defines]");
    eprintln!("  cargo run -- [flags] selftest-baseline-write        <progs_dir> <legacy_json_dir> <out.json>");
    eprintln!("  cargo run -- [flags] selftest-baseline-check        <progs_dir> <legacy_json_dir> <baseline.json>");
    eprintln!("  cargo run -- [flags] selftest-baseline-check-modern <progs_dir> <baseline.json>           (fast: skips legacy)");
    eprintln!("  cargo run -- [flags] btf-dump-struct-ops <elf_path> <struct_name>                        (diagnostic for W6.4a)");
    eprintln!("  cargo run -- [flags] legacy-selftest-list   <json_file>");
    eprintln!("  cargo run -- [flags] legacy-selftest-single <json_file> <test_name>");
    eprintln!("  cargo run -- [flags] legacy-selftest-run    <json_file>");
    eprintln!("  cargo run -- [flags] legacy-selftest-suite  <json_dir>");
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
    eprintln!(
        "  cargo run -- pcc-gen pcc-tests/pcc_examples.json \"pcc motivating: var add packet access (zone ok, kernel reject)\""
    );
    eprintln!(
        "  cargo run -- pcc-check pcc-tests/pcc_examples.json \"pcc motivating: var add packet access (zone ok, kernel reject)\" pcc-tests/certs/pcc_examples.valid.cert.json"
    );
    eprintln!(
        "  cargo run -- pcc-cycle pcc-tests/pcc_examples.json \"pcc motivating: var add packet access (zone ok, kernel reject)\""
    );
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
        eprintln!("Error: --generate-certificate is supported only with pcc-gen or pcc-cycle");
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
        // ============================================================
        // Selftest (modern): compile + run upstream .c sources
        // ============================================================
        "selftest-file" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing .c source path");
                usage();
                return;
            }
            run_modern_selftest_file(&remaining[1], remaining.get(2).map(|s| s.as_str()), &config);
        }
        "selftest-suite" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing progs/ directory path");
                usage();
                return;
            }
            run_modern_selftest_dir(&remaining[1], &config);
        }
        "selftest-baseline-write" => {
            if remaining.len() < 4 {
                eprintln!("Usage: selftest-baseline-write <progs_dir> <legacy_json_dir> <out.json>");
                return;
            }
            run_baseline_write(&remaining[1], &remaining[2], &remaining[3], &config);
        }
        "selftest-baseline-check" => {
            if remaining.len() < 4 {
                eprintln!("Usage: selftest-baseline-check <progs_dir> <legacy_json_dir> <baseline.json>");
                return;
            }
            run_baseline_check(&remaining[1], &remaining[2], &remaining[3], &config);
        }
        "selftest-baseline-check-modern" => {
            if remaining.len() < 3 {
                eprintln!("Usage: selftest-baseline-check-modern <progs_dir> <baseline.json>");
                return;
            }
            run_baseline_check_modern(&remaining[1], &remaining[2], &config);
        }
        "btf-dump-struct-ops" => {
            if remaining.len() < 3 {
                eprintln!("Usage: btf-dump-struct-ops <elf_path> <struct_name>");
                eprintln!("Diagnostic: walk the BTF for <struct_name>, list each member that");
                eprintln!("resolves to a `PTR -> FUNC_PROTO` (i.e. a struct_ops method), and");
                eprintln!("print the parameter list as the W6.4a entry-state plumbing sees it.");
                return;
            }
            run_btf_dump_struct_ops(&remaining[1], &remaining[2]);
        }
        "btf-dump-func" => {
            if remaining.len() < 3 {
                eprintln!("Usage: btf-dump-func <elf_path> <func_name>");
                eprintln!("Diagnostic: print the parameter list of <func_name> as recorded");
                eprintln!("in BTF. For struct_ops subprogs this is the same answer the");
                eprintln!("entry-state plumbing uses — without needing to know which");
                eprintln!("ops-struct member the subprog binds to.");
                return;
            }
            run_btf_dump_func(&remaining[1], &remaining[2]);
        }

        // ============================================================
        // Legacy selftest (pre-6.2 JSON corpus)
        // ============================================================
        "legacy-selftest-run" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing JSON test file path");
                usage();
                return;
            }
            let json_path = &remaining[1];
            let output_dir = Some("./results/selftest");

            selftest_run(json_path, &config, output_dir);
        }

        "legacy-selftest-suite" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing JSON test directory path");
                usage();
                return;
            }
            let json_dir = &remaining[1];
            let output_dir = Some("./results/selftest");

            selftest_suite(json_dir, &config, output_dir);
        }

        "legacy-selftest-list" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing JSON test file path");
                usage();
                return;
            }
            let json_path = &remaining[1];

            selftest_list(json_path);
        }

        "legacy-selftest-single" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                eprintln!("Usage: legacy-selftest-single <json_file> <test_name>");
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

            println!("\n====== Phase 1 / Certificate Generation (zone mode) ======\n");
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
                    eprintln!(
                        "Error: generated certificate is invalid '{}': {e:#}",
                        cert_out
                    );
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

            println!("\n====== Phase 2 / PCC Certificate Check (interval mode) ======\n");
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

// ============================================================
// Modern selftest helpers
// ============================================================

fn parse_extra_defines(arg: Option<&str>) -> Vec<String> {
    arg.map(|s| s.split(',').filter(|t| !t.is_empty()).map(String::from).collect())
        .unwrap_or_default()
}

fn run_modern_selftest_file(src: &str, defines_arg: Option<&str>, config: &VerifierConfig) {
    use crate::testing::selftest::clang::DEFAULT_HEADERS_TAG;
    use crate::testing::selftest::runner;

    let headers = std::path::PathBuf::from("selftests/headers").join(DEFAULT_HEADERS_TAG);
    let defines = parse_extra_defines(defines_arg);
    let define_refs: Vec<&str> = defines.iter().map(|s| s.as_str()).collect();

    match runner::run_file(std::path::Path::new(src), &headers, &define_refs, config) {
        Ok(report) => print_modern_report(&report),
        Err(e) => eprintln!("Error: {e:?}"),
    }
}

fn run_modern_selftest_dir(dir: &str, config: &VerifierConfig) {
    use crate::testing::selftest::clang::DEFAULT_HEADERS_TAG;
    use crate::testing::selftest::runner;

    let headers = std::path::PathBuf::from("selftests/headers").join(DEFAULT_HEADERS_TAG);
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Error reading {dir}: {e}");
            return;
        }
    };

    let mut totals = (0usize, 0usize, 0usize, 0usize, 0usize); // pass, false_reject, false_accept, skipped, error
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("c") {
            continue;
        }
        match runner::run_file(&path, &headers, &[], config) {
            Ok(report) => {
                print_modern_report(&report);
                for p in &report.progs {
                    use crate::testing::selftest::runner::Outcome;
                    match p.outcome {
                        Outcome::Pass => totals.0 += 1,
                        Outcome::FalseReject(_) => totals.1 += 1,
                        Outcome::FalseAccept => totals.2 += 1,
                        Outcome::Skipped(_) => totals.3 += 1,
                        Outcome::Error(_) => totals.4 += 1,
                    }
                }
            }
            Err(e) => eprintln!("Error on {}: {e:?}", path.display()),
        }
    }
    println!("\n=== Suite summary ===");
    println!(
        "  pass={}  false_reject={}  false_accept={}  skipped={}  error={}",
        totals.0, totals.1, totals.2, totals.3, totals.4
    );
}

fn collect_json_recursive(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let p = entry.path();
        if p.is_dir() {
            collect_json_recursive(&p, out);
        } else if p.extension().and_then(|s| s.to_str()) == Some("json") {
            out.push(p);
        }
    }
}

fn sweep_modern_and_legacy(
    progs_dir: &str,
    legacy_json_dir: &str,
    config: &VerifierConfig,
    filter: &dyn crate::testing::selftest::runner::ProgFilter,
) -> crate::testing::selftest::baseline::Baseline {
    use crate::testing::legacy_selftest;
    use crate::testing::selftest::baseline::Baseline;
    use crate::testing::selftest::clang::DEFAULT_HEADERS_TAG;
    use crate::testing::selftest::runner;

    let headers = std::path::PathBuf::from("selftests/headers").join(DEFAULT_HEADERS_TAG);
    let modern = runner::run_dir_filtered(std::path::Path::new(progs_dir), &headers, config, filter)
        .unwrap_or_else(|e| {
            eprintln!("Error sweeping modern {progs_dir}: {e:?}");
            Vec::new()
        });
    let mut bl = Baseline::from_reports(DEFAULT_HEADERS_TAG, &modern);

    // Legacy JSON sweep — recurse, picking up `*.json` under the dir.
    let mut legacy_files = Vec::new();
    collect_json_recursive(std::path::Path::new(legacy_json_dir), &mut legacy_files);
    legacy_files.sort();
    // Parallelize legacy file iteration. Each `.json` file is fully
    // independent; rayon walks them concurrently across cores. Within a
    // file, tests still run sequentially — a file-level granularity is
    // enough since most files have similar sizes.
    //
    // Also apply `with_selftest_caps` to the legacy config: without it,
    // the default `max_insn = 1M` lets a handful of pathological tests
    // run for many seconds each, dominating wallclock.
    use crate::testing::selftest::runner::with_selftest_caps;
    use rayon::prelude::*;
    let legacy_config = with_selftest_caps(config);
    let legacy_results: Vec<_> = legacy_files
        .par_iter()
        .filter_map(|path| match legacy_selftest::run_test_file(
            path.to_str().unwrap(),
            &legacy_config,
        ) {
            Ok(r) => Some(r),
            Err(e) => {
                eprintln!("Error on legacy {}: {e}", path.display());
                None
            }
        })
        .collect();
    bl.extend_with_legacy(&legacy_results);
    bl
}

fn sweep_modern_only(
    progs_dir: &str,
    config: &VerifierConfig,
    filter: &dyn crate::testing::selftest::runner::ProgFilter,
) -> crate::testing::selftest::baseline::Baseline {
    use crate::testing::selftest::baseline::Baseline;
    use crate::testing::selftest::clang::DEFAULT_HEADERS_TAG;
    use crate::testing::selftest::runner;

    let headers = std::path::PathBuf::from("selftests/headers").join(DEFAULT_HEADERS_TAG);
    let modern = runner::run_dir_filtered(std::path::Path::new(progs_dir), &headers, config, filter)
        .unwrap_or_else(|e| {
            eprintln!("Error sweeping modern {progs_dir}: {e:?}");
            Vec::new()
        });
    Baseline::from_reports(DEFAULT_HEADERS_TAG, &modern)
}

fn run_btf_dump_struct_ops(elf_path: &str, struct_name: &str) {
    use crate::parsing::btf::{self, StructOpsArg};
    use goblin::elf::Elf;

    let bytes = match std::fs::read(elf_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("read {elf_path}: {e}");
            std::process::exit(2);
        }
    };
    let elf = match Elf::parse(&bytes) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("parse ELF {elf_path}: {e}");
            std::process::exit(2);
        }
    };
    let mut btf_bytes: Option<&[u8]> = None;
    for sh in &elf.section_headers {
        let name = elf
            .shdr_strtab
            .get_at(sh.sh_name)
            .unwrap_or("");
        if name == ".BTF" {
            let start = sh.sh_offset as usize;
            let end = start + sh.sh_size as usize;
            if end <= bytes.len() {
                btf_bytes = Some(&bytes[start..end]);
            }
            break;
        }
    }
    let Some(raw) = btf_bytes else {
        eprintln!("no .BTF section in {elf_path}");
        std::process::exit(2);
    };
    let ctx = match btf::parse_btf(raw) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("parse BTF: {e}");
            std::process::exit(2);
        }
    };
    let Some(struct_id) = ctx.find_struct_by_name(struct_name) else {
        eprintln!("struct `{struct_name}` not found in BTF");
        std::process::exit(1);
    };
    println!("struct {struct_name} (btf_id {struct_id})");
    let ty = ctx.types.get(&struct_id).unwrap();
    let mut hits = 0usize;
    for m in &ty.members {
        let mname = ctx.read_string(m.name_off).unwrap_or("?");
        // We only print members that look like struct_ops methods — those
        // resolve to a `PTR -> FUNC_PROTO` chain.
        let Some(pointee_id) = ctx.pointee(m.type_id) else {
            continue;
        };
        let Some(pointee) = ctx.types.get(&pointee_id) else {
            continue;
        };
        if pointee.kind() != btf::BTF_KIND_FUNC_PROTO {
            continue;
        }
        hits += 1;
        let args = ctx
            .resolve_struct_ops_method(struct_name, mname)
            .unwrap_or_default();
        let pretty = args
            .iter()
            .map(|a| match a {
                StructOpsArg::Scalar => "scalar".to_string(),
                StructOpsArg::TrustedPtr(n) => format!("ptr<{n}>"),
                StructOpsArg::OpaquePtr => "ptr<?>".to_string(),
            })
            .collect::<Vec<_>>()
            .join(", ");
        println!("  .{mname:30} ({pretty})");
    }
    println!("({hits} method(s))");
}

fn run_btf_dump_func(elf_path: &str, func_name: &str) {
    use crate::parsing::btf::{self, StructOpsArg};
    use goblin::elf::Elf;

    let bytes = std::fs::read(elf_path).unwrap_or_else(|e| {
        eprintln!("read {elf_path}: {e}");
        std::process::exit(2);
    });
    let elf = Elf::parse(&bytes).unwrap_or_else(|e| {
        eprintln!("parse ELF: {e}");
        std::process::exit(2);
    });
    let mut btf_bytes: Option<&[u8]> = None;
    for sh in &elf.section_headers {
        if elf.shdr_strtab.get_at(sh.sh_name).unwrap_or("") == ".BTF" {
            let s = sh.sh_offset as usize;
            let e = s + sh.sh_size as usize;
            if e <= bytes.len() {
                btf_bytes = Some(&bytes[s..e]);
            }
            break;
        }
    }
    let raw = btf_bytes.unwrap_or_else(|| {
        eprintln!("no .BTF section");
        std::process::exit(2);
    });
    let ctx = btf::parse_btf(raw).unwrap_or_else(|e| {
        eprintln!("parse BTF: {e}");
        std::process::exit(2);
    });
    let Some(args) = ctx.resolve_func_args(func_name) else {
        eprintln!("FUNC `{func_name}` not found in BTF (or no FUNC_PROTO)");
        std::process::exit(1);
    };
    let pretty = args
        .iter()
        .map(|a| match a {
            StructOpsArg::Scalar => "scalar".to_string(),
            StructOpsArg::TrustedPtr(n) => format!("ptr<{n}>"),
            StructOpsArg::OpaquePtr => "ptr<?>".to_string(),
        })
        .collect::<Vec<_>>()
        .join(", ");
    println!("{func_name}({pretty})");
}

fn run_baseline_check_modern(progs_dir: &str, stored: &str, config: &VerifierConfig) {
    use crate::testing::selftest::baseline::{Baseline, CheckFilter, DeterministicFilter, diff};

    let mut baseline = match Baseline::read(stored) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("Error reading baseline {stored}: {e:?}");
            std::process::exit(2);
        }
    };
    // Ignore legacy entries on both sides — modern-only check is for
    // the day-to-day phase-advance gate; legacy regressions are caught
    // by the periodic full check.
    baseline.files.retain(|k, _| !k.starts_with("legacy/"));

    let det_filter = DeterministicFilter::from_baseline(&baseline);
    let check_filter = CheckFilter {
        filter: &det_filter,
        baseline: &baseline,
    };
    let current = sweep_modern_only(progs_dir, config, &check_filter);
    let d = diff(&baseline, &current);

    println!("=== Baseline diff (modern only) ===");
    println!("  unchanged: {}", d.unchanged);
    println!("  regressions: {}", d.regressions.len());
    println!("  new entries: {}", d.new_entries.len());
    println!("  removed entries: {}", d.removed_entries.len());

    for r in &d.regressions {
        let was = r.baseline.as_ref().map(|b| b.ours.as_str()).unwrap_or("?");
        let now = r.current.as_ref().map(|c| c.ours.as_str()).unwrap_or("?");
        println!("  REGRESSION  {}::{}  {was} -> {now}", r.file, r.prog);
    }
    for n in &d.new_entries {
        if let Some(c) = &n.current {
            println!("  NEW         {}::{}  ours={}", n.file, n.prog, c.ours);
        }
    }

    if !d.regressions.is_empty() {
        std::process::exit(1);
    }
}

fn run_baseline_write(progs_dir: &str, legacy_json_dir: &str, out: &str, config: &VerifierConfig) {
    use crate::testing::selftest::runner::RunAll;
    let bl = sweep_modern_and_legacy(progs_dir, legacy_json_dir, config, &RunAll);
    if let Err(e) = bl.write(out) {
        eprintln!("Error writing {out}: {e:?}");
        return;
    }
    println!("Wrote baseline ({} files) to {out}", bl.files.len());
}

fn run_baseline_check(
    progs_dir: &str,
    legacy_json_dir: &str,
    stored: &str,
    config: &VerifierConfig,
) {
    use crate::testing::selftest::baseline::{Baseline, CheckFilter, DeterministicFilter, diff};

    let baseline = match Baseline::read(stored) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("Error reading baseline {stored}: {e:?}");
            std::process::exit(2);
        }
    };
    // Fast path: only re-run programs whose baseline outcome is
    // deterministic (PASS / FALSE_REJECT / FALSE_ACCEPT) plus any
    // programs that aren't in the baseline at all (newly added). This
    // shrinks the gate from ~18 min to <1 min for a typical sweep.
    // Use `selftest-baseline-write` to refresh the baseline exhaustively.
    let det_filter = DeterministicFilter::from_baseline(&baseline);
    let check_filter = CheckFilter {
        filter: &det_filter,
        baseline: &baseline,
    };
    let current = sweep_modern_and_legacy(progs_dir, legacy_json_dir, config, &check_filter);
    let d = diff(&baseline, &current);

    println!("=== Baseline diff ===");
    println!("  unchanged: {}", d.unchanged);
    println!("  regressions: {}", d.regressions.len());
    println!("  new entries: {}", d.new_entries.len());
    println!("  removed entries: {}", d.removed_entries.len());

    for r in &d.regressions {
        let was = r.baseline.as_ref().map(|b| b.ours.as_str()).unwrap_or("?");
        let now = r.current.as_ref().map(|c| c.ours.as_str()).unwrap_or("?");
        println!("  REGRESSION  {}::{}  {was} -> {now}", r.file, r.prog);
    }
    for n in &d.new_entries {
        if let Some(c) = &n.current {
            println!("  NEW         {}::{}  ours={}", n.file, n.prog, c.ours);
        }
    }
    for n in &d.removed_entries {
        println!("  REMOVED     {}::{}", n.file, n.prog);
    }

    if !d.regressions.is_empty() {
        std::process::exit(1);
    }
}

fn print_modern_report(report: &crate::testing::selftest::runner::FileReport) {
    use crate::testing::selftest::runner::Outcome;
    println!("\n--- {} ---", report.source.display());
    for p in &report.progs {
        let tag = match &p.outcome {
            Outcome::Pass => "PASS".to_string(),
            Outcome::FalseReject(e) => format!("FALSE-REJECT ({e})"),
            Outcome::FalseAccept => "FALSE-ACCEPT (soundness!)".into(),
            Outcome::Skipped(r) => format!("skip: {r}"),
            Outcome::Error(e) => format!("ERROR: {e}"),
        };
        println!("  [{tag}]  {} ({})", p.func_name, p.description);
    }
    println!("  ({} / {} pass)", report.pass_count(), report.total());
}
