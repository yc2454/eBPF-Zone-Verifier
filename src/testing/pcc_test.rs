use std::fs;
use std::path::Path;

use crate::analysis;
use crate::common::config::VerifierConfig;
use crate::parsing::bpf_insn::RawBpfInsn;
use crate::parsing::bpf_to_ast::lower_raw_to_program;
use crate::pcc::{ProgramCertificate, generate_v1_obligations_from_zone, program_hash};
use crate::testing::selftest::{
    JsonTestCase, TestOutcome, build_exec_context, make_entry_state, run_test, run_test_file,
    run_test_suite, write_json_report, write_txt_report,
};

/// Run all PCC tests in a single JSON file.
pub fn pcc_test_run(json_path: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("Running PCC test file: {}\n", json_path);

    match run_test_file(json_path, config) {
        Ok(result) => {
            println!(
                "Results: {}/{} passed ({} soundness, {} precision, {} skipped, {} errors) in {}ms",
                result.passed,
                result.total,
                result.false_negatives,
                result.false_positives,
                result.skipped,
                result.errors,
                result.time_ms
            );

            if let Some(dir) = output_dir {
                let base = Path::new(json_path).file_stem().unwrap().to_string_lossy();
                let suite = crate::testing::selftest::SuiteResult {
                    total_files: 1,
                    total_tests: result.total,
                    passed: result.passed,
                    false_positives: result.false_positives,
                    false_negatives: result.false_negatives,
                    skipped: result.skipped,
                    errors: result.errors,
                    time_ms: result.time_ms,
                    files: vec![result],
                };
                let txt_path = format!("{}/{}_report.txt", dir, base);
                let json_path = format!("{}/{}_report.json", dir, base);
                if let Err(e) = write_txt_report(&suite, &txt_path) {
                    eprintln!("Warning: {}", e);
                }
                if let Err(e) = write_json_report(&suite, &json_path) {
                    eprintln!("Warning: {}", e);
                }
            }
        }
        Err(e) => eprintln!("Error: {}", e),
    }
}

/// Run a single PCC test by exact name from a JSON file.
/// Certificate generation is supported only here to keep workflow deterministic.
pub fn pcc_test_single(json_path: &str, test_name: &str, config: &VerifierConfig) {
    println!(
        "Running single PCC test: '{}' from {}\n",
        test_name, json_path
    );

    let content = match fs::read_to_string(json_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: Failed to read {}: {}", json_path, e);
            return;
        }
    };
    let tests: Vec<JsonTestCase> = match serde_json::from_str(&content) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Error: Failed to parse {}: {}", json_path, e);
            return;
        }
    };

    let matching: Vec<_> = tests.iter().filter(|t| t.name == test_name).collect();
    if matching.is_empty() {
        eprintln!("Error: No test matching '{}' found", test_name);
        return;
    }
    if matching.len() > 1 {
        eprintln!("Error: Duplicate test name '{}'", test_name);
        return;
    }

    let test = matching[0];
    println!("Test: {}", test.name);
    println!("Expected: {}", test.result);
    println!("Instructions: {}", test.insns.len());
    println!();

    let result = run_test(test, config);

    if let Some(path) = &config.certificate_output
        && matches!(result.outcome, TestOutcome::Pass)
    {
        let raw_insns: Vec<RawBpfInsn> = test.insns.iter().map(|j| j.into()).collect();
        let program = match lower_raw_to_program(&raw_insns) {
            Ok(p) => p,
            Err(e) => {
                eprintln!(
                    "Warning: cannot generate certificate, lowering failed: {:?}",
                    e
                );
                return;
            }
        };
        let mut cert = ProgramCertificate::empty(program_hash(&program));
        let (ctx, has_unsupported_fixup) = build_exec_context(test);
        if has_unsupported_fixup {
            eprintln!("Warning: certificate generation skipped due to unsupported fixup type");
            return;
        }
        let entry = make_entry_state();
        let zone_dbms = match analysis::analyze_program(&ctx, &program, entry, config) {
            Ok(v) => v,
            Err(e) => {
                eprintln!(
                    "Warning: certificate generation failed during zone analysis: {}",
                    e.description()
                );
                return;
            }
        };
        cert.obligations = generate_v1_obligations_from_zone(&program, &zone_dbms);
        match cert.save_to_path(path) {
            Ok(()) => println!("Certificate written: {}", path),
            Err(e) => eprintln!("Warning: failed to write certificate '{}': {e:#}", path),
        }
    }

    match &result.outcome {
        TestOutcome::Pass => println!("=== PASS === ({}ms)", result.time_ms),
        TestOutcome::FalseNegative => {
            println!("=== !!! SOUNDNESS ISSUE !!! === ({}ms)", result.time_ms)
        }
        TestOutcome::FalsePositive => println!("=== PRECISION ISSUE === ({}ms)", result.time_ms),
        TestOutcome::Skipped { reason } => {
            println!("=== SKIPPED === ({}ms) {}", result.time_ms, reason)
        }
        TestOutcome::Error { message } => {
            println!("=== ERROR === ({}ms) {}", result.time_ms, message)
        }
    }
}

/// List tests in a PCC JSON file.
pub fn pcc_test_list(json_path: &str) {
    println!("PCC tests in {}:\n", json_path);
    let content = match fs::read_to_string(json_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: Failed to read {}: {}", json_path, e);
            return;
        }
    };
    let tests: Vec<JsonTestCase> = match serde_json::from_str(&content) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Error: Failed to parse {}: {}", json_path, e);
            return;
        }
    };
    for (i, t) in tests.iter().enumerate() {
        println!("  [{:2}] {} -> {}", i, t.name, t.result);
    }
}

/// Run all PCC JSON files in a directory.
pub fn pcc_test_suite(dir: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("Running PCC test suite: {}\n", dir);
    match run_test_suite(dir, config) {
        Ok(result) => {
            println!(
                "Suite: {}/{} passed ({} soundness, {} precision, {} skipped, {} errors)",
                result.passed,
                result.total_tests,
                result.false_negatives,
                result.false_positives,
                result.skipped,
                result.errors
            );
            if let Some(out) = output_dir {
                let txt_path = format!("{}/pcc_test_report.txt", out);
                let json_path = format!("{}/pcc_test_report.json", out);
                if let Err(e) = write_txt_report(&result, &txt_path) {
                    eprintln!("Warning: {}", e);
                }
                if let Err(e) = write_json_report(&result, &json_path) {
                    eprintln!("Warning: {}", e);
                }
            }
        }
        Err(e) => eprintln!("Error: {}", e),
    }
}
