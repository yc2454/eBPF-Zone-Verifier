use std::fs;
use std::path::Path;

use crate::analysis;
use crate::common::config::{DomainMode, VerifierConfig};
use crate::parsing::bpf_insn::RawBpfInsn;
use crate::parsing::bpf_to_ast::lower_raw_to_program;
use crate::pcc::{ProgramCertificate, generate_prototype_certificate_from_zone};
use crate::testing::selftest::{
    JsonTestCase, TestOutcome, build_exec_context, make_entry_state, run_test,
};
use serde::Deserialize;

fn slugify_test_name(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut last_was_sep = false;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
            last_was_sep = false;
        } else if !last_was_sep {
            out.push('_');
            last_was_sep = true;
        }
    }
    let out = out.trim_matches('_');
    if out.is_empty() {
        "unnamed_test".to_string()
    } else {
        out.to_string()
    }
}

fn default_generated_cert_path(json_path: &str, test_name: &str, program_hash: &str) -> String {
    let suite = Path::new(json_path)
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "pcc_suite".to_string());
    let test = slugify_test_name(test_name);
    format!(
        "pcc-tests/certs/generated/{}.{}.{}.cert.json",
        suite, test, program_hash
    )
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

    let should_generate_cert =
        matches!(result.outcome, TestOutcome::Pass) && config.domain_mode == DomainMode::Zone;
    if should_generate_cert {
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
        let cert = generate_prototype_certificate_from_zone(&program, &zone_dbms);
        let output_path = config.certificate_output.clone().unwrap_or_else(|| {
            default_generated_cert_path(json_path, test_name, &cert.program_hash)
        });
        if let Some(parent) = Path::new(&output_path).parent()
            && let Err(e) = fs::create_dir_all(parent)
        {
            eprintln!(
                "Warning: failed to create certificate directory '{}': {}",
                parent.display(),
                e
            );
            return;
        }
        match cert.save_to_path(&output_path) {
            Ok(()) => {
                if config.certificate_output.is_some() {
                    println!("Certificate written: {}", output_path);
                } else {
                    println!("Certificate auto-written: {}", output_path);
                }
            }
            Err(e) => eprintln!(
                "Warning: failed to write certificate '{}': {e:#}",
                output_path
            ),
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

#[derive(Debug, Deserialize)]
struct PccCertCase {
    name: String,
    json_file: String,
    test_name: String,
    certificate: String,
    expected: String,
}

/// Run manifest-defined certificate cases with kernel-mode semantics.
pub fn pcc_cert_run(manifest_path: &str, config: &VerifierConfig) {
    println!("Running PCC certificate cases: {}\n", manifest_path);
    let content = match fs::read_to_string(manifest_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: Failed to read {}: {}", manifest_path, e);
            return;
        }
    };
    let cases: Vec<PccCertCase> = match serde_json::from_str(&content) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error: Failed to parse {}: {}", manifest_path, e);
            return;
        }
    };

    let mut passed = 0usize;
    let mut failed = 0usize;
    for case in &cases {
        let test_content = match fs::read_to_string(&case.json_file) {
            Ok(c) => c,
            Err(e) => {
                println!("[FAIL] {}: read test file: {}", case.name, e);
                failed += 1;
                continue;
            }
        };
        let tests: Vec<JsonTestCase> = match serde_json::from_str(&test_content) {
            Ok(t) => t,
            Err(e) => {
                println!("[FAIL] {}: parse test file: {}", case.name, e);
                failed += 1;
                continue;
            }
        };
        let Some(test) = tests.iter().find(|t| t.name == case.test_name) else {
            println!("[FAIL] {}: test '{}' not found", case.name, case.test_name);
            failed += 1;
            continue;
        };
        let cert = match ProgramCertificate::load_from_path(&case.certificate) {
            Ok(c) => c,
            Err(e) => {
                println!("[FAIL] {}: load cert failed: {e:#}", case.name);
                failed += 1;
                continue;
            }
        };

        let mut cfg = config.clone();
        cfg.domain_mode = DomainMode::Interval;
        cfg.detect_bounded_loops = false;
        cfg.require_single_loop_entry = true;
        cfg.certificate = Some(cert);

        let result = run_test(test, &cfg);
        if result.actual == case.expected {
            println!("[PASS] {} => {}", case.name, result.actual);
            passed += 1;
        } else {
            println!(
                "[FAIL] {} => expected {}, got {}",
                case.name, case.expected, result.actual
            );
            failed += 1;
        }
    }

    println!(
        "\nPCC certificate case summary: {}/{} passed, {} failed",
        passed,
        passed + failed,
        failed
    );
}
