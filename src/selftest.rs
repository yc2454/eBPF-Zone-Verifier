// src/selftest.rs
//
// Runner for kernel BPF verifier selftests converted to JSON format.
//
// Usage:
//   cargo run -- selftest-run tests/array_access.json
//   cargo run -- selftest-suite tests/

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::time::Instant;

use serde::{Deserialize, Serialize};

use crate::analysis;
use crate::analysis::context::{default_exec_ctx};
use crate::ast::ProgramKind;
use crate::parsing::bpf_to_ast::lower_raw_to_program;
use crate::parsing::elf_loader::{RelocInfo};
use crate::misc::config::VerifierConfig;
use crate::parsing::bpf_insn::RawBpfInsn;
use crate::parsing::elf_loader::BpfMapDef;
use crate::analysis::constants::{
    BPF_MAP_TYPE_HASH, BPF_MAP_TYPE_ARRAY, BPF_MAP_TYPE_PROG_ARRAY,
    BPF_PROG_TYPE_SCHED_CLS, BPF_PROG_TYPE_XDP
};
use crate::zone::dbm::Dbm;
use crate::zone::domain::{Reg, REG_ENV, assign_zero};

// ============================================================================
// JSON Deserialization Types
// ============================================================================

#[derive(Debug, Deserialize)]
pub struct JsonTestCase {
    pub name: String,
    pub result: String,
    pub result_unpriv: Option<String>,
    pub errstr: Option<String>,
    pub errstr_unpriv: Option<String>,
    pub prog_type: Option<u32>,
    pub flags: Option<u32>,
    pub fixups: Option<HashMap<String, Vec<usize>>>,
    pub insns: Vec<JsonInsn>,
}

#[derive(Debug, Deserialize)]
pub struct JsonInsn {
    pub code: u8,
    pub dst: u8,
    pub src: u8,
    pub off: i16,
    pub imm: i32,
}

impl From<&JsonInsn> for RawBpfInsn {
    fn from(j: &JsonInsn) -> Self {
        RawBpfInsn {
            code: j.code,
            dst: j.dst,
            src: j.src,
            off: j.off,
            imm: j.imm,
        }
    }
}

// ============================================================================
// Test Results
// ============================================================================

#[derive(Debug, Clone, Serialize)]
pub enum TestOutcome {
    /// Our result matches expected
    Pass,
    /// We got a different result than expected
    Mismatch {
        expected: String,
        actual: String,
    },
    /// Test couldn't be run (parse error, unsupported feature, etc.)
    Skipped {
        reason: String,
    },
    /// Internal error during analysis
    Error {
        message: String,
    },
}

impl TestOutcome {
    pub fn is_pass(&self) -> bool {
        matches!(self, TestOutcome::Pass)
    }

    pub fn is_mismatch(&self) -> bool {
        matches!(self, TestOutcome::Mismatch { .. })
    }
}

#[derive(Debug, Serialize)]
pub struct TestResult {
    pub name: String,
    pub outcome: TestOutcome,
    pub expected: String,
    pub actual: String,
    pub time_ms: u64,
}

#[derive(Debug, Serialize)]
pub struct FileResult {
    pub file: String,
    pub total: usize,
    pub passed: usize,
    pub mismatched: usize,
    pub skipped: usize,
    pub errors: usize,
    pub time_ms: u64,
    pub tests: Vec<TestResult>,
}

#[derive(Debug, Serialize)]
pub struct SuiteResult {
    pub total_files: usize,
    pub total_tests: usize,
    pub passed: usize,
    pub mismatched: usize,
    pub skipped: usize,
    pub errors: usize,
    pub time_ms: u64,
    pub files: Vec<FileResult>,
}

// ============================================================================
// Fixup → Map Definition
// ============================================================================

/// Convert fixup field names to BpfMapDef
fn map_def_for_fixup(fixup_name: &str) -> Option<BpfMapDef> {
    // Parse fixup name to determine map type and size
    // Format: fixup_map_{type}_{size} or fixup_map_{type}
    match fixup_name {
        "fixup_map_hash_8b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_HASH,
            key_size: 8,
            value_size: 8,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_hash_16b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_HASH,
            key_size: 8,
            value_size: 16,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_hash_48b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_HASH,
            key_size: 8,
            value_size: 48,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_48b" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 48,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_ro" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 8,
            max_entries: 1,
            map_flags: 0x80, // BPF_F_RDONLY_PROG
            name: "test_map_ro".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_wo" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 8,
            max_entries: 1,
            map_flags: 0x100, // BPF_F_WRONLY_PROG
            name: "test_map_wo".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_map_array_small" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_ARRAY,
            key_size: 4,
            value_size: 1,
            max_entries: 1,
            map_flags: 0,
            name: "test_map".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        "fixup_prog1" | "fixup_prog2" => Some(BpfMapDef {
            type_: BPF_MAP_TYPE_PROG_ARRAY,
            key_size: 4,
            value_size: 4,
            max_entries: 1,
            map_flags: 0,
            name: "test_prog_array".to_string(),
            btf_val_type_id: None,
            initial_data: None,
        }),
        // Add more fixup types as needed
        _ => None,
    }
}

// ============================================================================
// Build ExecContext from Test Case
// ============================================================================

fn build_exec_context(test: &JsonTestCase) -> (crate::analysis::context::ExecContext, bool) {
    let mut ctx = default_exec_ctx();
    let mut has_unsupported_fixup = false;

    if let Some(ref fixups) = test.fixups {
        for (fixup_name, pcs) in fixups {
            if let Some(map_def) = map_def_for_fixup(fixup_name) {
                let map_idx = ctx.map_defs.len();
                ctx.map_defs.push(map_def);

                // Record relocations for each PC
                for &pc in pcs {
                    ctx.pc_to_reloc.insert(
                        pc,
                        RelocInfo {
                            map_idx,
                            offset: 0,
                        },
                    );
                }
            } else {
                // Unsupported fixup type
                has_unsupported_fixup = true;
            }
        }
    }

    ctx.prog_kind = match test.prog_type {
        Some(BPF_PROG_TYPE_SCHED_CLS) => ProgramKind::SchedCls, // BPF_PROG_TYPE_SCHED_CLS
        Some(BPF_PROG_TYPE_XDP) => ProgramKind::Xdp,      // BPF_PROG_TYPE_XDP
        _ => ProgramKind::SocketFilter,   // Default
    };

    (ctx, has_unsupported_fixup)
}

// ============================================================================
// Entry State
// ============================================================================

fn make_entry_state() -> Dbm {
    let mut dbm = Dbm::new(REG_ENV.len());
    assign_zero(&mut dbm, Reg::R10);
    dbm
}

// ============================================================================
// Run Single Test
// ============================================================================

pub fn run_test(test: &JsonTestCase, config: &VerifierConfig) -> TestResult {
    let start = Instant::now();

    // Convert JSON instructions to RawBpfInsn
    let raw_insns: Vec<RawBpfInsn> = test.insns.iter().map(|j| j.into()).collect();

    // Lower to Program AST
    let program = match lower_raw_to_program(&raw_insns) {
        Ok(p) => p,
        Err(e) => {
            return TestResult {
                name: test.name.clone(),
                outcome: TestOutcome::Error {
                    message: format!("Failed to lower program: {:?}", e),
                },
                expected: test.result.clone(),
                actual: "ERROR".to_string(),
                time_ms: start.elapsed().as_millis() as u64,
            };
        }
    };

    // Build execution context
    let (ctx, has_unsupported_fixup) = build_exec_context(test);

    if has_unsupported_fixup {
        return TestResult {
            name: test.name.clone(),
            outcome: TestOutcome::Skipped {
                reason: "Unsupported fixup type".to_string(),
            },
            expected: test.result.clone(),
            actual: "SKIPPED".to_string(),
            time_ms: start.elapsed().as_millis() as u64,
        };
    }

    // Run analysis
    let entry = make_entry_state();
    let result = analysis::analyze_program(&ctx, &program, entry, config);

    let actual = if result.is_ok() { "ACCEPT" } else { "REJECT" };
    let expected = &test.result;

    let outcome = if actual == expected {
        TestOutcome::Pass
    } else {
        TestOutcome::Mismatch {
            expected: expected.clone(),
            actual: actual.to_string(),
        }
    };

    TestResult {
        name: test.name.clone(),
        outcome,
        expected: expected.clone(),
        actual: actual.to_string(),
        time_ms: start.elapsed().as_millis() as u64,
    }
}

// ============================================================================
// Run Test File
// ============================================================================

pub fn run_test_file(path: &str, config: &VerifierConfig) -> Result<FileResult, String> {
    let start = Instant::now();

    // Load JSON
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read {}: {}", path, e))?;

    let tests: Vec<JsonTestCase> = serde_json::from_str(&content)
        .map_err(|e| format!("Failed to parse {}: {}", path, e))?;

    let mut results = Vec::new();
    let mut passed = 0;
    let mut mismatched = 0;
    let mut skipped = 0;
    let mut errors = 0;

    for test in &tests {
        let result = run_test(test, config);

        match &result.outcome {
            TestOutcome::Pass => passed += 1,
            TestOutcome::Mismatch { .. } => mismatched += 1,
            TestOutcome::Skipped { .. } => skipped += 1,
            TestOutcome::Error { .. } => errors += 1,
        }

        results.push(result);
    }

    Ok(FileResult {
        file: path.to_string(),
        total: tests.len(),
        passed,
        mismatched,
        skipped,
        errors,
        time_ms: start.elapsed().as_millis() as u64,
        tests: results,
    })
}

// ============================================================================
// Run Test Suite (Directory)
// ============================================================================

pub fn run_test_suite(dir: &str, config: &VerifierConfig) -> Result<SuiteResult, String> {
    let start = Instant::now();

    let mut files = Vec::new();

    // Find all .json files
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("Failed to read directory {}: {}", dir, e))?;

    let mut json_files: Vec<_> = entries
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .extension()
                .map(|ext| ext == "json")
                .unwrap_or(false)
        })
        .collect();

    json_files.sort_by_key(|e| e.path());

    for entry in json_files {
        let path = entry.path();
        let path_str = path.to_string_lossy().to_string();

        match run_test_file(&path_str, config) {
            Ok(result) => files.push(result),
            Err(e) => {
                eprintln!("Warning: Skipping {}: {}", path_str, e);
            }
        }
    }

    // Aggregate stats
    let total_tests: usize = files.iter().map(|f| f.total).sum();
    let passed: usize = files.iter().map(|f| f.passed).sum();
    let mismatched: usize = files.iter().map(|f| f.mismatched).sum();
    let skipped: usize = files.iter().map(|f| f.skipped).sum();
    let errors: usize = files.iter().map(|f| f.errors).sum();

    Ok(SuiteResult {
        total_files: files.len(),
        total_tests,
        passed,
        mismatched,
        skipped,
        errors,
        time_ms: start.elapsed().as_millis() as u64,
        files,
    })
}

// ============================================================================
// Report Generation
// ============================================================================

pub fn write_txt_report(result: &SuiteResult, path: &str) -> Result<(), String> {
    let mut f = fs::File::create(path)
        .map_err(|e| format!("Failed to create {}: {}", path, e))?;

    writeln!(f, "BPF Verifier Selftest Report").unwrap();
    writeln!(f, "============================\n").unwrap();

    writeln!(f, "Summary:").unwrap();
    writeln!(f, "  Files:      {}", result.total_files).unwrap();
    writeln!(f, "  Tests:      {}", result.total_tests).unwrap();
    writeln!(f, "  Passed:     {} ({:.1}%)", 
             result.passed, 
             100.0 * result.passed as f64 / result.total_tests.max(1) as f64).unwrap();
    writeln!(f, "  Mismatched: {}", result.mismatched).unwrap();
    writeln!(f, "  Skipped:    {}", result.skipped).unwrap();
    writeln!(f, "  Errors:     {}", result.errors).unwrap();
    writeln!(f, "  Time:       {} ms\n", result.time_ms).unwrap();

    // Per-file summary
    writeln!(f, "Per-File Results:").unwrap();
    writeln!(f, "-----------------").unwrap();
    for file in &result.files {
        let status = if file.mismatched == 0 && file.errors == 0 {
            "OK"
        } else {
            "ISSUES"
        };
        writeln!(f, "  {} - {} ({}/{} passed) [{}ms]",
                 status,
                 Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                 file.passed,
                 file.total,
                 file.time_ms).unwrap();
    }

    // Mismatches detail
    let has_mismatches = result.files.iter().any(|f| f.mismatched > 0);
    if has_mismatches {
        writeln!(f, "\nMismatches:").unwrap();
        writeln!(f, "-----------").unwrap();
        for file in &result.files {
            for test in &file.tests {
                if let TestOutcome::Mismatch { expected, actual } = &test.outcome {
                    writeln!(f, "  [{}] {}", 
                             Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                             test.name).unwrap();
                    writeln!(f, "    Expected: {}, Got: {}", expected, actual).unwrap();
                }
            }
        }
    }

    // Errors detail
    let has_errors = result.files.iter().any(|f| f.errors > 0);
    if has_errors {
        writeln!(f, "\nErrors:").unwrap();
        writeln!(f, "-------").unwrap();
        for file in &result.files {
            for test in &file.tests {
                if let TestOutcome::Error { message } = &test.outcome {
                    writeln!(f, "  [{}] {}", 
                             Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                             test.name).unwrap();
                    writeln!(f, "    {}", message).unwrap();
                }
            }
        }
    }

    Ok(())
}

pub fn write_json_report(result: &SuiteResult, path: &str) -> Result<(), String> {
    let json = serde_json::to_string_pretty(result)
        .map_err(|e| format!("Failed to serialize: {}", e))?;

    fs::write(path, json)
        .map_err(|e| format!("Failed to write {}: {}", path, e))?;

    Ok(())
}

// ============================================================================
// CLI Entry Points
// ============================================================================

/// Run a single test file and print results
pub fn selftest_run(json_path: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("Running selftest: {}\n", json_path);

    match run_test_file(json_path, config) {
        Ok(result) => {
            // Print summary
            println!("Results: {}/{} passed ({} skipped, {} errors) in {}ms",
                     result.passed, result.total, result.skipped, result.errors, result.time_ms);

            // Print failures
            for test in &result.tests {
                match &test.outcome {
                    TestOutcome::Pass => {
                        if config.verbosity > 0 {
                            println!("  PASS: {}", test.name);
                        }
                    }
                    TestOutcome::Mismatch { expected, actual } => {
                        println!("  MISMATCH: {} (expected {}, got {})", test.name, expected, actual);
                    }
                    TestOutcome::Skipped { reason } => {
                        if config.verbosity > 0 {
                            println!("  SKIP: {} ({})", test.name, reason);
                        }
                    }
                    TestOutcome::Error { message } => {
                        println!("  ERROR: {} ({})", test.name, message);
                    }
                }
            }

            // Write reports if output_dir specified
            if let Some(dir) = output_dir {
                let base = Path::new(json_path)
                    .file_stem()
                    .unwrap()
                    .to_string_lossy();

                let suite = SuiteResult {
                    total_files: 1,
                    total_tests: result.total,
                    passed: result.passed,
                    mismatched: result.mismatched,
                    skipped: result.skipped,
                    errors: result.errors,
                    time_ms: result.time_ms,
                    files: vec![result],
                };

                let txt_path = format!("{}/{}_report.txt", dir, base);
                let json_path = format!("{}/{}_report.json", dir, base);

                if let Err(e) = write_txt_report(&suite, &txt_path) {
                    eprintln!("Warning: {}", e);
                } else {
                    println!("\nReport written to: {}", txt_path);
                }

                if let Err(e) = write_json_report(&suite, &json_path) {
                    eprintln!("Warning: {}", e);
                }
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}

/// Run all test files in a directory
pub fn selftest_suite(dir: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("Running selftest suite: {}\n", dir);

    match run_test_suite(dir, config) {
        Ok(result) => {
            // Print summary
            println!("========================================");
            println!("            SUITE SUMMARY");
            println!("========================================");
            println!("Files:      {}", result.total_files);
            println!("Tests:      {}", result.total_tests);
            println!("Passed:     {} ({:.1}%)",
                     result.passed,
                     100.0 * result.passed as f64 / result.total_tests.max(1) as f64);
            println!("Mismatched: {}", result.mismatched);
            println!("Skipped:    {}", result.skipped);
            println!("Errors:     {}", result.errors);
            println!("Time:       {} ms", result.time_ms);
            println!("========================================\n");

            // Per-file summary
            println!("Per-file results:");
            for file in &result.files {
                let status = if file.mismatched == 0 && file.errors == 0 {
                    "✓"
                } else {
                    "✗"
                };
                println!("  {} {} ({}/{} passed)",
                         status,
                         Path::new(&file.file).file_name().unwrap().to_string_lossy(),
                         file.passed,
                         file.total);
            }

            // Write reports
            let out = output_dir.unwrap_or(".");
            let txt_path = format!("{}/selftest_report.txt", out);
            let json_path = format!("{}/selftest_report.json", out);

            if let Err(e) = write_txt_report(&result, &txt_path) {
                eprintln!("Warning: {}", e);
            } else {
                println!("\nText report:  {}", txt_path);
            }

            if let Err(e) = write_json_report(&result, &json_path) {
                eprintln!("Warning: {}", e);
            } else {
                println!("JSON report:  {}", json_path);
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}
