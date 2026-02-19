//! PREVAIL Benchmark Tests
//!
//! Test runner for ELF files from the PREVAIL verifier benchmark suite.
//! These tests are derived from ~/ebpf-samples/build/ and validate that our
//! verifier correctly accepts safe programs and rejects unsafe ones.
//!
//! Usage:
//!   cargo run -- prevail-list <catalogue.json>
//!   cargo run -- prevail-run <catalogue.json>
//!   cargo run -- prevail-single <catalogue.json> <test_name>

use serde::{Deserialize, Serialize};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::common::config::VerifierConfig;
use crate::testing::runner::{AnalysisResult, Analyzer};

// ============================================================================
// JSON Catalogue Types
// ============================================================================

/// Test entry from the catalogue
#[derive(Debug, Deserialize, Clone)]
pub struct TestEntry {
    pub name: String,
    pub file: String,
    pub section: Option<String>,
    pub expected: String,
    pub reason: String,
}

/// The full test catalogue
#[derive(Debug, Deserialize)]
pub struct TestCatalogue {
    pub description: String,
    pub base_path: String,
    pub tests: Vec<TestEntry>,
}

// ============================================================================
// Test Results
// ============================================================================

#[derive(Debug, Clone, Serialize)]
pub enum TestOutcome {
    /// Our result matches expected
    Pass,
    /// Expected ACCEPT but we REJECT - precision issue (too conservative)
    FalsePositive,
    /// Expected REJECT but we ACCEPT - SOUNDNESS issue (too permissive - BAD!)
    FalseNegative,
    /// Test couldn't be run (file not found, parse error, etc.)
    Error { message: String },
    /// Analysis timed out
    Timeout,
}

#[derive(Debug, Serialize)]
pub struct TestResult {
    pub name: String,
    pub outcome: TestOutcome,
    pub expected: String,
    pub actual: String,
    pub time_ms: u64,
    pub error_detail: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct SuiteResult {
    pub total: usize,
    pub passed: usize,
    pub false_positives: usize,
    pub false_negatives: usize,
    pub errors: usize,
    pub timeouts: usize,
    pub time_ms: u64,
    pub tests: Vec<TestResult>,
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Expand ~ in paths
fn expand_path(path: &str) -> PathBuf {
    if path.starts_with("~/") {
        let home = std::env::var("HOME").expect("HOME not set");
        PathBuf::from(home).join(&path[2..])
    } else {
        PathBuf::from(path)
    }
}

/// Load the test catalogue from JSON
pub fn load_catalogue(path: &str) -> Result<TestCatalogue, String> {
    let content =
        fs::read_to_string(path).map_err(|e| format!("Failed to read catalogue: {}", e))?;

    serde_json::from_str(&content).map_err(|e| format!("Failed to parse catalogue: {}", e))
}

// ============================================================================
// Test Execution
// ============================================================================

/// Run a single test entry
pub fn run_test(entry: &TestEntry, base_path: &Path, config: &VerifierConfig) -> TestResult {
    let start = Instant::now();
    let elf_path = base_path.join(&entry.file);

    if !elf_path.exists() {
        return TestResult {
            name: entry.name.clone(),
            outcome: TestOutcome::Error {
                message: format!("ELF file not found: {:?}", elf_path),
            },
            expected: entry.expected.clone(),
            actual: "ERROR".to_string(),
            time_ms: start.elapsed().as_millis() as u64,
            error_detail: None,
        };
    }

    let analyzer = Analyzer::new(elf_path.to_str().unwrap(), config.clone());

    // Determine which section to analyze
    let result = if let Some(section) = &entry.section {
        analyzer.analyze_section(section)
    } else {
        // Analyze all sections, consider pass if all pass
        let (all_pass, results) = analyzer.analyze_all();
        if results.is_empty() {
            // No named code sections found, try .text as fallback
            // (many PREVAIL tests use .text for their code)
            analyzer.analyze_section(".text")
        } else if all_pass {
            AnalysisResult::Pass
        } else {
            // Return the first failure
            results
                .into_iter()
                .find(|(_, r)| !r.is_pass())
                .map(|(_, r)| r)
                .unwrap_or(AnalysisResult::Pass)
        }
    };

    let (actual, error_detail) = match &result {
        AnalysisResult::Pass => ("ACCEPT".to_string(), None),
        AnalysisResult::Fail(e) => ("REJECT".to_string(), Some(e.description().to_string())),
        AnalysisResult::Timeout => ("TIMEOUT".to_string(), None),
        AnalysisResult::LoadError(e) => ("ERROR".to_string(), Some(e.clone())),
    };

    let expected_accept = entry.expected == "ACCEPT";
    let actual_accept = actual == "ACCEPT";

    let outcome = match &result {
        AnalysisResult::Timeout => TestOutcome::Timeout,
        AnalysisResult::LoadError(msg) => TestOutcome::Error {
            message: msg.clone(),
        },
        _ => {
            if (expected_accept && actual_accept) || (!expected_accept && !actual_accept) {
                TestOutcome::Pass
            } else if expected_accept && !actual_accept {
                TestOutcome::FalsePositive
            } else {
                TestOutcome::FalseNegative
            }
        }
    };

    TestResult {
        name: entry.name.clone(),
        outcome,
        expected: entry.expected.clone(),
        actual,
        time_ms: start.elapsed().as_millis() as u64,
        error_detail,
    }
}

/// Run all tests in a catalogue
pub fn run_catalogue(catalogue: &TestCatalogue, config: &VerifierConfig) -> SuiteResult {
    let start = Instant::now();
    let base_path = expand_path(&catalogue.base_path);

    let mut results = Vec::new();
    let mut passed = 0;
    let mut false_positives = 0;
    let mut false_negatives = 0;
    let mut errors = 0;
    let mut timeouts = 0;

    for entry in &catalogue.tests {
        let result = run_test(entry, &base_path, config);

        match &result.outcome {
            TestOutcome::Pass => passed += 1,
            TestOutcome::FalsePositive => false_positives += 1,
            TestOutcome::FalseNegative => false_negatives += 1,
            TestOutcome::Error { .. } => errors += 1,
            TestOutcome::Timeout => timeouts += 1,
        }

        results.push(result);
    }

    SuiteResult {
        total: catalogue.tests.len(),
        passed,
        false_positives,
        false_negatives,
        errors,
        timeouts,
        time_ms: start.elapsed().as_millis() as u64,
        tests: results,
    }
}

// ============================================================================
// Report Generation
// ============================================================================

pub fn write_txt_report(result: &SuiteResult, path: &str) -> Result<(), String> {
    let mut f = fs::File::create(path).map_err(|e| format!("Failed to create {}: {}", path, e))?;

    writeln!(f, "PREVAIL Benchmark Test Report").unwrap();
    writeln!(f, "==============================\n").unwrap();

    writeln!(f, "Summary:").unwrap();
    writeln!(f, "  Total:            {}", result.total).unwrap();
    writeln!(
        f,
        "  Passed:           {} ({:.1}%)",
        result.passed,
        100.0 * result.passed as f64 / result.total.max(1) as f64
    )
    .unwrap();
    writeln!(
        f,
        "  SOUNDNESS ISSUES: {} (expected REJECT, got ACCEPT) <<<",
        result.false_negatives
    )
    .unwrap();
    writeln!(
        f,
        "  Precision issues: {} (expected ACCEPT, got REJECT)",
        result.false_positives
    )
    .unwrap();
    writeln!(f, "  Errors:           {}", result.errors).unwrap();
    writeln!(f, "  Timeouts:         {}", result.timeouts).unwrap();
    writeln!(f, "  Time:             {} ms\n", result.time_ms).unwrap();

    // SOUNDNESS ISSUES first
    let soundness: Vec<_> = result
        .tests
        .iter()
        .filter(|t| matches!(t.outcome, TestOutcome::FalseNegative))
        .collect();
    if !soundness.is_empty() {
        writeln!(f, "!!! SOUNDNESS ISSUES !!!").unwrap();
        writeln!(f, "========================").unwrap();
        for t in &soundness {
            writeln!(f, "  {} (expected REJECT, got ACCEPT)", t.name).unwrap();
        }
        writeln!(f).unwrap();
    }

    // Precision issues
    let precision: Vec<_> = result
        .tests
        .iter()
        .filter(|t| matches!(t.outcome, TestOutcome::FalsePositive))
        .collect();
    if !precision.is_empty() {
        writeln!(f, "Precision Issues:").unwrap();
        writeln!(f, "-----------------").unwrap();
        for t in &precision {
            writeln!(f, "  {} (expected ACCEPT, got REJECT)", t.name).unwrap();
            if let Some(ref detail) = t.error_detail {
                writeln!(f, "    Reason: {}", detail).unwrap();
            }
        }
        writeln!(f).unwrap();
    }

    // All results
    writeln!(f, "All Results:").unwrap();
    writeln!(f, "------------").unwrap();
    for t in &result.tests {
        let status = match &t.outcome {
            TestOutcome::Pass => "PASS",
            TestOutcome::FalsePositive => "PRECISION",
            TestOutcome::FalseNegative => "SOUNDNESS",
            TestOutcome::Error { .. } => "ERROR",
            TestOutcome::Timeout => "TIMEOUT",
        };
        writeln!(
            f,
            "  [{:9}] {} (expected {}, got {}) [{}ms]",
            status, t.name, t.expected, t.actual, t.time_ms
        )
        .unwrap();
    }

    Ok(())
}

pub fn write_json_report(result: &SuiteResult, path: &str) -> Result<(), String> {
    let json =
        serde_json::to_string_pretty(result).map_err(|e| format!("Failed to serialize: {}", e))?;

    fs::write(path, json).map_err(|e| format!("Failed to write {}: {}", path, e))?;

    Ok(())
}

// ============================================================================
// CLI Entry Points
// ============================================================================

/// List all tests in a catalogue
pub fn prevail_list(catalogue_path: &str) {
    println!("PREVAIL Tests in {}:\n", catalogue_path);

    match load_catalogue(catalogue_path) {
        Ok(catalogue) => {
            println!("Description: {}", catalogue.description);
            println!("Base path:   {}\n", catalogue.base_path);

            let accept_tests: Vec<_> =
                catalogue.tests.iter().filter(|t| t.expected == "ACCEPT").collect();
            let reject_tests: Vec<_> =
                catalogue.tests.iter().filter(|t| t.expected == "REJECT").collect();

            println!("Tests expecting ACCEPT ({}):", accept_tests.len());
            for t in &accept_tests {
                let section = t.section.as_deref().unwrap_or("(all)");
                println!("  {} [{}] - {}", t.name, section, t.reason);
            }

            println!("\nTests expecting REJECT ({}):", reject_tests.len());
            for t in &reject_tests {
                let section = t.section.as_deref().unwrap_or("(all)");
                println!("  {} [{}] - {}", t.name, section, t.reason);
            }

            println!("\nTotal: {} tests", catalogue.tests.len());
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}

/// Run all tests in a catalogue
pub fn prevail_run(catalogue_path: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("Running PREVAIL tests: {}\n", catalogue_path);

    match load_catalogue(catalogue_path) {
        Ok(catalogue) => {
            let result = run_catalogue(&catalogue, config);

            // Print summary
            println!("========================================");
            println!("       PREVAIL Test Results");
            println!("========================================");
            println!("Total:            {}", result.total);
            println!(
                "Passed:           {} ({:.1}%)",
                result.passed,
                100.0 * result.passed as f64 / result.total.max(1) as f64
            );
            if result.false_negatives > 0 {
                println!("SOUNDNESS ISSUES: {} <<<", result.false_negatives);
            } else {
                println!("Soundness issues: 0 (good!)");
            }
            println!("Precision issues: {}", result.false_positives);
            println!("Errors:           {}", result.errors);
            println!("Timeouts:         {}", result.timeouts);
            println!("Time:             {} ms", result.time_ms);
            println!("========================================\n");

            // Print soundness issues first
            for t in &result.tests {
                if matches!(t.outcome, TestOutcome::FalseNegative) {
                    println!(
                        "  !!! SOUNDNESS: {} (expected REJECT, got ACCEPT)",
                        t.name
                    );
                }
            }

            // Print precision issues
            for t in &result.tests {
                if matches!(t.outcome, TestOutcome::FalsePositive) {
                    println!("  PRECISION: {} (expected ACCEPT, got REJECT)", t.name);
                    if let Some(ref detail) = t.error_detail {
                        println!("    Reason: {}", detail);
                    }
                }
            }

            // Print individual results if verbose
            if config.verbosity > 0 {
                println!("\nIndividual results:");
                for t in &result.tests {
                    let status = match &t.outcome {
                        TestOutcome::Pass => "PASS",
                        TestOutcome::FalsePositive => "PRECISION",
                        TestOutcome::FalseNegative => "SOUNDNESS",
                        TestOutcome::Error { .. } => "ERROR",
                        TestOutcome::Timeout => "TIMEOUT",
                    };
                    println!(
                        "  [{:9}] {} (expected {}, got {})",
                        status, t.name, t.expected, t.actual
                    );
                }
            }

            // Write reports
            if let Some(dir) = output_dir {
                let _ = fs::create_dir_all(dir);
                let txt_path = format!("{}/prevail_report.txt", dir);
                let json_path = format!("{}/prevail_report.json", dir);

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
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}

/// Run a single test by name
pub fn prevail_single(catalogue_path: &str, test_name: &str, config: &VerifierConfig) {
    println!("Running PREVAIL test: '{}'\n", test_name);

    match load_catalogue(catalogue_path) {
        Ok(catalogue) => {
            let base_path = expand_path(&catalogue.base_path);

            // Find test by name
            let entry = catalogue
                .tests
                .iter()
                .find(|t| t.name == test_name);

            match entry {
                Some(entry) => {
                    println!("Test:     {}", entry.name);
                    println!("File:     {}", entry.file);
                    println!("Section:  {}", entry.section.as_deref().unwrap_or("(all)"));
                    println!("Expected: {}", entry.expected);
                    println!("Reason:   {}", entry.reason);
                    println!();

                    let result = run_test(entry, &base_path, config);

                    match &result.outcome {
                        TestOutcome::Pass => {
                            println!("=== PASS === ({}ms)", result.time_ms);
                        }
                        TestOutcome::FalseNegative => {
                            println!("=== !!! SOUNDNESS ISSUE !!! === ({}ms)", result.time_ms);
                            println!("  Expected: REJECT");
                            println!("  Actual:   ACCEPT");
                        }
                        TestOutcome::FalsePositive => {
                            println!("=== PRECISION ISSUE === ({}ms)", result.time_ms);
                            println!("  Expected: ACCEPT");
                            println!("  Actual:   REJECT");
                            if let Some(ref detail) = result.error_detail {
                                println!("  Reason:   {}", detail);
                            }
                        }
                        TestOutcome::Error { message } => {
                            println!("=== ERROR === ({}ms)", result.time_ms);
                            println!("  {}", message);
                        }
                        TestOutcome::Timeout => {
                            println!("=== TIMEOUT === ({}ms)", result.time_ms);
                        }
                    }
                }
                None => {
                    eprintln!("Error: Test '{}' not found", test_name);
                    eprintln!("\nAvailable tests:");
                    for t in &catalogue.tests {
                        eprintln!("  {}", t.name);
                    }
                }
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}
