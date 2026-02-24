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
//!   cargo run -- prevail-benchmark ~/ebpf-samples [--project <name>]

use chrono::Local;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::common::config::VerifierConfig;
use crate::testing::benchmark_common::{
    self, BenchmarkStats, FileResult, expand_path, extract_project, is_elf_file, visit_dirs,
};
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

            let accept_tests: Vec<_> = catalogue
                .tests
                .iter()
                .filter(|t| t.expected == "ACCEPT")
                .collect();
            let reject_tests: Vec<_> = catalogue
                .tests
                .iter()
                .filter(|t| t.expected == "REJECT")
                .collect();

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
                    println!("  !!! SOUNDNESS: {} (expected REJECT, got ACCEPT)", t.name);
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
            let entry = catalogue.tests.iter().find(|t| t.name == test_name);

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

// ============================================================================
// Prevail Benchmark (Full ebpf-samples scan)
// ============================================================================

/// Run benchmark on all ELF files in ~/ebpf-samples
///
/// - Files in `invalid/` directory are expected to be REJECTED
/// - All other files are expected to be ACCEPTED
pub fn prevail_benchmark(dir_path: &str, config: &VerifierConfig, output_dir: Option<&str>) {
    println!("=== PREVAIL Benchmark ===\n");

    let root_path = expand_path(dir_path);
    let start_time = Instant::now();

    println!("Root Directory: {}", root_path.display());
    if let Some(p) = &config.bench_project {
        println!("Filter [Project]: {}", p);
    }

    if !root_path.exists() || !root_path.is_dir() {
        eprintln!("Error: Directory does not exist: {:?}", root_path);
        return;
    }

    // Collect all files
    let mut files = Vec::new();
    if let Err(e) = visit_dirs(&root_path, &mut files) {
        eprintln!("Error reading directory: {}", e);
        return;
    }

    // Filter to ELF files and apply project filter
    let mut tasks: Vec<(PathBuf, String, String, bool)> = Vec::new(); // (path, filename, project, expected_accept)

    for path in files {
        if !is_elf_file(&path) {
            continue;
        }

        let filename = path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("")
            .to_string();

        let project = extract_project(&path, &root_path);

        // Apply project filter
        if let Some(filter_proj) = &config.bench_project
            && &project != filter_proj {
                continue;
            }

        // Skip build directory (that's for catalogue-based tests)
        if project == "build" {
            continue;
        }

        // Determine expected outcome: invalid/ should be rejected, others accepted
        let expected_accept = project != "invalid";

        tasks.push((path, filename, project, expected_accept));
    }

    // Sort by project, then filename
    tasks.sort_by(|a, b| (&a.2, &a.1).cmp(&(&b.2, &b.1)));

    let total_count = tasks.len();
    println!("Found {} files matching filters.\n", total_count);

    if total_count == 0 {
        return;
    }

    // Statistics
    let mut stats = BenchmarkStats::default();
    let mut results: Vec<FileResult> = Vec::new();

    // Main analysis loop
    for (i, (path, filename, project, expected_accept)) in tasks.into_iter().enumerate() {
        let path_str = path.to_str().unwrap();

        // Progress
        print!(
            "[{}/{}] [{}] {} ... ",
            i + 1,
            total_count,
            project,
            filename
        );
        std::io::stdout().flush().unwrap();

        let analyzer = Analyzer::new(path_str, config.clone());
        let (_passed, section_results) = analyzer.analyze_all();

        // Analyze results
        let mut all_pass = true;
        let mut has_timeout = false;
        let mut has_failure = false;

        for (_, res) in &section_results {
            match res {
                AnalysisResult::Pass => {}
                AnalysisResult::Timeout => {
                    all_pass = false;
                    has_timeout = true;
                    stats.sections_timeout += 1;
                }
                _ => {
                    all_pass = false;
                    has_failure = true;
                }
            }
        }

        // File-level pass means all sections pass
        let file_passed = all_pass && !section_results.is_empty();
        let file_timeout = has_timeout && !has_failure;

        // Update stats
        stats.total_files += 1;
        stats.total_sections += section_results.len();
        stats.sections_passed += section_results.iter().filter(|(_, r)| r.is_pass()).count();

        if expected_accept {
            stats.expected_accept += 1;
        } else {
            stats.expected_reject += 1;
        }

        if file_passed {
            stats.files_passed += 1;
            if expected_accept {
                println!("PASS");
            } else {
                println!("PASS (expected REJECT - SOUNDNESS ISSUE!)");
                stats.false_negatives += 1;
            }
        } else if file_timeout {
            stats.files_timeout += 1;
            println!("TIMEOUT");
        } else {
            stats.files_failed += 1;
            if expected_accept {
                println!("FAIL (expected ACCEPT - precision issue)");
                stats.false_positives += 1;
            } else {
                println!("FAIL (expected)");
            }
        }

        results.push(FileResult {
            file_name: filename,
            file_path: path_str.to_string(),
            project,
            passed: file_passed,
            timeout: file_timeout,
            expected_accept,
            details: section_results,
        });
    }

    let duration = start_time.elapsed();

    // Print summary
    println!("\n========================================");
    println!("       PREVAIL Benchmark Results");
    println!("========================================");
    println!("Total Files:      {}", stats.total_files);
    println!(
        "Files Passed:     {} ({:.1}%)",
        stats.files_passed,
        stats.file_pass_rate()
    );
    println!("Files Failed:     {}", stats.files_failed);
    println!("Files Timeout:    {}", stats.files_timeout);
    println!();
    println!("Expected ACCEPT:  {}", stats.expected_accept);
    println!("Expected REJECT:  {}", stats.expected_reject);
    if stats.false_negatives > 0 {
        println!(
            "SOUNDNESS ISSUES: {} (expected REJECT, got ACCEPT) <<<",
            stats.false_negatives
        );
    } else {
        println!("Soundness issues: 0 (good!)");
    }
    println!(
        "Precision issues: {} (expected ACCEPT, got REJECT)",
        stats.false_positives
    );
    println!();
    println!("Correctness:      {:.1}%", stats.correctness_rate());
    println!("Duration:         {:.2}s", duration.as_secs_f64());
    println!("========================================\n");

    // Print soundness issues
    for r in &results {
        if !r.expected_accept && r.passed {
            println!(
                "  !!! SOUNDNESS: [{}] {} (expected REJECT, got ACCEPT)",
                r.project, r.file_name
            );
        }
    }

    // Print precision issues
    for r in &results {
        if r.expected_accept && !r.passed && !r.timeout {
            println!("  PRECISION: [{}] {}", r.project, r.file_name);
            for (sec, res) in &r.details {
                if !res.is_pass() {
                    let msg = match res {
                        AnalysisResult::Fail(e) => e.description(),
                        AnalysisResult::LoadError(s) => s.clone(),
                        _ => String::new(),
                    };
                    if !msg.is_empty() {
                        println!("      - {}: {}", sec, msg);
                    }
                }
            }
        }
    }

    // Write reports
    if let Some(dir) = output_dir {
        let _ = fs::create_dir_all(dir);

        // Construct filename
        let mut base_name = String::from("prevail_benchmark");
        if let Some(p) = &config.bench_project {
            base_name.push_str(&format!("_{}", p));
        }
        let timestamp = Local::now().format("%Y-%m-%d_%H-%M-%S").to_string();
        base_name.push_str(&format!("_{}", timestamp));

        let txt_path = format!("{}/{}_report.txt", dir, base_name);
        let json_path = format!("{}/{}_results.json", dir, base_name);

        // Build filter list
        let mut filters_str: Vec<(&str, &str)> = Vec::new();
        if let Some(p) = &config.bench_project {
            filters_str.push(("project", p.as_str()));
        }

        if let Err(e) = benchmark_common::write_text_report(
            &txt_path,
            "PREVAIL Benchmark Report",
            &stats,
            &results,
            duration.as_secs_f64(),
            &filters_str,
        ) {
            eprintln!("Warning: {}", e);
        } else {
            println!("\nText report:  {}", txt_path);
        }

        // For JSON, we need owned strings
        let filters_owned: Vec<(&str, String)> = filters_str
            .iter()
            .map(|(k, v)| (*k, v.to_string()))
            .collect();

        if let Err(e) = benchmark_common::write_json_report(
            &json_path,
            &stats,
            &results,
            duration.as_secs_f64(),
            &filters_owned,
        ) {
            eprintln!("Warning: {}", e);
        } else {
            println!("JSON report:  {}", json_path);
        }
    }
}
