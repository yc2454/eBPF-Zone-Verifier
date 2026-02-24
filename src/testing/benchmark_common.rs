//! Common utilities for benchmark modules (BCF and Prevail)
//!
//! Shared types and functions for directory traversal, statistics tracking,
//! and report generation.

use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};

use crate::testing::runner::AnalysisResult;

// ============================================================================
// Shared Types
// ============================================================================

/// Result for a single file analysis
#[derive(Debug)]
pub struct FileResult {
    pub file_name: String,
    #[allow(dead_code)]
    pub file_path: String,
    pub project: String,
    pub passed: bool,
    pub timeout: bool,
    pub expected_accept: bool,
    pub details: Vec<(String, AnalysisResult)>,
}

impl FileResult {
    /// Returns true if the result matches expectation
    pub fn matches_expectation(&self) -> bool {
        if self.expected_accept {
            self.passed
        } else {
            !self.passed && !self.timeout
        }
    }
}

/// Statistics for a benchmark run
#[derive(Debug, Default)]
pub struct BenchmarkStats {
    pub total_files: usize,
    pub files_passed: usize,
    pub files_failed: usize,
    pub files_timeout: usize,
    #[allow(dead_code)]
    pub files_error: usize,

    pub total_sections: usize,
    pub sections_passed: usize,
    pub sections_timeout: usize,

    // For tests with expected outcomes
    pub expected_accept: usize,
    pub expected_reject: usize,
    pub false_positives: usize, // Expected ACCEPT, got REJECT
    pub false_negatives: usize, // Expected REJECT, got ACCEPT (soundness issue!)
}

impl BenchmarkStats {
    pub fn file_pass_rate(&self) -> f64 {
        if self.total_files > 0 {
            100.0 * self.files_passed as f64 / self.total_files as f64
        } else {
            0.0
        }
    }

    pub fn section_pass_rate(&self) -> f64 {
        if self.total_sections > 0 {
            100.0 * self.sections_passed as f64 / self.total_sections as f64
        } else {
            0.0
        }
    }

    pub fn correctness_rate(&self) -> f64 {
        let total = self.expected_accept + self.expected_reject;
        if total > 0 {
            let correct = total - self.false_positives - self.false_negatives;
            100.0 * correct as f64 / total as f64
        } else {
            0.0
        }
    }
}

// ============================================================================
// Directory Traversal
// ============================================================================

/// Recursively collect all files in a directory
pub fn visit_dirs(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if dir.is_dir() {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                visit_dirs(&path, files)?;
            } else {
                files.push(path);
            }
        }
    }
    Ok(())
}

/// Expand ~ in paths to home directory
pub fn expand_path(path: &str) -> PathBuf {
    if let Some(stripped) = path.strip_prefix("~/") {
        let home = std::env::var("HOME").expect("HOME not set");
        PathBuf::from(home).join(stripped)
    } else {
        PathBuf::from(path)
    }
}

/// Extract project name from path (first subdirectory relative to root)
pub fn extract_project(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .ok()
        .and_then(|rel| rel.components().next())
        .map(|c| c.as_os_str().to_string_lossy().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Filter to only ELF object files
pub fn is_elf_file(path: &Path) -> bool {
    path.extension().is_some_and(|ext| ext == "o")
}

// ============================================================================
// Progress Reporting
// ============================================================================

/// Print progress indicator
#[allow(dead_code)]
pub fn print_progress(current: usize, total: usize, project: &str, file: &str) {
    print!("[{}/{}] [{}] {} ... ", current, total, project, file);
    std::io::stdout().flush().unwrap();
}

/// Print result status
#[allow(dead_code)]
pub fn print_status(result: &FileResult) {
    if result.passed {
        if result.expected_accept {
            println!("PASS");
        } else {
            println!("PASS (expected REJECT - SOUNDNESS ISSUE!)");
        }
    } else if result.timeout {
        println!("TIMEOUT");
    } else if result.expected_accept {
        println!("FAIL (expected ACCEPT - precision issue)");
    } else {
        println!("FAIL (expected)");
    }
}

// ============================================================================
// Report Generation
// ============================================================================

/// Write a text report for benchmark results
pub fn write_text_report(
    path: &str,
    title: &str,
    stats: &BenchmarkStats,
    results: &[FileResult],
    duration_secs: f64,
    filters: &[(&str, &str)],
) -> Result<(), String> {
    let mut f = File::create(path).map_err(|e| format!("Failed to create {}: {}", path, e))?;

    writeln!(f, "{}", title).unwrap();
    writeln!(f, "{}", "=".repeat(title.len())).unwrap();
    writeln!(f, "Duration: {:.2}s\n", duration_secs).unwrap();

    // Filters
    if !filters.is_empty() {
        writeln!(f, "Filters:").unwrap();
        for (name, value) in filters {
            writeln!(f, "  {}: {}", name, value).unwrap();
        }
        writeln!(f).unwrap();
    }

    // Summary statistics
    writeln!(f, "--- File Statistics ---").unwrap();
    writeln!(f, "Total Files:    {}", stats.total_files).unwrap();
    writeln!(
        f,
        "Files Passed:   {} ({:.1}%)",
        stats.files_passed,
        stats.file_pass_rate()
    )
    .unwrap();
    writeln!(f, "Files Failed:   {}", stats.files_failed).unwrap();
    writeln!(f, "Files Timeout:  {}", stats.files_timeout).unwrap();

    writeln!(f, "\n--- Section Statistics ---").unwrap();
    writeln!(f, "Total Sections:   {}", stats.total_sections).unwrap();
    writeln!(
        f,
        "Sections Passed:  {} ({:.1}%)",
        stats.sections_passed,
        stats.section_pass_rate()
    )
    .unwrap();
    writeln!(f, "Sections Timeout: {}", stats.sections_timeout).unwrap();

    // Expectation-based stats if applicable
    if stats.expected_accept > 0 || stats.expected_reject > 0 {
        writeln!(f, "\n--- Correctness ---").unwrap();
        writeln!(f, "Expected ACCEPT:  {}", stats.expected_accept).unwrap();
        writeln!(f, "Expected REJECT:  {}", stats.expected_reject).unwrap();
        writeln!(
            f,
            "False Positives:  {} (expected ACCEPT, got REJECT)",
            stats.false_positives
        )
        .unwrap();
        writeln!(
            f,
            "False Negatives:  {} (expected REJECT, got ACCEPT) <<<",
            stats.false_negatives
        )
        .unwrap();
        writeln!(f, "Correctness:      {:.1}%", stats.correctness_rate()).unwrap();
    }

    // Soundness issues first
    let soundness_issues: Vec<_> = results
        .iter()
        .filter(|r| !r.expected_accept && r.passed)
        .collect();
    if !soundness_issues.is_empty() {
        writeln!(f, "\n!!! SOUNDNESS ISSUES !!!").unwrap();
        writeln!(f, "========================").unwrap();
        for r in &soundness_issues {
            writeln!(
                f,
                "  [{}] {} (expected REJECT, got ACCEPT)",
                r.project, r.file_name
            )
            .unwrap();
        }
    }

    // Precision issues
    let precision_issues: Vec<_> = results
        .iter()
        .filter(|r| r.expected_accept && !r.passed && !r.timeout)
        .collect();
    if !precision_issues.is_empty() {
        writeln!(f, "\nPrecision Issues:").unwrap();
        writeln!(f, "-----------------").unwrap();
        for r in &precision_issues {
            writeln!(f, "  [{}] {}", r.project, r.file_name).unwrap();
            for (sec, res) in &r.details {
                if !res.is_pass() {
                    let msg = match res {
                        AnalysisResult::Fail(e) => e.description(),
                        AnalysisResult::LoadError(s) => s.clone(),
                        AnalysisResult::Timeout => "Timeout".to_string(),
                        _ => String::new(),
                    };
                    writeln!(f, "      - {}: {}", sec, msg).unwrap();
                }
            }
        }
    }

    // Group results by project
    writeln!(f, "\n--- Results by Project ---").unwrap();
    let mut by_project: std::collections::BTreeMap<&str, Vec<&FileResult>> =
        std::collections::BTreeMap::new();
    for r in results {
        by_project.entry(&r.project).or_default().push(r);
    }

    for (project, proj_results) in &by_project {
        let passed = proj_results
            .iter()
            .filter(|r| r.matches_expectation())
            .count();
        let total = proj_results.len();
        writeln!(f, "\n[{}] {}/{} correct", project, passed, total).unwrap();

        for r in proj_results {
            let status = if r.matches_expectation() {
                "OK"
            } else if r.timeout {
                "TIMEOUT"
            } else if r.expected_accept {
                "PRECISION"
            } else {
                "SOUNDNESS"
            };
            writeln!(f, "  [{:9}] {}", status, r.file_name).unwrap();
        }
    }

    Ok(())
}

/// Write a JSON report for benchmark results
pub fn write_json_report(
    path: &str,
    stats: &BenchmarkStats,
    results: &[FileResult],
    duration_secs: f64,
    filters: &[(&str, String)],
) -> Result<(), String> {
    let mut f = File::create(path).map_err(|e| format!("Failed to create {}: {}", path, e))?;

    writeln!(f, "{{").unwrap();
    writeln!(f, "  \"summary\": {{").unwrap();

    // Filters
    write!(f, "    \"filters\": {{").unwrap();
    for (i, (name, value)) in filters.iter().enumerate() {
        if i > 0 {
            write!(f, ",").unwrap();
        }
        write!(f, "\n      \"{}\": \"{}\"", name, value).unwrap();
    }
    write!(f, "\n    }},\n").unwrap();

    // Stats
    writeln!(f, "    \"duration_secs\": {:.2},", duration_secs).unwrap();
    writeln!(f, "    \"total_files\": {},", stats.total_files).unwrap();
    writeln!(f, "    \"files_passed\": {},", stats.files_passed).unwrap();
    writeln!(f, "    \"files_failed\": {},", stats.files_failed).unwrap();
    writeln!(f, "    \"files_timeout\": {},", stats.files_timeout).unwrap();
    writeln!(f, "    \"total_sections\": {},", stats.total_sections).unwrap();
    writeln!(f, "    \"sections_passed\": {},", stats.sections_passed).unwrap();
    writeln!(f, "    \"false_positives\": {},", stats.false_positives).unwrap();
    writeln!(f, "    \"false_negatives\": {}", stats.false_negatives).unwrap();
    writeln!(f, "  }},").unwrap();

    // Results by project
    writeln!(f, "  \"results\": [").unwrap();
    for (i, r) in results.iter().enumerate() {
        writeln!(f, "    {{").unwrap();
        writeln!(f, "      \"file\": \"{}\",", r.file_name).unwrap();
        writeln!(f, "      \"project\": \"{}\",", r.project).unwrap();
        writeln!(f, "      \"expected_accept\": {},", r.expected_accept).unwrap();
        writeln!(f, "      \"passed\": {},", r.passed).unwrap();
        writeln!(f, "      \"timeout\": {},", r.timeout).unwrap();
        writeln!(
            f,
            "      \"matches_expectation\": {}",
            r.matches_expectation()
        )
        .unwrap();
        write!(f, "    }}").unwrap();
        if i < results.len() - 1 {
            write!(f, ",").unwrap();
        }
        writeln!(f).unwrap();
    }
    writeln!(f, "  ]").unwrap();
    writeln!(f, "}}").unwrap();

    Ok(())
}
