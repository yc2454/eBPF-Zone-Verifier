//! Filesystem helpers shared by the remaining corpus tools.
//!
//! Most of this module's pre-Pass-2 contents (BenchmarkStats, FileResult,
//! write_text_report, write_json_report, …) were aggregation/reporting
//! machinery owned by `bcf_benchmark.rs` and `prevail.rs`. Both moved to
//! Python harnesses on top of `dev verify-corpus`. The only consumer left
//! in Rust is `scanner.rs`, which still wants directory traversal and the
//! `~/` expansion helper.

use std::fs;
use std::path::{Path, PathBuf};

/// Recursively collect every file under `dir` into `files`.
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

/// Expand a leading `~/` to the user's home directory.
pub fn expand_path(path: &str) -> PathBuf {
    if let Some(stripped) = path.strip_prefix("~/") {
        let home = std::env::var("HOME").expect("HOME not set");
        PathBuf::from(home).join(stripped)
    } else {
        PathBuf::from(path)
    }
}

/// True if `path` ends in `.o` (the BPF-object convention).
pub fn is_elf_file(path: &Path) -> bool {
    path.extension().is_some_and(|ext| ext == "o")
}
