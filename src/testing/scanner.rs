//! `dev benchmark-scan <dir> <out.json>` — ELF/BTF metadata extractor.
//!
//! For every `.o` under `<dir>`, lists each code section that loads
//! cleanly and the function names declared in it. Pure parsing — no
//! verification work happens here. Used to build catalogues / scoping
//! reports without invoking the verifier.

use crate::parsing::elf::{get_functions_in_section, list_section_names};
use crate::testing::runner::is_code_section;
use anyhow::{Context, Result};
use serde::Serialize;
use std::fs::{self, File};
use std::io::BufWriter;
use std::path::{Path, PathBuf};

#[derive(Serialize)]
pub struct ElfScanResult {
    pub file: String,
    pub sections: Vec<SectionScanInfo>,
}

#[derive(Serialize)]
pub struct SectionScanInfo {
    pub name: String,
    pub functions: Vec<String>,
}

pub fn scan_benchmark_dir(dir_path: &str, output_json: &str) -> Result<()> {
    let root_path = expand_tilde(dir_path);
    if !root_path.exists() || !root_path.is_dir() {
        return Err(anyhow::anyhow!("Directory does not exist: {:?}", root_path));
    }

    println!("Scanning directory: {:?}", root_path);

    let mut files = Vec::new();
    visit_dirs(&root_path, &mut files).context("Failed to visit directories")?;

    let mut results = Vec::new();

    for path in files {
        if !is_elf_file(&path) {
            continue;
        }

        let file_name = path.to_string_lossy().to_string();
        let mut sections_info = Vec::new();

        if let Ok(sections) = list_section_names(&path) {
            for section in sections {
                if !is_code_section(&section) {
                    continue;
                }

                // Verify section is non-empty and valid BPF (matching analyze_all logic)
                let prog_check = match crate::parsing::elf::try_load_program_from_elf(
                    &file_name, &section, None,
                ) {
                    Ok(p) => p,
                    Err(_) => continue,
                };
                if prog_check.instrs.is_empty() {
                    continue;
                }

                let functions = match get_functions_in_section(&path, &section) {
                    Ok(funcs) => funcs.into_iter().map(|f| f.name).collect(),
                    Err(_) => Vec::new(),
                };

                sections_info.push(SectionScanInfo {
                    name: section,
                    functions,
                });
            }
        }

        results.push(ElfScanResult {
            file: file_name,
            sections: sections_info,
        });
    }

    println!(
        "Found {} ELF files. Writing to {}...",
        results.len(),
        output_json
    );

    let file = File::create(output_json).context("Failed to create output JSON file")?;
    let writer = BufWriter::new(file);
    serde_json::to_writer_pretty(writer, &results).context("Failed to write JSON content")?;

    println!("Done.");
    Ok(())
}

// --- Local filesystem helpers ---
//
// Trivial enough to live next to their only caller; previously lived in
// `benchmark_common.rs` alongside the (now-deleted) bcf/prevail Rust
// harnesses.

fn visit_dirs(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
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

fn expand_tilde(path: &str) -> PathBuf {
    if let Some(stripped) = path.strip_prefix("~/") {
        let home = std::env::var("HOME").expect("HOME not set");
        PathBuf::from(home).join(stripped)
    } else {
        PathBuf::from(path)
    }
}

fn is_elf_file(path: &Path) -> bool {
    path.extension().is_some_and(|ext| ext == "o")
}
