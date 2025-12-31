// src/bin/zone_batch.rs
use std::fs;
use std::path::{Path, PathBuf};
use crate::exec::{analyze_program_for_file};
use crate::stats::AnalysisStats;

fn is_elf_candidate(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    match path.extension().and_then(|s| s.to_str()) {
        Some("o") | Some("elf") | Some("so") => true,
        _ => false,
    }
}

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let dir = args
        .next()
        .expect("Usage: zone_batch <directory-with-elfs>");

    let dir_path = PathBuf::from(dir);

    let mut total = 0usize;
    let mut safe = 0usize;
    let mut dangerous = 0usize;

    let mut dangerous_files: Vec<(PathBuf, AnalysisStats)> = Vec::new();

    for entry in fs::read_dir(&dir_path)? {
        let entry = entry?;
        let path = entry.path();

        if !is_elf_candidate(&path) {
            continue;
        }

        total += 1;
        println!("=== Analyzing {} ===", path.display());

        match analyze_program_for_file(&path) {
            Ok(stats) => {
                if stats.dangerous {
                    dangerous += 1;
                    println!("=> DANGEROUS\n");
                    dangerous_files.push((path.clone(), stats));
                } else {
                    safe += 1;
                    println!("=> SAFE\n");
                }
            }
            Err(e) => {
                // If we can't even analyze, treat as dangerous.
                dangerous += 1;
                println!("=> ERROR during analysis ({})", e);
                let mut stats = AnalysisStats::default();
                stats.dangerous = true;
                dangerous_files.push((path.clone(), stats));
            }
        }
    }

    println!("=== SUMMARY for {} ===", dir_path.display());
    println!("Total ELF files:    {}", total);
    println!("Safe:               {}", safe);
    println!("Dangerous / error:  {}", dangerous);

    if !dangerous_files.is_empty() {
        println!("\nDetails for dangerous files:");
        for (path, stats) in &dangerous_files {
            println!("  - {}", path.display());
            if stats.unsafe_stack_load {
                println!("      * unsafe stack load");
            }
            if stats.unsafe_stack_store {
                println!("      * unsafe stack store");
            }
            if stats.dbm_inconsistent {
                println!("      * DBM inconsistency");
            }
            if stats.unsupported_opcode {
                println!("      * unsupported opcode");
            }
        }
    }

    Ok(())
}
