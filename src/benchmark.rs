// src/benchmark.rs

use crate::misc::config::VerifierConfig;
use crate::runner::{Analyzer, AnalysisResult};
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

// ... (FileResult struct and helper functions remain the same) ...
struct FileResult {
    file_name: String,
    project: String,
    compiler: String,
    opt: String,
    source_prog: String,
    passed: bool,
    details: Vec<(String, AnalysisResult)>,
}

fn parse_benchmark_filename(name: &str) -> (String, String, String) {
    // Expected format: clang-<VER>_-<OPT>_<SOURCE>.o
    let fallback = ("unknown".to_string(), "unknown".to_string(), name.to_string());
    if !name.starts_with("clang-") { return fallback; }

    let parts: Vec<&str> = name.splitn(3, '_').collect();
    if parts.len() < 3 { return fallback; }

    let compiler = parts[0].to_string(); 
    let opt = parts[1].to_string();      
    let source_part = parts[2];
    let source_prog = source_part.strip_suffix(".o").unwrap_or(source_part).to_string();

    (compiler, opt, source_prog)
}

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

pub fn analyze_benchmark(dir_path: &str, config: &VerifierConfig) {
    println!("=== Starting Benchmark Analysis ===");
    println!("Root Directory: {}", dir_path);
    if let Some(p) = &config.bench_project { println!("Filter [Project]:  {}", p); }
    if let Some(c) = &config.bench_compiler { println!("Filter [Compiler]: {}", c); }
    if let Some(o) = &config.bench_opt { println!("Filter [Opt]:      {}", o); }
    if let Some(s) = &config.bench_source { println!("Filter [Source]:   {}", s); }

    let start_time = Instant::now();
    let root_path = Path::new(dir_path);
    let mut files = Vec::new();

    if !root_path.exists() || !root_path.is_dir() {
        eprintln!("Error: Directory does not exist: {:?}", root_path);
        return;
    }

    if let Err(e) = visit_dirs(root_path, &mut files) {
        eprintln!("Error reading directory: {}", e);
        return;
    }

    // 1. Identify all ELF files
    let all_elf_files: Vec<&PathBuf> = files.iter()
        .filter(|p| p.extension().map_or(false, |ext| ext == "o"))
        .collect();

    // 2. Pre-Calculate Metadata & Apply Filters
    // We map to a tuple (path, project, compiler, opt, source) to avoid re-parsing later
    let mut tasks = Vec::new();
    
    for path in all_elf_files {
        let filename = path.file_name().unwrap().to_str().unwrap();
        let (compiler, opt, source_prog) = parse_benchmark_filename(filename);
        
        // Determine Project
        let relative = path.strip_prefix(root_path).unwrap_or(path);
        let project = relative.components().next()
            .map(|c| c.as_os_str().to_string_lossy().to_string())
            .unwrap_or_else(|| "unknown".to_string());

        // Apply Filters HERE
        if let Some(f_proj) = &config.bench_project { if &project != f_proj { continue; } }
        if let Some(f_comp) = &config.bench_compiler { if &compiler != f_comp { continue; } }
        if let Some(f_opt) = &config.bench_opt { if &opt != f_opt { continue; } }
        if let Some(f_src) = &config.bench_source { if &source_prog != f_src { continue; } }

        tasks.push((path, filename, project, compiler, opt, source_prog));
    }

    let total_files_count = tasks.len();
    println!("Found {} files matching filters.\n", total_files_count);

    if total_files_count == 0 {
        return;
    }

    let mut grouped_results: BTreeMap<String, Vec<FileResult>> = BTreeMap::new();
    
    // Statistics Counters
    let mut total_files_processed = 0;
    let mut total_files_passed = 0;
    let mut total_sections_processed = 0;
    let mut total_sections_passed = 0;

    // 3. Main Loop over Filtered Tasks
    for (i, (path, filename, project, compiler, opt, source_prog)) in tasks.into_iter().enumerate() {
        let path_str = path.to_str().unwrap();
        
        // Progress Indicator
        print!("[{}/{}] [Project: {}] Analyzing {} ... ", 
               i + 1, total_files_count, project, filename);
        std::io::stdout().flush().unwrap();

        let analyzer = Analyzer::new(path_str, config.clone());
        let (passed, section_results) = analyzer.analyze_all();

        // Update stats
        total_files_processed += 1;
        if passed {
            total_files_passed += 1;
            println!("PASS");
        } else {
            println!("FAIL");
        }

        let file_sections = section_results.len();
        let file_passed_sections = section_results.iter().filter(|(_, res)| res.is_pass()).count();
        
        total_sections_processed += file_sections;
        total_sections_passed += file_passed_sections;

        let res = FileResult {
            file_name: filename.to_string(),
            project,
            compiler,
            opt,
            source_prog,
            passed,
            details: section_results,
        };

        grouped_results.entry(res.source_prog.clone()).or_default().push(res);
    }

    let duration = start_time.elapsed();

    // Construct dynamic filename
    let mut base_name = String::from("benchmark");
    if let Some(p) = &config.bench_project { base_name.push_str(&format!("_{}", p)); }
    if let Some(c) = &config.bench_compiler { base_name.push_str(&format!("_{}", c)); }
    if let Some(o) = &config.bench_opt { base_name.push_str(&format!("_{}", o)); }
    if let Some(s) = &config.bench_source { base_name.push_str(&format!("_{}", s)); }

    // Ensure 'results' directory exists
    let results_dir = "results";
    if let Err(e) = fs::create_dir_all(results_dir) {
        eprintln!("Error: Could not create 'results' directory: {}", e);
        return;
    }

    // --- Generate Text Report ---
    let report_path = format!("{}/{}_report.txt", results_dir, base_name);
    let mut report = File::create(&report_path).expect("Could not create report file");

    writeln!(report, "BPF Verifier Benchmark Report").unwrap();
    writeln!(report, "=============================").unwrap();
    writeln!(report, "Date:       {}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()).unwrap();
    writeln!(report, "Duration:   {:.2?}", duration).unwrap();
    if let Some(p) = &config.bench_project { writeln!(report, "Filter [Project]:  {}", p).unwrap(); }
    if let Some(c) = &config.bench_compiler { writeln!(report, "Filter [Compiler]: {}", c).unwrap(); }
    
    writeln!(report, "\n--- Program Statistics ---").unwrap();
    writeln!(report, "Total Files Found: {}", total_files_processed).unwrap();
    let prog_rate = if total_files_processed > 0 { (total_files_passed as f64 / total_files_processed as f64) * 100.0 } else { 0.0 };
    writeln!(report, "Files Passing:     {} ({:.1}%)", total_files_passed, prog_rate).unwrap();

    writeln!(report, "\n--- Section Statistics ---").unwrap();
    writeln!(report, "Total Sections:    {}", total_sections_processed).unwrap();
    let sec_rate = if total_sections_processed > 0 { (total_sections_passed as f64 / total_sections_processed as f64) * 100.0 } else { 0.0 };
    writeln!(report, "Sections Passing:  {} ({:.1}%)", total_sections_passed, sec_rate).unwrap();

    writeln!(report, "\n--- Breakdown by Source Program ---").unwrap();

    for (source, runs) in &grouped_results {
        writeln!(report, "\nSource: {}", source).unwrap();
        let mut sorted_runs: Vec<&FileResult> = runs.iter().collect();
        sorted_runs.sort_by_key(|r| (&r.project, &r.compiler, &r.opt));

        for run in sorted_runs {
            let status = if run.passed { "PASS" } else { "FAIL" };
            writeln!(report, "  [{}] [{}] {} {}: {}", status, run.project, run.compiler, run.opt, run.file_name).unwrap();
            
            if !run.passed {
                for (sec, res) in &run.details {
                    if !res.is_pass() {
                        let err_msg = match res {
                            AnalysisResult::Fail(e) => e.description(),
                            AnalysisResult::LoadError(s) => s.clone(),
                            _ => "".to_string()
                        };
                        writeln!(report, "      - {}: {}", sec, err_msg).unwrap();
                    }
                }
            }
        }
    }

    println!("\nAnalysis complete.");
    println!("Programs: {}/{} ({:.1}%)", total_files_passed, total_files_processed, prog_rate);
    println!("Sections: {}/{} ({:.1}%)", total_sections_passed, total_sections_processed, sec_rate);
    println!("Report written to '{}'", report_path);

    // --- Generate JSON ---
    let json_path = format!("{}/{}_results.json", results_dir, base_name);
    let mut json_file = File::create(&json_path).expect("Could not create JSON file");
    
    write!(json_file, "{{\n").unwrap();
    write!(json_file, "  \"summary\": {{\n").unwrap();
    write!(json_file, "    \"filters\": {{\n").unwrap();
    if let Some(p) = &config.bench_project { write!(json_file, "      \"project\": \"{}\",\n", p).unwrap(); }
    if let Some(c) = &config.bench_compiler { write!(json_file, "      \"compiler\": \"{}\",\n", c).unwrap(); }
    if let Some(o) = &config.bench_opt { write!(json_file, "      \"opt\": \"{}\",\n", o).unwrap(); }
    if let Some(s) = &config.bench_source { write!(json_file, "      \"source\": \"{}\"\n", s).unwrap(); }
    write!(json_file, "      \"none\": null\n").unwrap(); 
    write!(json_file, "    }},\n").unwrap();
    write!(json_file, "    \"files_processed\": {},\n", total_files_processed).unwrap();
    write!(json_file, "    \"files_passed\": {},\n", total_files_passed).unwrap();
    write!(json_file, "    \"sections_processed\": {},\n", total_sections_processed).unwrap();
    write!(json_file, "    \"sections_passed\": {},\n", total_sections_passed).unwrap();
    write!(json_file, "    \"duration_secs\": {:.2}\n", duration.as_secs_f64()).unwrap();
    write!(json_file, "  }},\n").unwrap();
    write!(json_file, "  \"results_by_source\": {{\n").unwrap();

    for (i, (source, runs)) in grouped_results.iter().enumerate() {
        write!(json_file, "    \"{}\": [\n", source).unwrap();
        for (j, run) in runs.iter().enumerate() {
            write!(json_file, "      {{\n").unwrap();
            write!(json_file, "        \"project\": \"{}\",\n", run.project).unwrap();
            write!(json_file, "        \"compiler\": \"{}\",\n", run.compiler).unwrap();
            write!(json_file, "        \"opt\": \"{}\",\n", run.opt).unwrap();
            write!(json_file, "        \"passed\": {},\n", run.passed).unwrap();
            write!(json_file, "        \"file\": \"{}\"\n", run.file_name).unwrap();
            write!(json_file, "      }}").unwrap();
            if j < runs.len() - 1 { write!(json_file, ",").unwrap(); }
            write!(json_file, "\n").unwrap();
        }
        write!(json_file, "    ]").unwrap();
        if i < grouped_results.len() - 1 { write!(json_file, ",").unwrap(); }
        write!(json_file, "\n").unwrap();
    }
    write!(json_file, "  }}\n").unwrap();
    write!(json_file, "}}\n").unwrap();

    println!("JSON data written to '{}'", json_path);
}