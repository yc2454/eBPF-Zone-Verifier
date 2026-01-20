// src/main.rs - With configurable verifier options

mod ast;
mod analysis;
mod parsing;
mod zone;
mod misc;
mod logging;

use crate::analysis::context::{ExecContext, default_exec_ctx};
use crate::analysis::env::VerificationError;
use crate::misc::config::VerifierConfig;
use crate::zone::dbm::Dbm;
use crate::zone::domain::{REG_ENV, assign_zero};
use crate::misc::utils::{load_program_from_elf, program_kind_for_object};
use crate::parsing::elf_loader::{
    load_maps, load_relocations, load_data_section_maps,
    load_raw_programs, list_section_names, BpfMapDef
};
use crate::parsing::elf_loader::{self};
use crate::parsing::btf::{self, BtfContext};
use crate::ast::ProgramKind;
use crate::logging::{FilterConfig};

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn usage() {
    eprintln!("Usage:");
    eprintln!("  cargo run -- [flags] elf-list        <elf_path>");
    eprintln!("  cargo run -- [flags] elf-analyze     <elf_path> <section_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-func <elf_path> <func_name>");
    eprintln!("  cargo run -- [flags] elf-analyze-prog <elf_path>");
    eprintln!("  cargo run -- [flags] elf-analyze-benchmark <dir_path> [project_name]");
    eprintln!("");
    VerifierConfig::print_help();
    eprintln!("");
    eprintln!("Examples:");
    eprintln!("  cargo run -- elf-list ./bpf_host.o");
    eprintln!("  cargo run -- elf-analyze ./bpf_host.o tc");
    eprintln!("  cargo run -- elf-analyze-benchmark ./bpf-progs cilium");
}

fn make_entry_state(ctx: &ExecContext) -> Dbm {
    let mut dbm = Dbm::new(REG_ENV.len());
    assign_zero(&mut dbm, ctx.r10, ctx.zero);
    dbm
}

/// Result of analyzing a single section
#[derive(Debug)]
enum AnalysisResult {
    Pass,
    Fail(VerificationError),
    LoadError(String),
}

impl AnalysisResult {
    fn is_pass(&self) -> bool {
        matches!(self, AnalysisResult::Pass)
    }
}

// --- Shared Analyzer Logic ---

struct Analyzer {
    path: String,
    config: VerifierConfig,
    maps: Vec<BpfMapDef>,
    btf: BtfContext,
}

impl Analyzer {
    /// Initialize analyzer for a specific ELF file.
    /// Loads shared resources (Maps, BTF) once.
    fn new(path: &str, config: VerifierConfig) -> Self {
        // Load maps (explicit + data sections)
        let explicit_maps = load_maps(path).unwrap_or_default();
        let data_maps = load_data_section_maps(path).unwrap_or_default();
        let mut all_maps = explicit_maps;
        all_maps.extend(data_maps);

        // Apply map size overrides from config
        for m in &mut all_maps {
            if let Some(&new_size) = config.map_overrides.get(&m.name) {
                if config.verbosity > 0 {
                    println!("Overriding map '{}' size: {} -> {}", m.name, m.value_size, new_size);
                }
                m.value_size = new_size;
            }
        }

        // Load BTF
        let btf_bytes = elf_loader::load_section_bytes(path, ".BTF", false).unwrap_or_default();
        let btf = if !btf_bytes.is_empty() {
            btf::parse_btf(&btf_bytes).unwrap_or_else(|e| {
                if config.verbosity > 0 { println!("BTF Parse Warning: {}", e); }
                btf::BtfContext::new()
            })
        } else {
            btf::BtfContext::new()
        };

        Analyzer {
            path: path.to_string(),
            config,
            maps: all_maps,
            btf,
        }
    }

    /// Analyze a single section by name
    fn analyze_section(&self, section: &str) -> AnalysisResult {
        // Load program
        let prog = load_program_from_elf(&self.path, section);
        if prog.instrs.is_empty() {
            return AnalysisResult::LoadError("Empty program or section not found".to_string());
        }

        if self.config.verbosity > 0 {
            println!("Analyzing Section: '{}' ({} insns)", section, prog.instrs.len());
        }

        // Build context
        let mut ctx = default_exec_ctx();
        ctx.map_defs = self.maps.clone();
        ctx.btf = self.btf.clone();
        
        // Load relocations specific to this section
        ctx.pc_to_reloc = load_relocations(&self.path, &self.maps, section).unwrap_or_default();
        
        // Determine program kind
        ctx.prog_kind = match program_kind_for_object(Path::new(&self.path)) {
            Ok(kind) => kind,
            Err(_) => ProgramKind::from_section(section),
        };

        if self.config.verbosity > 0 {
            println!("  Program kind: {:?}", ctx.prog_kind);
        }

        // Run analysis
        let entry = make_entry_state(&ctx);
        let result = analysis::analyze_program(&ctx, &prog, entry, &self.config);

        match result {
            Ok(_) => AnalysisResult::Pass,
            Err(e) => AnalysisResult::Fail(e),
        }
    }

    /// Analyze all code sections in the file
    fn analyze_all(&self) -> (bool, Vec<(String, AnalysisResult)>) {
        let sections = list_section_names(&self.path).unwrap_or_default();
        let mut results = Vec::new();
        let mut all_pass = true;

        for section in sections {
            if !is_code_section(&section) { continue; }
            
            // Skip loading if program is empty (optimization)
            let prog_check = load_program_from_elf(&self.path, &section);
            if prog_check.instrs.is_empty() { continue; }

            let result = self.analyze_section(&section);
            
            if !result.is_pass() {
                all_pass = false;
            }
            results.push((section, result));
        }
        (all_pass, results)
    }
}

/// Helper: Find section name for a given function symbol
fn find_section_for_func(path: &str, func_name: &str) -> Option<String> {
    let progs = load_raw_programs(path).ok()?;
    let target = progs.iter().find(|p| p.name == func_name)?;
    let sections = list_section_names(path).ok()?;
    sections.get(target.section_idx).map(|s| s.to_string())
}

/// Check if a section contains BPF code
fn is_code_section(name: &str) -> bool {
    if name.is_empty() { return false; }
    if name.starts_with('.') { return false; }
    if name == "license" || name == "version" || name == "maps" { return false; }
    true
}

// --- Benchmark Logic ---

struct FileResult {
    file_name: String,
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

fn analyze_benchmark(dir_path: &str, project_filter: Option<&String>, config: &VerifierConfig) {
    println!("=== Starting Benchmark Analysis ===");
    println!("Root Directory: {}", dir_path);
    if let Some(proj) = project_filter {
        println!("Project Filter: {}", proj);
    }
    println!("Config: max_insn={}, skip_dbm={}", config.max_insn, config.skip_dbm_check);

    let start_time = Instant::now();
    let mut files = Vec::new();

    // If a project filter is provided, append it to the path
    let search_path = if let Some(proj) = project_filter {
        Path::new(dir_path).join(proj)
    } else {
        PathBuf::from(dir_path)
    };

    if !search_path.exists() || !search_path.is_dir() {
        eprintln!("Error: Directory does not exist: {:?}", search_path);
        return;
    }

    if let Err(e) = visit_dirs(&search_path, &mut files) {
        eprintln!("Error reading directory: {}", e);
        return;
    }

    let elf_files: Vec<&PathBuf> = files.iter()
        .filter(|p| p.extension().map_or(false, |ext| ext == "o"))
        .collect();

    println!("Found {} ELF files to analyze in {:?}.\n", elf_files.len(), search_path);

    let mut grouped_results: BTreeMap<String, Vec<FileResult>> = BTreeMap::new();
    
    // Statistics Counters
    let mut total_files = 0;
    let mut total_files_passed = 0;
    let mut total_sections = 0;
    let mut total_sections_passed = 0;

    for (idx, path) in elf_files.iter().enumerate() {
        let filename = path.file_name().unwrap().to_str().unwrap();
        let (compiler, opt, source_prog) = parse_benchmark_filename(filename);
        let path_str = path.to_str().unwrap();

        print!("[{}/{}] Analyzing {} ... ", idx + 1, elf_files.len(), filename);
        std::io::stdout().flush().unwrap();

        // Use the unified Analyzer
        let analyzer = Analyzer::new(path_str, config.clone());
        let (passed, section_results) = analyzer.analyze_all();

        // Update stats
        total_files += 1;
        if passed {
            total_files_passed += 1;
            println!("PASS");
        } else {
            println!("FAIL");
        }

        let file_sections = section_results.len();
        let file_passed_sections = section_results.iter().filter(|(_, res)| res.is_pass()).count();
        
        total_sections += file_sections;
        total_sections_passed += file_passed_sections;

        let res = FileResult {
            file_name: filename.to_string(),
            compiler,
            opt,
            source_prog: source_prog.clone(),
            passed,
            details: section_results,
        };

        grouped_results.entry(source_prog).or_default().push(res);
    }

    let duration = start_time.elapsed();

    // --- Generate Text Report ---
    let report_path = "benchmark_report.txt";
    let mut report = File::create(report_path).expect("Could not create report file");

    writeln!(report, "BPF Verifier Benchmark Report").unwrap();
    writeln!(report, "=============================").unwrap();
    if let Some(proj) = project_filter {
        writeln!(report, "Project:    {}", proj).unwrap();
    }
    writeln!(report, "Date:       {}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()).unwrap();
    writeln!(report, "Duration:   {:.2?}", duration).unwrap();
    
    writeln!(report, "\n--- Program Statistics ---").unwrap();
    writeln!(report, "Total ELFs: {}", total_files).unwrap();
    let prog_rate = if total_files > 0 { (total_files_passed as f64 / total_files as f64) * 100.0 } else { 0.0 };
    writeln!(report, "Passing:    {} ({:.1}%)", total_files_passed, prog_rate).unwrap();

    writeln!(report, "\n--- Section Statistics ---").unwrap();
    writeln!(report, "Total Sections: {}", total_sections).unwrap();
    let sec_rate = if total_sections > 0 { (total_sections_passed as f64 / total_sections as f64) * 100.0 } else { 0.0 };
    writeln!(report, "Passing:        {} ({:.1}%)", total_sections_passed, sec_rate).unwrap();

    writeln!(report, "\n--- Breakdown by Source Program ---").unwrap();

    for (source, runs) in &grouped_results {
        writeln!(report, "\nSource: {}", source).unwrap();
        let mut sorted_runs: Vec<&FileResult> = runs.iter().collect();
        sorted_runs.sort_by_key(|r| (&r.compiler, &r.opt));

        for run in sorted_runs {
            let status = if run.passed { "PASS" } else { "FAIL" };
            writeln!(report, "  [{}] {} {}: {}", status, run.compiler, run.opt, run.file_name).unwrap();
            
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
    println!("Programs: {}/{} ({:.1}%)", total_files_passed, total_files, prog_rate);
    println!("Sections: {}/{} ({:.1}%)", total_sections_passed, total_sections, sec_rate);
    println!("Report written to '{}'", report_path);

    // --- Generate JSON ---
    let json_path = "benchmark_results.json";
    let mut json_file = File::create(json_path).expect("Could not create JSON file");
    
    write!(json_file, "{{\n").unwrap();
    write!(json_file, "  \"summary\": {{\n").unwrap();
    if let Some(proj) = project_filter {
        write!(json_file, "    \"project\": \"{}\",\n", proj).unwrap();
    }
    write!(json_file, "    \"total_files\": {},\n", total_files).unwrap();
    write!(json_file, "    \"passed_files\": {},\n", total_files_passed).unwrap();
    write!(json_file, "    \"total_sections\": {},\n", total_sections).unwrap();
    write!(json_file, "    \"passed_sections\": {},\n", total_sections_passed).unwrap();
    write!(json_file, "    \"duration_secs\": {:.2}\n", duration.as_secs_f64()).unwrap();
    write!(json_file, "  }},\n").unwrap();
    write!(json_file, "  \"results_by_source\": {{\n").unwrap();

    for (i, (source, runs)) in grouped_results.iter().enumerate() {
        write!(json_file, "    \"{}\": [\n", source).unwrap();
        for (j, run) in runs.iter().enumerate() {
            write!(json_file, "      {{\n").unwrap();
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

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        usage();
        return;
    }

    // Parse config flags and get remaining positional args
    let (config, remaining) = VerifierConfig::from_args(&args[1..]);

    // Initialize logging
    logging::VerifierLogger::init(config.verbosity);

    // If debug_pc is set, configure logging filter
    if let Some(target_pc) = config.debug_pc {
        let filter = FilterConfig {
            pc_range: Some(target_pc.saturating_sub(10)..=target_pc + 10),
            interesting_regs: vec![],
        };
        logging::VerifierLogger::set_config(filter);
    }
    
    if remaining.is_empty() {
        usage();
        return;
    }

    let cmd = &remaining[0];

    match cmd.as_str() {
        // ============================================================
        // List all sections and programs in an ELF
        // ============================================================
        "elf-list" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &remaining[1];

            println!("=== ELF Contents: '{}' ===\n", path);
            println!("--- SECTIONS ---");
            match list_section_names(path) {
                Ok(sections) => {
                    for (i, name) in sections.iter().enumerate() {
                        if is_code_section(name) {
                            println!("  [{}] {}", i, name);
                        }
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }
            println!("\n--- BPF PROGRAMS ---");
            match load_raw_programs(path) {
                Ok(progs) => {
                    for (i, p) in progs.iter().enumerate() {
                        println!("  [{}] {} ({} insns)", i, p.name, p.data.len() / 8);
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }
            println!("\n--- BPF MAPS ---");
            match load_maps(path) {
                Ok(maps) => {
                    for (i, m) in maps.iter().enumerate() {
                        println!("  [{}] {} (k:{}, v:{})", i, m.name, m.key_size, m.value_size);
                    }
                }
                Err(e) => eprintln!("  Error: {:?}", e),
            }
        }

        // ============================================================
        // Analyze by section name
        // ============================================================
        "elf-analyze-section" | "elf-analyze" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &remaining[1];
            let section = &remaining[2];

            println!("=== Analyzing: '{}' section '{}' ===", path, section);
            
            let analyzer = Analyzer::new(path, config);
            let result = analyzer.analyze_section(section);
            
            match result {
                AnalysisResult::Pass => println!("\n=== PASS ==="),
                AnalysisResult::Fail(e) => println!("\n=== FAIL: {} ===", e.description()),
                AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
            }
        }

        // ============================================================
        // Analyze by function name
        // ============================================================
        "elf-analyze-func" => {
            if remaining.len() < 3 {
                eprintln!("Error: Missing arguments");
                usage();
                return;
            }
            let path = &remaining[1];
            let func_name = &remaining[2];

            println!("=== Analyzing function: '{}' in '{}' ===", func_name, path);

            if let Some(section_name) = find_section_for_func(path, func_name) {
                let analyzer = Analyzer::new(path, config);
                let result = analyzer.analyze_section(&section_name);
                
                match result {
                    AnalysisResult::Pass => println!("\n=== PASS ==="),
                    AnalysisResult::Fail(e) => println!("\n=== FAIL: {} ===", e.description()),
                    AnalysisResult::LoadError(e) => println!("\n=== LOAD ERROR: {} ===", e),
                }
            } else {
                eprintln!("Function '{}' not found or section lookup failed.", func_name);
            }
        }

        // ============================================================
        // Batch analyze all sections in an ELF
        // ============================================================
        "elf-analyze-prog" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing ELF path");
                usage();
                return;
            }
            let path = &remaining[1];

            println!("=== Batch Analysis: '{}' ===\n", path);
            println!("Config: max_insn={}, skip_dbm={}, verbosity={}", 
                     config.max_insn, config.skip_dbm_check, config.verbosity);

            let analyzer = Analyzer::new(path, config);
            let (_, results) = analyzer.analyze_all();

            let mut pass_count = 0;
            let mut fail_count = 0;
            let mut error_count = 0;

            for (section, res) in &results {
                print!("Section '{}'... ", section);
                match res {
                    AnalysisResult::Pass => {
                        println!("PASS");
                        pass_count += 1;
                    },
                    AnalysisResult::Fail(_) => {
                        println!("FAIL");
                        fail_count += 1;
                    },
                    AnalysisResult::LoadError(e) => {
                        println!("ERROR ({})", e);
                        error_count += 1;
                    }
                }
            }

            println!("\n========================================");
            println!("              SUMMARY");
            println!("========================================");
            println!("Total:  {}", results.len());
            if !results.is_empty() {
                println!("Pass:   {} ({:.1}%)", pass_count, 100.0 * pass_count as f64 / results.len() as f64);
            }
            println!("Fail:   {}", fail_count);
            println!("Errors: {}", error_count);

            if fail_count > 0 {
                println!("\n--- FAILURES ---");
                for (section, res) in &results {
                    if let AnalysisResult::Fail(e) = res {
                        println!("  {}: {}", section, e.description());
                    }
                }
            }
            println!("\n=== Done ===");
        }

        // ============================================================
        // BENCHMARK COMMAND (Recursive directory analysis)
        // ============================================================
        "elf-analyze-benchmark" => {
            if remaining.len() < 2 {
                eprintln!("Error: Missing benchmark directory path");
                usage();
                return;
            }
            let dir_path = &remaining[1];
            let project_filter = if remaining.len() > 2 {
                Some(&remaining[2])
            } else {
                None
            };
            analyze_benchmark(dir_path, project_filter, &config);
        }

        _ => {
            eprintln!("Unknown command: {}", cmd);
            usage();
        }
    }
}