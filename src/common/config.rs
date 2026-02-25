// src/analysis/config.rs
//
// Verifier configuration - controls analysis behavior via command-line flags.

/// Verifier configuration options
#[derive(Clone, Debug)]
pub struct VerifierConfig {
    /// Verbosity level (0=quiet, 1=info, 2=trace, 3=debug)
    pub verbosity: u8,

    /// Maximum instructions to process before aborting
    pub max_insn: usize,

    /// Skip DBM (numeric) comparison in pruning - faster but less precise
    pub skip_dbm_check: bool,

    /// Use widening in pruning - might cause unsoundness but guarantees loop termination
    pub use_widening: bool,

    /// Maximum states to keep per PC for pruning
    pub max_states_per_pc: usize,

    /// Log heartbeat interval
    pub log_interval: usize,

    /// Debug a specific PC (force verbose logging at this PC)
    pub debug_pc: Option<usize>,

    /// Enable path tracing for crash analysis
    pub enable_path_trace: bool,

    /// A manual override for map file descriptors to sizes
    pub map_overrides: std::collections::HashMap<String, u32>,

    // --- Benchmark Filters ---
    /// Filter benchmark by project (subdirectory name)
    pub bench_project: Option<String>,
    /// Filter benchmark by compiler version (e.g., "clang-16")
    pub bench_compiler: Option<String>,
    /// Filter benchmark by optimization level (e.g., "-O1")
    pub bench_opt: Option<String>,
    /// Filter benchmark by source program name (e.g., "bpf_host")
    pub bench_source: Option<String>,

    // --- Benchmark Input ---
    /// Optional: Path to a file containing a list of ELF paths to analyze
    pub bench_input_file: Option<String>,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self {
            verbosity: 1,
            max_insn: 1_000_0, // 1 million instructions to match modern kernel limits
            skip_dbm_check: false,
            use_widening: false,
            max_states_per_pc: 8,
            log_interval: 100_000,
            debug_pc: None,
            enable_path_trace: false,
            map_overrides: std::collections::HashMap::new(),
            bench_project: None,
            bench_compiler: None,
            bench_opt: None,
            bench_source: None,
            bench_input_file: None,
        }
    }
}

impl VerifierConfig {
    /// Parse configuration from command-line arguments.
    /// Returns (config, remaining_args) where remaining_args are non-flag arguments.
    pub fn from_args(args: &[String]) -> (Self, Vec<String>) {
        let mut config = Self::default();
        let mut remaining = Vec::new();

        let mut i = 0;
        while i < args.len() {
            let arg = &args[i];

            if arg.starts_with("--") || arg.starts_with("-") {
                match arg.as_str() {
                    "-v" | "--verbose" => {
                        config.verbosity = 2;
                    }
                    "-vv" | "--very-verbose" => {
                        config.verbosity = 3;
                    }
                    "-q" | "--quiet" => {
                        config.verbosity = 0;
                    }
                    "--skip-dbm" => {
                        config.skip_dbm_check = true;
                    }
                    "--use-widening" => {
                        config.use_widening = true;
                    }
                    "--enable-path-trace" => {
                        config.enable_path_trace = true;
                    }
                    "--max-insn" => {
                        i += 1;
                        if i < args.len() {
                            config.max_insn = args[i].parse().unwrap_or(config.max_insn);
                        }
                    }
                    "--max-states" => {
                        i += 1;
                        if i < args.len() {
                            config.max_states_per_pc =
                                args[i].parse().unwrap_or(config.max_states_per_pc);
                        }
                    }
                    "--log-interval" => {
                        i += 1;
                        if i < args.len() {
                            config.log_interval = args[i].parse().unwrap_or(config.log_interval);
                        }
                    }
                    "--debug-pc" => {
                        i += 1;
                        if i < args.len() {
                            config.debug_pc = args[i].parse().ok();
                        }
                    }
                    "--map-override" => {
                        if i + 1 < args.len() {
                            let val = &args[i + 1];
                            // Expected format: "map_name:1234"
                            match val.split_once(':') {
                                Some((name, size_str)) => {
                                    if let Ok(size) = size_str.parse::<u32>() {
                                        config.map_overrides.insert(name.to_string(), size);
                                    } else {
                                        eprintln!(
                                            "Warning: Invalid size in map override '{}'",
                                            val
                                        );
                                    }
                                }
                                None => {
                                    eprintln!(
                                        "Warning: Invalid map override format '{}'. Expected 'name:size'",
                                        val
                                    );
                                }
                            }
                            i += 1;
                        }
                    }
                    // --- Benchmark Filters ---
                    "--project" => {
                        i += 1;
                        if i < args.len() {
                            config.bench_project = Some(args[i].clone());
                        }
                    }
                    "--compiler" => {
                        i += 1;
                        if i < args.len() {
                            config.bench_compiler = Some(args[i].clone());
                        }
                    }
                    "--opt" => {
                        i += 1;
                        if i < args.len() {
                            config.bench_opt = Some(args[i].clone());
                        }
                    }
                    "--source" => {
                        i += 1;
                        if i < args.len() {
                            config.bench_source = Some(args[i].clone());
                        }
                    }
                    // --- Benchmark Input ---
                    "--input-list" => {
                        i += 1;
                        if i < args.len() {
                            config.bench_input_file = Some(args[i].clone());
                        }
                    }
                    _ => {
                        eprintln!("Warning: Unknown flag '{}'", arg);
                    }
                }
            } else {
                remaining.push(arg.clone());
            }

            i += 1;
        }

        (config, remaining)
    }

    /// Print help for configuration flags
    pub fn print_help() {
        eprintln!("Configuration flags:");
        eprintln!("  -q, --quiet          Verbosity 0: errors only");
        eprintln!("  -v, --verbose        Verbosity 2: trace execution");
        eprintln!("  -vv, --very-verbose  Verbosity 3: full debug output");
        eprintln!("  --skip-dbm           Skip DBM comparison in pruning (faster)");
        eprintln!(
            "  --use-widening       Use widening in pruning (DANGEROUS: might cause unsoundness)"
        );
        eprintln!("  --max-insn N         Max instructions to process (default: 1000000)");
        eprintln!("  --max-states N       Max states per PC for pruning (default: 8)");
        eprintln!("  --log-interval N     Heartbeat log interval (default: 100000)");
        eprintln!("  --debug-pc N         Force debug logging at specific PC");
        eprintln!("  --enable-path-trace  Enable path tracing for crash analysis");
        eprintln!("Benchmark Filters:");
        eprintln!("  --project NAME       Filter by project subdirectory (e.g. 'cilium')");
        eprintln!("  --compiler NAME      Filter by compiler (e.g. 'clang-16')");
        eprintln!("  --opt LEVEL          Filter by optimization (e.g. '-O1')");
        eprintln!("  --source NAME        Filter by source program name (e.g. 'bpf_host')");
        eprintln!("Benchmark Input:");
        eprintln!("  --input-list PATH    Path to file with list of ELF paths to analyze");
    }
}
