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
    
    /// Maximum states to keep per PC for pruning
    pub max_states_per_pc: usize,
    
    /// Log heartbeat interval
    pub log_interval: usize,
    
    /// Debug a specific PC (force verbose logging at this PC)
    pub debug_pc: Option<usize>,

    /// Enable path tracing for crash analysis
    pub enable_path_trace: bool,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self {
            verbosity: 1,
            max_insn: 1_000_000,
            skip_dbm_check: false,
            max_states_per_pc: 8,
            log_interval: 100_000,
            debug_pc: None,
            enable_path_trace: false,
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
                            config.max_states_per_pc = args[i].parse().unwrap_or(config.max_states_per_pc);
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
        eprintln!("  --max-insn N         Max instructions to process (default: 1000000)");
        eprintln!("  --max-states N       Max states per PC for pruning (default: 8)");
        eprintln!("  --log-interval N     Heartbeat log interval (default: 100000)");
        eprintln!("  --debug-pc N         Force debug logging at specific PC");
        eprintln!("  --enable-path-trace  Enable path tracing for crash analysis");
    }
}
