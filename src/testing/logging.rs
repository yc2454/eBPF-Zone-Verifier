use log::{Level, LevelFilter, Log, Metadata, Record};
use std::collections::VecDeque;
use std::sync::{Mutex, Once, RwLock}; // RwLock for config (read often, write once)

// --- 1. Configuration Structures ---

#[derive(Debug, Clone, Default)]
pub struct FilterConfig {
    /// Only log steps within this PC range (Inclusive)
    pub pc_range: Option<std::ops::RangeInclusive<usize>>,
    /// Only log steps that touch these registers (by index, e.g. 0 for R0)
    pub interesting_regs: Vec<u8>,
}

impl FilterConfig {
    // A helper to decide if a log line is "interesting"
    fn allows(&self, log_msg: &str) -> bool {
        // 1. Check PC Filter
        if let Some(range) = &self.pc_range {
            // Scan for tag "|PC:123|"
            if let Some(start) = log_msg.find("|PC:") {
                let rest = &log_msg[start + 4..];
                if let Some(end) = rest.find('|')
                    && let Ok(pc) = rest[..end].parse::<usize>()
                    && !range.contains(&pc)
                {
                    return false;
                }
            }
        }

        // 2. Check Register Filter
        if !self.interesting_regs.is_empty() {
            // Scan for tag "|REG:R0|" or "|REG:R1,R2|"
            // Simple heuristic: does the string contain "R{id}"?
            let mut found = false;
            for reg in &self.interesting_regs {
                // Look for "R0", "R1", etc. inside the metadata section
                // We rely on the analysis formatting "Regs:[R0, R1]" or similar.
                let token = format!("R{}", reg);
                if log_msg.contains(&token) {
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }

        true
    }
}

// --- 2. The Smart Logger ---

static INSTANCE: VerifierLogger = VerifierLogger {
    buffer: Mutex::new(VecDeque::new()),
    config: RwLock::new(FilterConfig {
        pc_range: None,
        interesting_regs: vec![],
    }),
};

static INIT: Once = Once::new();

pub struct VerifierLogger {
    buffer: Mutex<VecDeque<String>>,
    config: RwLock<FilterConfig>, // Config is simpler to guard with RwLock
}

impl VerifierLogger {
    pub fn init(verbosity: u8) {
        // Map u8 verbosity to LevelFilter
        let level = match verbosity {
            0 => LevelFilter::Warn,  // Quiet (Errors/Warns only)
            1 => LevelFilter::Info,  // Default (Summaries)
            2 => LevelFilter::Debug, // Detailed
            _ => LevelFilter::Trace, // Everything
        };
        INIT.call_once(|| {
            log::set_logger(&INSTANCE)
                .map(|()| log::set_max_level(level))
                .expect("Failed to initialize logger");
        });
    }

    /// Update the filters at runtime (call this from main)
    pub fn set_config(config: FilterConfig) {
        let mut w = INSTANCE.config.write().unwrap();
        *w = config;
    }

    fn dump_buffer(&self) {
        let buffer = self.buffer.lock().unwrap();
        println!(
            "\n=== CRASH TRACE (Last {} Relevant Steps) ===",
            buffer.len()
        );
        for line in buffer.iter() {
            print!("{}", line);
        }
        println!("==============================================\n");
    }
}

impl Log for VerifierLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Trace
    }

    fn log(&self, record: &Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        if record.target() == "analysis" {
            let msg_str = format!("{}", record.args());

            // --- FILTERING LOGIC ---
            // Scope the read lock
            {
                let config = self.config.read().unwrap();
                if !config.allows(&msg_str) {
                    // If filter rejects it, don't buffer it!
                    // BUT, if it's an ERROR, always let it through to trigger the dump.
                    if record.level() != Level::Error {
                        return;
                    }
                }
            }

            // --- BUFFERING LOGIC ---
            let mut buffer = self.buffer.lock().unwrap();

            // Keep last 100 *matching* lines
            if buffer.len() >= 100 {
                buffer.pop_front();
            }
            buffer.push_back(format!("[Analysis] {}\n", msg_str));

            // --- TRIGGER LOGIC ---
            if record.level() == Level::Error {
                drop(buffer);
                self.dump_buffer();
                println!("!!! ANALYSIS FAILURE: {} !!!", record.args());
            }
        } else {
            // General App Logs
            println!("[{}] {}", record.level(), record.args());
        }
    }

    fn flush(&self) {}
}
