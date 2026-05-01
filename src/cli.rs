// src/cli.rs - clap-based CLI definitions and backward-compat argv rewriting.
//
// User-facing surface is three verbs: `elf`, `verify`, `pcc`. All
// corpus/benchmark/baseline/regression commands live under a hidden `dev`
// subcommand. Old top-level command names (e.g. `selftest-suite`,
// `prevail-benchmark`, `pcc-gen`) are translated to the new form by
// `rewrite_legacy_argv` before clap parses, so existing scripts/CI keep
// working without surfacing them in `--help`.

use crate::common::config::{DomainMode, VerifierConfig};
use clap::{Args, Parser, Subcommand, ValueEnum};

#[derive(Parser, Debug)]
#[command(
    name = "zovia",
    version,
    about = "eBPF zone verifier",
    disable_help_subcommand = true
)]
pub struct Cli {
    #[command(flatten)]
    pub global: GlobalOpts,

    #[command(subcommand)]
    pub cmd: Cmd,
}

// Verifier-tuning flags shared by every subcommand.
//
// All flags are `global = true` so they may appear before *or* after the
// subcommand name. Old scripts (`zovia -q --max-insn N selftest-suite …`)
// keep working unchanged.
#[derive(Args, Debug)]
pub struct GlobalOpts {
    /// Verbosity 0 (errors only)
    #[arg(short, long, global = true)]
    pub quiet: bool,
    /// Verbosity 2 (trace execution)
    #[arg(short, long, global = true)]
    pub verbose: bool,
    /// Verbosity 3 (full debug)
    #[arg(long = "very-verbose", global = true)]
    pub very_verbose: bool,

    /// Use kernel-style interval domain (also sets single-entry loops, disables bounded-loop detection)
    #[arg(long = "kernel-mode", alias = "interval", global = true)]
    pub kernel_mode: bool,
    /// Use zone domain (default; more precise)
    #[arg(long = "zone-mode", alias = "zone", global = true)]
    pub zone_mode: bool,

    #[arg(long, global = true)]
    pub skip_dbm: bool,
    #[arg(long, global = true)]
    pub use_widening: bool,
    #[arg(long, global = true)]
    pub enable_path_trace: bool,

    #[arg(long, global = true)]
    pub detect_bounded_loops: bool,
    #[arg(long = "no-detect-bounded-loops", global = true)]
    pub no_detect_bounded_loops: bool,
    #[arg(long, global = true)]
    pub single_entry_loops: bool,
    #[arg(long, global = true)]
    pub multi_entry_loops: bool,
    #[arg(long, global = true)]
    pub enable_private_stack: bool,
    #[arg(long, global = true)]
    pub disable_private_stack: bool,

    #[arg(long, global = true, value_name = "N")]
    pub max_insn: Option<usize>,
    #[arg(long, global = true, value_name = "N")]
    pub max_states: Option<usize>,
    #[arg(long, global = true, value_name = "N")]
    pub log_interval: Option<usize>,
    #[arg(long, global = true, value_name = "PC")]
    pub debug_pc: Option<usize>,

    /// Map size override `NAME:SIZE` (repeatable)
    #[arg(long = "map-override", global = true, value_name = "NAME:SIZE")]
    pub map_overrides: Vec<String>,

    // Benchmark filters (only meaningful for `dev bcf-benchmark` /
    // `dev prevail benchmark`). Kept global so old invocations still parse.
    #[arg(long, global = true, value_name = "NAME")]
    pub project: Option<String>,
    #[arg(long, global = true, value_name = "NAME")]
    pub compiler: Option<String>,
    #[arg(long, global = true, value_name = "LEVEL")]
    pub opt: Option<String>,
    #[arg(long, global = true, value_name = "NAME")]
    pub source: Option<String>,
    #[arg(long, global = true, value_name = "PATH")]
    pub input_list: Option<String>,
}

#[derive(Subcommand, Debug)]
pub enum Cmd {
    /// Inspect ELF / BTF contents (no verification)
    Elf(ElfArgs),

    /// Verify an eBPF program. Source is auto-detected by extension:
    /// `.o` (ELF object), `.c` (C source compiled via clang), `.json`
    /// (legacy test catalogue — requires `--test NAME` to pick a case;
    /// bare invocation lists tests).
    Verify(VerifyArgs),

    /// Proof-Carrying Code (PCC) certificate workflows
    Pcc {
        #[command(subcommand)]
        sub: PccCmd,
    },

    /// Internal corpus / benchmark / baseline harness commands.
    /// Not part of the user-facing surface; subject to change.
    #[command(hide = true)]
    Dev {
        #[command(subcommand)]
        sub: DevCmd,
    },
}

#[derive(Args, Debug)]
pub struct ElfArgs {
    pub path: String,

    /// Analyze a specific section
    #[arg(long, conflicts_with_all = ["func", "all", "struct_ops", "btf_func", "bindings"])]
    pub section: Option<String>,
    /// Analyze a specific function (looks up its containing section)
    #[arg(long, conflicts_with_all = ["section", "all", "struct_ops", "btf_func", "bindings"])]
    pub func: Option<String>,
    /// Analyze every section in the ELF
    #[arg(long, conflicts_with_all = ["section", "func", "struct_ops", "btf_func", "bindings"])]
    pub all: bool,

    /// Diagnostic: dump the struct_ops methods of STRUCT
    #[arg(long = "struct-ops", value_name = "STRUCT")]
    pub struct_ops: Option<String>,
    /// Diagnostic: print the BTF FUNC parameter list of FUNC
    #[arg(long = "btf-func", value_name = "FUNC")]
    pub btf_func: Option<String>,
    /// Diagnostic: dump struct_ops bindings recovered from .struct_ops sections
    #[arg(long)]
    pub bindings: bool,
}

#[derive(Args, Debug)]
pub struct VerifyArgs {
    /// Path to ELF (`.o`), source (`.c`), or legacy test catalogue (`.json`)
    pub path: String,

    /// (ELF) section to verify
    #[arg(long)]
    pub section: Option<String>,
    /// (ELF) function to verify
    #[arg(long)]
    pub func: Option<String>,

    /// (`.json`) test name; bare `verify foo.json` lists tests instead of running
    #[arg(long)]
    pub test: Option<String>,

    /// (`.c`) extra preprocessor defines, comma-separated
    #[arg(long)]
    pub defines: Option<String>,

    /// Force input kind when the extension is ambiguous or missing
    #[arg(long, value_enum)]
    pub kind: Option<InputKind>,
}

#[derive(ValueEnum, Clone, Copy, Debug)]
pub enum InputKind {
    Elf,
    C,
    Json,
}

#[derive(Subcommand, Debug)]
pub enum PccCmd {
    /// Generate a PCC certificate (zone mode enforced)
    Gen {
        json_file: String,
        #[arg(long)]
        test: String,
        /// Path to write the certificate JSON
        #[arg(long, value_name = "PATH")]
        out: Option<String>,
    },
    /// Verify with a pre-existing certificate (interval mode enforced)
    Check {
        json_file: String,
        #[arg(long)]
        test: String,
        #[arg(long, value_name = "PATH")]
        cert: String,
    },
    /// Generate then check in one invocation
    Cycle {
        json_file: String,
        #[arg(long)]
        test: String,
        #[arg(long, value_name = "PATH")]
        out: Option<String>,
    },
}

#[derive(Subcommand, Debug)]
pub enum DevCmd {
    /// Compile + verify a single upstream-style `.c` selftest
    SelftestFile {
        src: String,
        defines: Option<String>,
    },
    /// Compile + verify every `.c` selftest in `progs_dir`
    SelftestSuite { progs_dir: String },
    /// Sweep modern + legacy and write a baseline JSON
    SelftestBaselineWrite {
        progs_dir: String,
        legacy_json_dir: String,
        out: String,
    },
    /// Sweep upstream kernel selftests and write a baseline JSON
    SelftestBaselineWriteUpstream {
        upstream_root: String,
        out: String,
    },
    /// Diff a baseline against a fresh modern+legacy sweep
    SelftestBaselineCheck {
        progs_dir: String,
        legacy_json_dir: String,
        baseline: String,
    },
    /// Diff a baseline against a fresh modern-only sweep (fast)
    SelftestBaselineCheckModern {
        progs_dir: String,
        baseline: String,
    },
    /// Recursive ELF-corpus benchmark
    BcfBenchmark { dir: String },
    /// Legacy JSON-corpus selftest commands
    LegacySelftest {
        #[command(subcommand)]
        sub: LegacySelftestCmd,
    },
    /// Prevail-catalogue commands
    Prevail {
        #[command(subcommand)]
        sub: PrevailCmd,
    },
    /// Run the PCC regression manifest
    PccRegress {
        manifest: Option<String>,
    },
    /// Export ELF metadata for a corpus directory to JSON
    BenchmarkScan { dir: String, out: String },
}

#[derive(Subcommand, Debug)]
pub enum LegacySelftestCmd {
    List { json_file: String },
    Single { json_file: String, test: String },
    Run { json_file: String },
    Suite { json_dir: String },
}

#[derive(Subcommand, Debug)]
pub enum PrevailCmd {
    List { catalogue: String },
    Run { catalogue: String },
    Single { catalogue: String, test: String },
    Benchmark { dir: String },
}

// ============================================================
// Backward-compat: rewrite legacy argv into the new form
// ============================================================
//
// Scripts and CI still call `zovia selftest-suite ./progs`,
// `zovia prevail-benchmark ~/ebpf-samples`, etc. We map those to the new
// subcommand path *before* clap parses, so the old surface keeps working
// without bloating the help text. The mapping is mechanical and keeps
// positional arguments in their existing order — no value remoulding.

/// Translate legacy command names into the new `dev`/`elf`/`pcc` paths.
/// Operates on the slice of args *after* the binary name.
pub fn rewrite_legacy_argv(args: Vec<String>) -> Vec<String> {
    // Find the first positional that matches a known legacy command.
    // We skip flags and their values conservatively: anything starting with
    // `-` is a flag; if it's a known long-option that takes a value (no `=`),
    // skip the next arg too. Unknown flags: assume value-less. The set of
    // value-taking flags below mirrors GlobalOpts plus the historical ones.
    const VALUE_FLAGS: &[&str] = &[
        "--max-insn",
        "--max-states",
        "--log-interval",
        "--debug-pc",
        "--map-override",
        "--project",
        "--compiler",
        "--opt",
        "--source",
        "--input-list",
        "--generate-certificate",
        "--certificate-aided-analysis",
    ];

    // Locate the command position.
    let mut cmd_idx: Option<usize> = None;
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if a.starts_with('-') {
            if VALUE_FLAGS.iter().any(|f| *f == a) {
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        cmd_idx = Some(i);
        break;
    }

    let Some(cmd_idx) = cmd_idx else {
        return args;
    };

    let leading: Vec<String> = args[..cmd_idx].to_vec();
    let cmd = args[cmd_idx].clone();
    let rest: Vec<String> = args[cmd_idx + 1..].to_vec();

    // Translate. Each arm returns the new tail (subcommand path + args).
    let new_tail: Vec<String> = match cmd.as_str() {
        // ---- elf ----
        "elf-list" => prepend(&["elf"], &rest),
        "elf-analyze" | "elf-analyze-section" => match rest.split_first() {
            Some((path, tail)) if !tail.is_empty() => {
                let mut v = vec!["elf".into(), path.clone(), "--section".into(), tail[0].clone()];
                v.extend(tail[1..].iter().cloned());
                v
            }
            _ => prepend(&["elf"], &rest),
        },
        "elf-analyze-func" => match rest.split_first() {
            Some((path, tail)) if !tail.is_empty() => {
                let mut v = vec!["elf".into(), path.clone(), "--func".into(), tail[0].clone()];
                v.extend(tail[1..].iter().cloned());
                v
            }
            _ => prepend(&["elf"], &rest),
        },
        "elf-analyze-prog" => {
            let mut v = vec!["elf".into()];
            v.extend(rest);
            v.push("--all".into());
            v
        }
        "btf-dump-struct-ops" => match rest.split_first() {
            Some((path, tail)) if !tail.is_empty() => {
                let mut v = vec![
                    "elf".into(),
                    path.clone(),
                    "--struct-ops".into(),
                    tail[0].clone(),
                ];
                v.extend(tail[1..].iter().cloned());
                v
            }
            _ => prepend(&["elf"], &rest),
        },
        "btf-dump-func" => match rest.split_first() {
            Some((path, tail)) if !tail.is_empty() => {
                let mut v = vec![
                    "elf".into(),
                    path.clone(),
                    "--btf-func".into(),
                    tail[0].clone(),
                ];
                v.extend(tail[1..].iter().cloned());
                v
            }
            _ => prepend(&["elf"], &rest),
        },
        "struct-ops-bindings" => {
            let mut v = vec!["elf".into()];
            v.extend(rest);
            v.push("--bindings".into());
            v
        }

        // ---- pcc ----
        "pcc-gen" => translate_pcc(&["pcc", "gen"], &rest, /*needs_cert*/ false),
        "pcc-check" => translate_pcc(&["pcc", "check"], &rest, /*needs_cert*/ true),
        "pcc-cycle" => translate_pcc(&["pcc", "cycle"], &rest, /*needs_cert*/ false),

        // ---- dev: selftest ----
        "selftest-file" => prepend(&["dev", "selftest-file"], &rest),
        "selftest-suite" => prepend(&["dev", "selftest-suite"], &rest),
        "selftest-baseline-write" => prepend(&["dev", "selftest-baseline-write"], &rest),
        "selftest-baseline-write-upstream" => {
            // The old 3-arg form takes <progs_dir> <upstream_root> <out> and
            // the modern 2-arg form takes <upstream_root> <out>. Both are
            // passed straight through; the handler still accepts the old
            // form for back-compat with a deprecation note.
            prepend(&["dev", "selftest-baseline-write-upstream"], &rest)
        }
        "selftest-baseline-check" => prepend(&["dev", "selftest-baseline-check"], &rest),
        "selftest-baseline-check-modern" => {
            prepend(&["dev", "selftest-baseline-check-modern"], &rest)
        }

        // ---- dev: misc ----
        "bcf-benchmark" | "elf-analyze-benchmark" => prepend(&["dev", "bcf-benchmark"], &rest),
        "benchmark-scan" => prepend(&["dev", "benchmark-scan"], &rest),
        "pcc-regress" => prepend(&["dev", "pcc-regress"], &rest),

        // ---- dev: legacy-selftest ----
        "legacy-selftest-list" => prepend(&["dev", "legacy-selftest", "list"], &rest),
        "legacy-selftest-single" => prepend(&["dev", "legacy-selftest", "single"], &rest),
        "legacy-selftest-run" => prepend(&["dev", "legacy-selftest", "run"], &rest),
        "legacy-selftest-suite" => prepend(&["dev", "legacy-selftest", "suite"], &rest),

        // ---- dev: prevail ----
        "prevail-list" => prepend(&["dev", "prevail", "list"], &rest),
        "prevail-run" => prepend(&["dev", "prevail", "run"], &rest),
        "prevail-single" => prepend(&["dev", "prevail", "single"], &rest),
        "prevail-benchmark" => prepend(&["dev", "prevail", "benchmark"], &rest),

        // Already-new command (or unknown — let clap report it).
        _ => {
            let mut v = vec![cmd];
            v.extend(rest);
            v
        }
    };

    let mut out = leading;
    out.extend(new_tail);
    out
}

fn prepend(prefix: &[&str], rest: &[String]) -> Vec<String> {
    let mut v: Vec<String> = prefix.iter().map(|s| s.to_string()).collect();
    v.extend(rest.iter().cloned());
    v
}

/// Translate legacy `pcc-{gen,check,cycle} <json> <test> [extra]` into the
/// new flag-based form. `needs_cert` distinguishes `pcc-check`'s third
/// positional (the cert path) from `pcc-{gen,cycle}`'s optional cert-out.
fn translate_pcc(prefix: &[&str], rest: &[String], needs_cert: bool) -> Vec<String> {
    let mut v: Vec<String> = prefix.iter().map(|s| s.to_string()).collect();
    if rest.is_empty() {
        return v;
    }
    v.push(rest[0].clone()); // json_file
    if rest.len() >= 2 {
        v.push("--test".into());
        v.push(rest[1].clone());
    }
    if rest.len() >= 3 {
        v.push(if needs_cert { "--cert".into() } else { "--out".into() });
        v.push(rest[2].clone());
    }
    // Anything past the third positional was undefined in the old form;
    // forward it so clap can complain rather than silently dropping it.
    for x in rest.iter().skip(3) {
        v.push(x.clone());
    }
    v
}

// ============================================================
// Build a VerifierConfig from parsed clap flags.
// ============================================================

impl GlobalOpts {
    pub fn into_verifier_config(self) -> VerifierConfig {
        let mut c = VerifierConfig::default();

        // Verbosity: highest wins (vv > v > q > default).
        if self.very_verbose {
            c.verbosity = 3;
        } else if self.verbose {
            c.verbosity = 2;
        } else if self.quiet {
            c.verbosity = 0;
        }

        // Domain mode. `--kernel-mode` sets a triplet (interval domain,
        // single-entry loops on, bounded-loop detection off) to mirror the
        // historical behavior. `--zone-mode` only flips the domain back —
        // loop flags must be set explicitly if needed.
        if self.kernel_mode {
            c.domain_mode = DomainMode::Interval;
            c.detect_bounded_loops = false;
            c.require_single_loop_entry = true;
        }
        if self.zone_mode {
            c.domain_mode = DomainMode::Zone;
        }

        if self.skip_dbm {
            c.skip_dbm_check = true;
        }
        if self.use_widening {
            c.use_widening = true;
        }
        if self.enable_path_trace {
            c.enable_path_trace = true;
        }

        if self.detect_bounded_loops {
            c.detect_bounded_loops = true;
        }
        if self.no_detect_bounded_loops {
            c.detect_bounded_loops = false;
        }
        if self.single_entry_loops {
            c.require_single_loop_entry = true;
        }
        if self.multi_entry_loops {
            c.require_single_loop_entry = false;
        }
        if self.enable_private_stack {
            c.enable_private_stack = true;
        }
        if self.disable_private_stack {
            c.enable_private_stack = false;
        }

        if let Some(n) = self.max_insn {
            c.max_insn = n;
        }
        if let Some(n) = self.max_states {
            c.max_states_per_pc = n;
        }
        if let Some(n) = self.log_interval {
            c.log_interval = n;
        }
        if let Some(pc) = self.debug_pc {
            c.debug_pc = Some(pc);
        }

        for spec in &self.map_overrides {
            match spec.split_once(':') {
                Some((name, size_str)) => match size_str.parse::<u32>() {
                    Ok(size) => {
                        c.map_overrides.insert(name.to_string(), size);
                    }
                    Err(_) => eprintln!("Warning: invalid size in map override '{spec}'"),
                },
                None => eprintln!(
                    "Warning: invalid map override format '{spec}'. Expected 'name:size'"
                ),
            }
        }

        c.bench_project = self.project;
        c.bench_compiler = self.compiler;
        c.bench_opt = self.opt;
        c.bench_source = self.source;
        c.bench_input_file = self.input_list;

        c
    }
}
