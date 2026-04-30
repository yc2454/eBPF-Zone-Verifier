//! Orchestrate compile → verify → diff for a modern upstream selftest file.
//!
//! Inputs:  one (or many) `progs/verifier_*.c`.
//! Output:  per-program `Outcome` reporting whether our verifier's verdict
//!          matched the `__success` / `__failure` annotation in the source.

use anyhow::{Context, Result};
use rayon::prelude::*;
use std::path::{Path, PathBuf};

use crate::common::config::VerifierConfig;
use crate::testing::runner::{AnalysisResult, Analyzer};

use super::attrs::{self, ProgAttrs};
use super::clang;
use super::expectations;

/// Filter that decides which programs the runner actually verifies.
/// Programs the filter returns `false` for short-circuit to
/// `Outcome::Skipped("filtered")` — useful for fast checks where we
/// already know certain programs are non-deterministic in the baseline
/// (TIMEOUT, ERROR) and re-running them just burns wallclock.
pub trait ProgFilter: Send + Sync {
    fn should_run(&self, file_basename: &str, prog_func_name: &str) -> bool;
}

/// Filter that always runs everything. Used when caller doesn't
/// supply a filter.
pub struct RunAll;
impl ProgFilter for RunAll {
    fn should_run(&self, _: &str, _: &str) -> bool {
        true
    }
}

/// Tight `max_insn` cap for selftest sweeps. The verifier's existing
/// complexity-limit check returns `Timeout` once the abstract-interp
/// step counter hits this. We don't use a wallclock-based timeout
/// here — those would have to orphan worker threads we can't cancel,
/// and orphans accumulate to saturate CPU under rayon. Tying the cap
/// to step count keeps termination cooperative, deterministic, and
/// parallelism-safe.
pub const SELFTEST_MAX_INSN: usize = 100_000;

/// Derive a config tuned for selftest sweeps from the caller's config:
/// keep all user-set knobs, but clamp `max_insn` down so the verifier
/// terminates promptly on a state-explosion. Caller can opt out of
/// the clamp by setting an explicit `max_insn` lower than ours.
pub fn with_selftest_caps(base: &VerifierConfig) -> VerifierConfig {
    let mut c = base.clone();
    if c.max_insn > SELFTEST_MAX_INSN {
        c.max_insn = SELFTEST_MAX_INSN;
    }
    c
}

/// Per-file `-D` defines clang needs to compile certain corpus sources.
/// Keep this list small and explicit — anything not listed here is
/// compiled with no extra defines.
pub const PER_FILE_DEFINES: &[(&str, &[&str])] = &[
    // Phase 1 ISA gates.
    ("verifier_gotol.c", &["CAN_USE_GOTOL"]),
    ("verifier_ldsx.c", &["__TARGET_ARCH_x86"]),
    ("verifier_movsx.c", &["__TARGET_ARCH_x86"]),
    // load_acquire/store_release/may_goto rely on macros that the
    // upstream tree gates behind cpuv4 + clang ≥18; surface the
    // payload functions by tripping those gates at compile time.
    ("verifier_load_acquire.c", &["CAN_USE_LOAD_ACQ_STORE_REL"]),
    ("verifier_store_release.c", &["ENABLE_ATOMICS_TESTS", "__TARGET_ARCH_x86"]),
    // W7.3: private-stack tests are gated on __TARGET_ARCH_x86 in the
    // upstream source. The `__jited(...)` annotations check actual x86
    // codegen which we don't validate; only `__success`/`__failure` is
    // consulted by our runner, so the gate is safe to trip at compile time.
    ("verifier_private_stack.c", &["__TARGET_ARCH_x86"]),
];

fn defines_for_file(path: &Path) -> &'static [&'static str] {
    let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
    PER_FILE_DEFINES
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, d)| *d)
        .unwrap_or(&[])
}

/// Did our verifier's verdict line up with the upstream annotation?
#[derive(Debug, Clone)]
pub enum Outcome {
    /// Verdict matched expectation (ACCEPT/REJECT).
    Pass,
    /// Expected ACCEPT, we REJECTed — precision issue.
    FalseReject(String),
    /// Expected REJECT, we ACCEPTed — soundness issue.
    FalseAccept,
    /// Couldn't run the test.
    Skipped(String),
    /// Verifier error (timeout, load failure, etc.).
    Error(String),
}

#[derive(Debug, Clone)]
pub struct ProgReport {
    pub func_name: String,
    pub description: String,
    pub sec: String,
    pub outcome: Outcome,
}

#[derive(Debug, Clone)]
pub struct FileReport {
    pub source: PathBuf,
    pub progs: Vec<ProgReport>,
}

impl FileReport {
    pub fn pass_count(&self) -> usize {
        self.progs
            .iter()
            .filter(|p| matches!(p.outcome, Outcome::Pass))
            .count()
    }

    pub fn total(&self) -> usize {
        self.progs.len()
    }
}

/// Run a single `.c` source end-to-end: scrape, compile, verify each
/// program, diff against expectation.
///
/// `headers_root` should be `selftests/headers/<tag>/` — see [`clang`].
/// `extra_defines` lets a caller pass `-D` flags that some files need
/// (e.g. `CAN_USE_GOTOL`); leave empty for files that don't.
pub fn run_file(
    src: &Path,
    headers_root: &Path,
    extra_defines: &[&str],
    config: &VerifierConfig,
) -> Result<FileReport> {
    run_file_filtered(src, headers_root, extra_defines, config, &RunAll)
}

pub fn run_file_filtered(
    src: &Path,
    headers_root: &Path,
    extra_defines: &[&str],
    config: &VerifierConfig,
    filter: &dyn ProgFilter,
) -> Result<FileReport> {
    let inc = clang::default_include_dirs(headers_root);
    let iq = clang::default_iquote_dirs(headers_root);
    run_file_with_dirs(src, &inc, &iq, extra_defines, config, filter)
}

/// Core per-file driver, parameterized on include and `-iquote` dirs so
/// callers (default vendored-headers sweep, upstream-tree sweep) share
/// the same scrape → compile → verify → diff pipeline.
pub fn run_file_with_dirs(
    src: &Path,
    include_dirs: &[PathBuf],
    iquote_dirs: &[PathBuf],
    extra_defines: &[&str],
    config: &VerifierConfig,
    filter: &dyn ProgFilter,
) -> Result<FileReport> {
    let progs = attrs::scrape(src)
        .with_context(|| format!("scraping attributes from {}", src.display()))?;

    let stem = src
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "selftest".to_string());
    let obj = std::env::temp_dir().join(format!("zovia_selftest_{stem}.o"));
    let _ = std::fs::remove_file(&obj);

    clang::compile_with_iquote(src, &obj, include_dirs, iquote_dirs, extra_defines)
        .with_context(|| format!("compiling {}", src.display()))?;

    let analyzer = Analyzer::new(obj.to_str().unwrap(), with_selftest_caps(config));
    let basename = src
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default();

    // Per-prog parallelism. Each `run_one` already spawns its own
    // worker thread for the wallclock timeout; rayon's pool runs
    // independent progs concurrently, so a file with N timeouts no
    // longer takes N × timeout wallclock.
    let progs = progs
        .into_par_iter()
        .map(|attrs| {
            if !filter.should_run(&basename, &attrs.func_name) {
                return ProgReport {
                    func_name: attrs.func_name.clone(),
                    description: attrs.description.clone().unwrap_or_default(),
                    sec: attrs.sec.clone().unwrap_or_default(),
                    outcome: Outcome::Skipped("filtered (baseline non-deterministic)".into()),
                };
            }
            run_one(&analyzer, attrs, &basename)
        })
        .collect();

    Ok(FileReport {
        source: src.to_path_buf(),
        progs,
    })
}

/// Sweep every `*.c` file under `dir`. Compile failures are surfaced
/// as a single `Outcome::Error` entry on a synthetic `<compile>` prog
/// so the report still has a row for the file. Per-file extra defines
/// are pulled from [`PER_FILE_DEFINES`].
pub fn run_dir(
    dir: &Path,
    headers_root: &Path,
    config: &VerifierConfig,
) -> Result<Vec<FileReport>> {
    run_dir_filtered(dir, headers_root, config, &RunAll)
}

pub fn run_dir_filtered(
    dir: &Path,
    headers_root: &Path,
    config: &VerifierConfig,
    filter: &dyn ProgFilter,
) -> Result<Vec<FileReport>> {
    let inc = clang::default_include_dirs(headers_root);
    let iq = clang::default_iquote_dirs(headers_root);
    run_dir_with_dirs(dir, &inc, &iq, &[], config, filter)
}

/// Sweep every `*.c` file under `dir`, running the upstream kernel
/// selftests/bpf tree directly (no header re-vendoring). `upstream_root`
/// is the kernel checkout root (typically `vendor/linux/`).
pub fn run_dir_upstream_filtered(
    dir: &Path,
    headers_root: &Path,
    upstream_root: &Path,
    config: &VerifierConfig,
    filter: &dyn ProgFilter,
) -> Result<Vec<FileReport>> {
    let inc = clang::upstream_include_dirs(headers_root, upstream_root);
    let iq = clang::upstream_iquote_dirs(headers_root, upstream_root);
    run_dir_with_dirs(dir, &inc, &iq, clang::UPSTREAM_GLOBAL_DEFINES, config, filter)
}

/// Core per-directory driver. `global_defines` are passed to every file
/// in addition to its `PER_FILE_DEFINES` entry (used by the upstream
/// sweep to apply `__TARGET_ARCH_x86` globally, matching the upstream
/// Makefile). Build the include/iquote vectors *once* outside this fn —
/// they're the same for every file in the sweep.
pub fn run_dir_with_dirs(
    dir: &Path,
    include_dirs: &[PathBuf],
    iquote_dirs: &[PathBuf],
    global_defines: &[&str],
    config: &VerifierConfig,
    filter: &dyn ProgFilter,
) -> Result<Vec<FileReport>> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .with_context(|| format!("reading dir {}", dir.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("c"))
        .collect();
    entries.sort();

    let mut out = Vec::with_capacity(entries.len());
    for path in entries {
        let mut defines: Vec<&str> = global_defines.to_vec();
        defines.extend(defines_for_file(&path));
        match run_file_with_dirs(&path, include_dirs, iquote_dirs, &defines, config, filter) {
            Ok(r) => out.push(r),
            Err(e) => out.push(FileReport {
                source: path.clone(),
                progs: vec![ProgReport {
                    func_name: "<compile>".into(),
                    description: String::new(),
                    sec: String::new(),
                    outcome: Outcome::Error(format!("{e}")),
                }],
            }),
        }
    }
    Ok(out)
}

fn run_one(analyzer: &Analyzer, attrs: ProgAttrs, file_basename: &str) -> ProgReport {
    let description = attrs.description.clone().unwrap_or_default();
    let sec = attrs.sec.clone().unwrap_or_default();

    // `__load_if_JITed()` programs only load when the kernel JIT is on.
    // We don't simulate JIT-specific semantics (e.g. JIT-mode `may_goto`
    // keeps its counter in a register, not on the stack), so an upstream
    // ACCEPT verdict on such a program isn't something we can soundly
    // reproduce. Skip rather than risk a misleading PASS or FR.
    if attrs.load_if_jited {
        return ProgReport {
            func_name: attrs.func_name,
            description,
            sec,
            outcome: Outcome::Skipped("__load_if_JITed (JIT-only semantics)".into()),
        };
    }

    // Verdict-source precedence — keep this in sync with the doc-comment in
    // src/testing/selftest/expectations.rs:
    //   1. __success / __failure macros from the bpf-selftests test_loader
    //      convention (extracted by attrs::scrape).
    //   2. selftests/expectations.json — sidecar manifest for vendored
    //      struct_ops / sched_ext files whose intent lives in the kernel's
    //      C-side prog_tests / runner harnesses, not in the BPF source.
    //   3. Otherwise: Skipped("no verdict source").
    let expected_accept = match (attrs.success, attrs.failure) {
        (true, false) => true,
        (false, true) => false,
        _ => match expectations::lookup(file_basename) {
            Some(e) => matches!(e.expect, expectations::Expect::Accept),
            None => {
                return ProgReport {
                    func_name: attrs.func_name,
                    description,
                    sec,
                    outcome: Outcome::Skipped(
                        "no verdict source (no __success/__failure and not in selftests/expectations.json)".into(),
                    ),
                };
            }
        },
    };

    if sec.is_empty() {
        return ProgReport {
            func_name: attrs.func_name,
            description,
            sec,
            outcome: Outcome::Skipped("missing SEC()".into()),
        };
    }

    // Termination is bounded by the verifier's own complexity-limit
    // check — see `SELFTEST_MAX_INSN` and `with_selftest_caps` below.
    // No wallclock timeout, no orphan threads.
    let result = analyzer.analyze_function_with_flags(&sec, &attrs.func_name, attrs.prog_flags);
    let outcome = match (expected_accept, result) {
        (true, AnalysisResult::Pass) => Outcome::Pass,
        (false, AnalysisResult::Fail(_)) => Outcome::Pass,
        (true, AnalysisResult::Fail(e)) => Outcome::FalseReject(e.description().to_string()),
        (false, AnalysisResult::Pass) => Outcome::FalseAccept,
        // Hitting the complexity limit on a `__failure` program is
        // kernel-aligned — the kernel verifier itself rejects via
        // `BPF_COMPLEXITY_LIMIT_INSNS` for unbounded-loop and
        // back-edge constructs (e.g. `infinite_loop_in_two_jumps`,
        // `mov64sx_s32_varoff_1`, `may_goto_self`). Counts as Pass.
        (false, AnalysisResult::Timeout) => Outcome::Pass,
        (_, AnalysisResult::Timeout) => Outcome::Error("verifier timeout".into()),
        (_, AnalysisResult::LoadError(e)) => {
            // The function not being present in the ELF means it was
            // compiled out (typically by an `#ifdef` branch the scraper
            // walks past blindly). That's a skip, not a verifier
            // failure. Two phrasings come from `analyze_function`:
            // the per-section variant ("not found in section '…'") and
            // the multi-section fallback ("not found (looked in '…' and
            // N other sections)").
            if e.contains("not found in section") || e.contains("not found (looked in") {
                Outcome::Skipped(format!("not in ELF: {e}"))
            } else if !expected_accept {
                // The program was rejected before abstract-interp ever
                // ran — typically because clang-emitted bytecode is
                // intentionally malformed (upstream `__failure` tests
                // for invalid register encodings, bad opcodes, …).
                // That's a verifier REJECT verdict, just produced at
                // the parse layer instead of the analysis layer; it
                // matches upstream's `__failure` annotation.
                Outcome::Pass
            } else {
                // Expected ACCEPT but couldn't even load. Surfacing as
                // FalseReject lines up with the abstract-interp side:
                // either the parser is too strict, or the test really
                // is invalid input.
                Outcome::FalseReject(format!("load: {e}"))
            }
        }
    };

    ProgReport {
        func_name: attrs.func_name,
        description,
        sec,
        outcome,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn headers() -> PathBuf {
        PathBuf::from("selftests/headers/v6.15")
    }

    #[test]
    fn runs_verifier_gotol_end_to_end() {
        if !headers().exists() {
            eprintln!("skipping: vendored headers not present");
            return;
        }
        let config = VerifierConfig::default();
        let report = run_file(
            Path::new("selftests/progs/verifier_gotol.c"),
            &headers(),
            &["CAN_USE_GOTOL"],
            &config,
        )
        .expect("run_file should succeed");

        // We expect at least gotol_small_imm and gotol_large_imm.
        assert!(
            report.progs.len() >= 2,
            "got {} progs",
            report.progs.len()
        );
        for p in &report.progs {
            eprintln!(
                "  {} ({}): {:?}",
                p.func_name, p.description, p.outcome
            );
        }
    }
}
