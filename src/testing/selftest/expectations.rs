//! Sidecar manifest that supplies expected verifier verdicts for vendored
//! corpus files which carry no `__success` / `__failure` annotations.
//!
//! ## Why a sidecar (not in-source)
//!
//! Two distinct upstream conventions coexist in our corpus:
//!
//!   * **bpf-selftests** (`tools/testing/selftests/bpf/progs/verifier_*.c`)
//!     — annotate verdicts in source via the `__success` / `__failure`
//!     macros from `bpf_misc.h`. The test_loader harness reads them at
//!     runtime. [`super::attrs::scrape`] extracts these.
//!
//!   * **struct_ops + sched_ext** (`tools/testing/selftests/bpf/progs/bpf_*.c`,
//!     `tools/testing/selftests/sched_ext/*.bpf.c`) — the BPF source files
//!     carry no per-program annotations. Verdicts are asserted by per-test
//!     C harnesses in `tools/testing/selftests/bpf/prog_tests/*.c` and
//!     `tools/testing/selftests/sched_ext/runner.c`.
//!
//! Modifying the second category in-place would break our verbatim-mirror
//! invariant. This manifest captures the same intent, with each entry
//! citing the upstream harness that justifies the verdict.
//!
//! ## Verdict-source precedence (consulted by [`super::runner::run_one`])
//!
//!   1. `__success` / `__failure` macros in source.
//!   2. This manifest (keyed by file basename).
//!   3. Otherwise: `Outcome::Skipped("no verdict source")`.
//!
//! ## Scope discipline
//!
//! Only files whose verdict the **verifier itself** can decide belong here.
//! Files whose kernel-side failure happens past the verifier — struct_ops
//! map registration, GPL gating, sched_ext runtime exit — should either be
//! removed from the corpus or marked `accept` (since the verifier accepts
//! them). The manifest's `note` field documents which category each entry
//! is in.

use serde::Deserialize;
use std::collections::HashMap;
use std::path::Path;
use std::sync::OnceLock;

/// Expected verifier verdict declared by the manifest.
#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Expect {
    Accept,
    Reject,
}

/// Per-program override inside a file entry. Used for files that mix
/// positive and negative progs (test-loader convention with `SEC("?...")`
/// + per-prog `bpf_program__set_autoload` toggling on the C-driver side —
/// see `project_remaining_skipped_analysis_*`). Lookup precedence:
///
///   1. `__success` / `__failure` macro on the prog (extracted by attrs::scrape)
///   2. file's `progs[<prog_name>]` per-prog override (this struct)
///   3. file-level `expect` default
///   4. otherwise `Outcome::Skipped("no verdict source")`
#[derive(Debug, Clone, Deserialize)]
pub struct ProgEntry {
    pub expect: Expect,
    #[serde(default)]
    pub note: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Entry {
    /// File-level default. Optional when `progs` is non-empty: a file may
    /// list per-prog overrides without any file-level fallback (un-overridden
    /// progs then fall through to `Outcome::Skipped`).
    #[serde(default)]
    pub expect: Option<Expect>,
    #[serde(default)]
    pub note: String,
    #[serde(default)]
    pub progs: HashMap<String, ProgEntry>,
}

#[derive(Debug, Clone, Deserialize)]
struct Manifest {
    files: HashMap<String, Entry>,
}

/// Default manifest path, resolved relative to the working directory the
/// runner is invoked from. Mirrors the convention used for
/// `selftests/baseline_v6.15.json`.
pub const DEFAULT_PATH: &str = "selftests/expectations.json";

fn load_default() -> HashMap<String, Entry> {
    let path = Path::new(DEFAULT_PATH);
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!(
                "[expectations] could not read {}: {} (continuing without manifest)",
                path.display(),
                e
            );
            return HashMap::new();
        }
    };
    match serde_json::from_slice::<Manifest>(&bytes) {
        Ok(m) => m.files,
        Err(e) => {
            eprintln!(
                "[expectations] failed to parse {}: {} (continuing without manifest)",
                path.display(),
                e
            );
            HashMap::new()
        }
    }
}

fn entries() -> &'static HashMap<String, Entry> {
    static CELL: OnceLock<HashMap<String, Entry>> = OnceLock::new();
    CELL.get_or_init(load_default)
}

/// Look up the manifest entry for a source file by basename. Returns
/// `None` if the file isn't listed (caller falls back to `Skipped`).
pub fn lookup(file_basename: &str) -> Option<Entry> {
    entries().get(file_basename).cloned()
}

/// Look up the verdict for a specific prog inside a file, applying the
/// per-prog override → file-level fallback precedence. Returns `None`
/// when the file is not listed, or is listed but has neither a matching
/// per-prog override nor a file-level `expect` (caller falls back to
/// `Outcome::Skipped`).
pub fn lookup_prog(file_basename: &str, prog_name: &str) -> Option<Expect> {
    let entry = entries().get(file_basename)?;
    if let Some(po) = entry.progs.get(prog_name) {
        return Some(po.expect);
    }
    entry.expect
}
