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

#[derive(Debug, Clone, Deserialize)]
pub struct Entry {
    pub expect: Expect,
    #[serde(default)]
    pub note: String,
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
