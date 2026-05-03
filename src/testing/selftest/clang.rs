//! Drive `clang -target bpf` to compile an upstream `verifier_*.c` source
//! into a BPF ELF object that the rest of the pipeline (existing ELF
//! parser + verifier) can read directly.
//!
//! Headers are vendored under `selftests/headers/<tag>/` (see that
//! directory's README); we point clang at them via `-I` flags so the
//! pipeline doesn't depend on a system libbpf or kernel UAPI install.

use anyhow::{Context, Result, anyhow};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Default kernel-tag subdirectory under `selftests/headers/`. Bump in
/// lockstep with `selftests/SOURCE_TAG` and the vendored header refresh.
pub const DEFAULT_HEADERS_TAG: &str = "v6.15";

/// Resolve the clang binary to invoke. Honors `$BPF_CLANG` for
/// override; otherwise tries Homebrew's path on macOS, then `clang` on
/// `$PATH`.
fn resolve_clang() -> String {
    if let Ok(p) = std::env::var("BPF_CLANG") {
        return p;
    }
    let homebrew = "/opt/homebrew/opt/llvm/bin/clang";
    if Path::new(homebrew).exists() {
        return homebrew.to_string();
    }
    "clang".to_string()
}

/// Default vendored-header include dirs for the given tag. Order
/// matters: stubs (for libc bits clang-bpf doesn't ship) shadow real
/// kernel UAPI headers when both define the same name (e.g. `errno.h`),
/// so stubs come first.
pub fn default_include_dirs(headers_root: &Path) -> Vec<PathBuf> {
    vec![
        headers_root.join("_stubs"),
        headers_root.to_path_buf(),
        headers_root.join("bpf"),
    ]
}

/// Default `-iquote` directories for the given tag. These exist solely
/// to redirect `#include "…/relative/path.h"` lines that the upstream
/// kernel selftests use to reach into `tools/include/`. We can't
/// recreate that tree at the path their relative includes expect, so
/// we register a deep dummy directory under `_quotes/` and place the
/// stub headers at the resolved location. clang searches each
/// `-iquote` dir for a literal `"x/y/z.h"` include, so a stub at
/// `_quotes/include/linux/filter.h` resolves the upstream
/// `"../../../include/linux/filter.h"` when the iquote root is
/// `_quotes/q1/q2/q3` (three `..` ascents land back at `_quotes/`).
pub fn default_iquote_dirs(headers_root: &Path) -> Vec<PathBuf> {
    vec![headers_root.join("_quotes/q1/q2/q3")]
}

/// `-D` macros the upstream selftests Makefile sets globally for every
/// BPF prog. Without these, ~25 tracing programs refuse to compile
/// (`#error "Must specify a BPF target arch via __TARGET_ARCH_xxx"`).
/// Applied on top of any `PER_FILE_DEFINES` entry for an individual file.
pub const UPSTREAM_GLOBAL_DEFINES: &[&str] = &["__TARGET_ARCH_x86"];

/// Include dirs for sweeping the *upstream* selftests tree directly
/// (no re-vendoring). Layers our hand-written stubs on top of the
/// in-tree headers so the libc shims still win where both define the
/// same symbol. `upstream_root` is the root of a checked-out kernel
/// (typically `vendor/linux/`).
///
/// Order:
///   1. our `_stubs/`            — libc shims
///   2. `selftests/headers/<tag>/` + `bpf/` — our pinned vendored copies
///                                  of the most-used selftest/uapi headers
///   3. upstream `tools/lib/`    — resolves `<bpf/bpf_endian.h>` etc.
///   4. upstream `tools/lib/bpf`
///   5. upstream `tools/include` + `tools/include/uapi`
///   6. upstream `include/uapi`  — kernel-internal uapi (`linux/libc-compat.h`, …)
///   7. upstream `arch/x86/include/uapi` — `<asm/byteorder.h>`, `<asm/ptrace.h>`
///   8. upstream `tools/testing/selftests/bpf` + `progs` — sibling helper headers
pub fn upstream_include_dirs(headers_root: &Path, upstream_root: &Path) -> Vec<PathBuf> {
    let mut v = default_include_dirs(headers_root);
    v.extend([
        upstream_root.join("tools/lib"),
        upstream_root.join("tools/lib/bpf"),
        upstream_root.join("tools/include"),
        upstream_root.join("tools/include/uapi"),
        upstream_root.join("include/uapi"),
        upstream_root.join("arch/x86/include/uapi"),
        upstream_root.join("tools/testing/selftests/bpf"),
        upstream_root.join("tools/testing/selftests/bpf/progs"),
    ]);
    v
}

/// `-iquote` dirs for upstream sweeps: the existing dummy depth-3 dir
/// that handles `"../../../include/linux/filter.h"`-style ascents, plus
/// the selftests/bpf dir for sibling quoted includes.
pub fn upstream_iquote_dirs(headers_root: &Path, upstream_root: &Path) -> Vec<PathBuf> {
    let mut v = default_iquote_dirs(headers_root);
    v.push(upstream_root.join("tools/testing/selftests/bpf"));
    v
}

/// Returns clang's resource-dir `include` path (where compiler intrinsic
/// headers live: `stddef.h`, `stdarg.h`, `stdint.h`, …). We need to
/// surface these as `-isystem` rather than rely on the host's `/usr/include`
/// because `-target bpf` doesn't accept macOS or Linux libc headers.
fn clang_resource_include(clang: &str) -> Option<PathBuf> {
    let out = Command::new(clang)
        .arg("-print-resource-dir")
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let dir = String::from_utf8(out.stdout).ok()?.trim().to_string();
    Some(PathBuf::from(dir).join("include"))
}

/// Compile a `.c` source into a BPF ELF object. `out_path` is the
/// destination `.o` file; caller chooses where it lives (typically a
/// temp dir).
///
/// `extra_defines` lets a caller pass `-D` macros — e.g. `CAN_USE_GOTOL`
/// for files gated on cpuv4 features.
pub fn compile<P: AsRef<Path>, Q: AsRef<Path>>(
    src: P,
    out_path: Q,
    include_dirs: &[PathBuf],
    extra_defines: &[&str],
) -> Result<()> {
    compile_with_iquote(src, out_path, include_dirs, &[], extra_defines)
}

pub fn compile_with_iquote<P: AsRef<Path>, Q: AsRef<Path>>(
    src: P,
    out_path: Q,
    include_dirs: &[PathBuf],
    iquote_dirs: &[PathBuf],
    extra_defines: &[&str],
) -> Result<()> {
    let src = src.as_ref();
    let out = out_path.as_ref();
    let clang = resolve_clang();

    let mut cmd = Command::new(&clang);
    // `-nostdinc` blocks the host system include search (macOS SDK,
    // /usr/include) which doesn't grok `-target bpf`. We add back only
    // clang's own resource-dir intrinsics (`-isystem`) plus the
    // vendored / stub dirs (`-I`).
    cmd.args(["-target", "bpf", "-O2", "-g", "-Wall", "-nostdinc", "-c"]);
    if let Some(rdir) = clang_resource_include(&clang) {
        cmd.arg("-isystem").arg(rdir);
    }
    for inc in include_dirs {
        cmd.arg("-I").arg(inc);
    }
    for q in iquote_dirs {
        cmd.arg("-iquote").arg(q);
    }
    for d in extra_defines {
        cmd.arg(format!("-D{d}"));
    }
    cmd.arg(src).arg("-o").arg(out);

    let output = cmd
        .output()
        .with_context(|| format!("invoking {clang} (set $BPF_CLANG to override)"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(anyhow!(
            "clang failed compiling {}: {}",
            src.display(),
            stderr.trim()
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn project_headers_dir() -> PathBuf {
        PathBuf::from("selftests/headers").join(DEFAULT_HEADERS_TAG)
    }

    #[test]
    fn compiles_verifier_gotol() {
        let headers = project_headers_dir();
        if !headers.exists() {
            // Skip on environments where vendored headers aren't checked out.
            eprintln!("skipping: {} not found", headers.display());
            return;
        }
        let tmp = std::env::temp_dir().join("zovia_clang_gotol.o");
        let _ = fs::remove_file(&tmp);

        let inc = default_include_dirs(&headers);
        compile(
            "selftests/progs/verifier_gotol.c",
            &tmp,
            &inc,
            &["CAN_USE_GOTOL"],
        )
        .expect("clang should compile verifier_gotol.c");

        let meta = fs::metadata(&tmp).expect("output .o exists");
        assert!(meta.len() > 0, "output object is empty");
    }
}
