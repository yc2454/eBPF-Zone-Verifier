#!/usr/bin/env python3
"""
Build a stratified ~cilium-42-scale representative calico subset for the
fast per-commit impact scorecard, and (default) diff the current zovia
against a pre-fix baseline sweep JSON — zovia-only, NO 2h sweep, NO VM.

Why this is sound enough for per-commit use:
  * All 337 calico objects fail in the SAME shared function
    (calico_tc_main); the dominant behaviour axis is the BLOCKER CLASS,
    not the 118 felix sources. A sample stratified across every
    (blocker-class) x (spread of sources) x (clang extreme) cell tracks
    the corpus's verdict distribution.
  * The kernel verdict is invariant to zovia changes, so soundness
    (FA=0) is gated by the frozen kernel oracle via fa_scorecard.py
    (cilium-42 today; calico-repr once its oracle is captured) — this
    script measures the zovia-side verdict/bundle DELTA cheaply.
  * Tradeoff: a sample can miss a source-specific regression. Mitigation
    = keep the full 337 sweep as a PRE-MILESTONE backstop, not per-commit.

Usage:
  scripts/calico_repr.py --emit-list           # write /tmp/calico_repr_list.txt
  scripts/calico_repr.py --diff BASELINE.json  # zovia-only impact vs baseline
"""
from __future__ import annotations
import argparse, concurrent.futures, glob, json, os, re, subprocess, sys, threading, time
from collections import defaultdict
from pathlib import Path

BPFPROGS = "/Users/yalucai/BCF/bpf-progs"
ZOVIA = "./target/release/zovia"
PER_CLASS = 10  # sources sampled per blocker class -> ~5 classes*10 ~= 50


def parse(p: str):
    b = p.split("/")[-1][:-2]
    m = re.match(r"clang-(\d+)_-O([0-9sz]+)_(.+)$", b)
    return (int(m.group(1)), m.group(2), m.group(3)) if m else (0, "?", b)


def klass(fr: str) -> str:
    fr = fr or ""
    if "!read_ok" in fr:
        return "read_ok"
    if "Invalid helper ID" in fr:
        return "helperID"
    if "complexity" in fr or "1000000" in fr:
        return "cx1M"
    if "Unsafe generic load" in fr:
        return "scalarid"
    if "timeout" in fr.lower():
        return "timeout"
    return "other"


def load_baseline_rows(paths: list[str]) -> list[dict]:
    rows: list[dict] = []
    for f in paths:
        rows += json.load(open(f))
    return rows


def stratify(rows: list[dict]) -> list[str]:
    by_class: dict[str, dict[str, list[tuple]]] = defaultdict(lambda: defaultdict(list))
    for r in rows:
        cl, opt, src = parse(r["program"])
        by_class[klass(r.get("l2_fail_reason", ""))][src].append((cl, r["program"]))
    chosen: list[str] = []
    for k, by_src in sorted(by_class.items()):
        # deterministic spread of sources across the class
        srcs = sorted(by_src)
        step = max(1, len(srcs) // PER_CLASS)
        for s in srcs[::step][:PER_CLASS]:
            variants = sorted(by_src[s])
            chosen.append(variants[0][1])              # min-clang
            if variants[-1][1] != variants[0][1]:
                chosen.append(variants[-1][1])         # max-clang extreme
    return sorted(set(chosen))


def emit_list(rows, out="/tmp/calico_repr_list.txt"):
    repr_set = stratify(rows)
    Path(out).write_text(
        "\n".join(f"{BPFPROGS}/{p}" for p in repr_set) + "\n"
    )
    by_k = defaultdict(int)
    for p in repr_set:
        # recompute class from baseline rows for the summary
        pass
    print(f"wrote {out}: {len(repr_set)} objects "
          f"(~{PER_CLASS}/blocker-class, source-spread, clang-extremes)")
    return repr_set


def zovia_l2(obj: str, timeout: float) -> tuple[str, bool]:
    bundle = Path(f"{obj}.bcf-bundle")
    if bundle.exists():
        bundle.unlink()
    try:
        r = subprocess.run(
            [ZOVIA, "--bcf", "--kernel-mode", "verify", obj],
            capture_output=True, text=True, timeout=timeout,
        )
        out = r.stdout
    except subprocess.TimeoutExpired:
        return "TIMEOUT", bundle.exists()
    if "VERIFICATION PASSED" in out or re.search(r"Section.*: PASS", out):
        v = "ACCEPT"
    elif "FAILURE:" in out or "ERROR" in out or "halted" in out:
        v = "REJECT"
    else:
        v = "ERROR"
    return v, bundle.exists()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--baseline", default=None,
                    help="glob of pre-fix sweep JSON(s); default /tmp/results_calico_0*.json")
    ap.add_argument("--emit-list", action="store_true")
    ap.add_argument("--diff", action="store_true",
                    help="zovia-only impact of current binary vs baseline")
    # NOTE: --diff is a weak no-VM STOPGAP. Big calico objects need
    # ~150-220s of zovia compute; under N-way parallelism CPU contention
    # stretches per-object wall time, so a tight --timeout converts
    # "slow" into inconclusive "TIMEOUT" (seen: 60s -> 59/71 TIMEOUT).
    # The AUTHORITATIVE per-commit measurement is the frozen-kernel-oracle
    # scorecard (scripts/fa_scorecard.py --jobs N) which classifies vs
    # kernel ground truth and is not baseline/timeout-sensitive. Keep
    # --diff only as a fast 0-regression / 0-FA-suspect tripwire, and
    # give it a realistic timeout.
    ap.add_argument("--timeout", type=float, default=220)
    ap.add_argument("--jobs", type=int, default=8,
                    help="parallel zovia workers (default 8 = the P-cores; "
                         "machine is 8P+4E, leave E-cores for the OS)")
    a = ap.parse_args()

    bpaths = sorted(glob.glob(a.baseline or "/tmp/results_calico_0*.json"))
    rows = load_baseline_rows(bpaths)
    base = {r["program"]: r for r in rows}
    repr_set = emit_list(rows)

    if a.emit_list and not a.diff:
        return 0

    # zovia-only impact diff vs baseline JSON (NO VM, NO re-sweep),
    # parallel across --jobs workers (one zovia subprocess per worker;
    # zovia is single-threaded so N workers ~= N P-cores of throughput).
    imp = reg = same = moved = 0
    fa_suspect: list[str] = []
    lock = threading.Lock()
    done = [0]
    n = len(repr_set)

    def work(rel: str):
        b = base.get(rel, {})
        b_out = b.get("l2_outcome", "?")
        b_bun = b.get("bundle_exists", False)
        v, bun = zovia_l2(f"{BPFPROGS}/{rel}", a.timeout)
        if (v, bun) == (b_out, b_bun):
            tag = "same"
        elif (b_out != "ACCEPT" and v == "ACCEPT") or (not b_bun and bun):
            tag = "IMPROVED"
        elif b_out == "ACCEPT" and v != "ACCEPT":
            tag = "REGRESSED"
        else:
            tag = "moved"
        fa = v == "ACCEPT" and not bun and b.get("l3_outcome") == "REJECT"
        return rel, tag, b_out, b_bun, v, bun, fa

    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as ex:
        for rel, tag, b_out, b_bun, v, bun, fa in ex.map(work, repr_set):
            if tag == "same":
                same += 1
            elif tag == "IMPROVED":
                imp += 1
            elif tag == "REGRESSED":
                reg += 1
            else:
                moved += 1
            if fa:
                fa_suspect.append(rel)
            with lock:
                done[0] += 1
                print(f"[{done[0]:3d}/{n}] {tag:9s} {b_out}/{b_bun} -> "
                      f"{v}/{bun}  {rel}", flush=True)

    dt = time.time() - t0
    print(f"\n=== calico-repr zovia-only impact ({n} obj, {dt:.0f}s, "
          f"{a.jobs} workers) ===")
    print(f"  IMPROVED {imp}   REGRESSED {reg}   same {same}   moved {moved}")
    print(f"  FA-suspect (ACCEPT, no bundle, baseline kernel-REJECT): "
          f"{len(fa_suspect)} {fa_suspect[:8]}")
    print("  NOTE: FA=0 is authoritatively gated by the frozen kernel "
          "oracle via fa_scorecard.py; this is a fast tripwire only.")
    return 1 if (reg or fa_suspect) else 0


if __name__ == "__main__":
    sys.exit(main())
