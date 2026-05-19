#!/usr/bin/env python3
"""Divide-and-conquer upstream selftest sweep.

The Rust `dev selftest-baseline-{write,check}-upstream` runs the whole
tree in one process. Each `.c` file is independent, so instead we fan
`dev selftest-file <f> --upstream <root>` out across a process pool and
aggregate the per-prog verdicts here. No Rust changes; the Rust
baseline-refresh path can be deleted later.

  scripts/parallel_selftest.py --out /tmp/cur.tsv
  scripts/parallel_selftest.py --out /tmp/cur.tsv --baseline /tmp/ref.tsv

Report format (sorted, stable): one line per (file, prog)
  <basename.c>::<prog>\\t<VERDICT>
VERDICT ∈ PASS | FALSE_ACCEPT | FALSE_REJECT | ERROR | SKIP | OTHER

Gate semantics when --baseline is given:
  * FALSE_ACCEPT anywhere            -> hard fail (soundness floor)
  * was PASS in ref, non-PASS now    -> regression (fail)
  * non-PASS in ref, PASS now        -> improvement (informational)
Exit 0 iff zero FALSE_ACCEPT and zero regressions vs --baseline.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed

# Verdict lines are 2-space-indented: `  [PASS]  prog (desc)`,
# `  [FALSE-ACCEPT (soundness!)]  prog (...)`,
# `  [FALSE-REJECT (reason)]  prog (...)`, `  [skip: ...]  prog (...)`.
# Log noise (`[ERROR] ...`, `[Analysis] ...`, `[WARN] ...`,
# `[Verifier] ...`) is column-0 — the leading-whitespace anchor plus
# the known-class filter excludes it. The tag may itself contain
# parenthesised `(...)` with no inner `]`, so match up to the final `]`.
VERDICT_RE = re.compile(r"^\s+\[([^\]]+)\]\s+(\S+)")
_KNOWN = {"PASS", "FALSE_ACCEPT", "FALSE_REJECT", "SKIP"}


def classify(tag: str) -> str:
    t = tag.strip().upper().replace(" ", "")
    if t == "PASS":
        return "PASS"
    if t.startswith("FALSE-ACCEPT") or t.startswith("FALSE_ACCEPT"):
        return "FALSE_ACCEPT"
    if t.startswith("FALSE-REJECT") or t.startswith("FALSE_REJECT"):
        return "FALSE_REJECT"
    if t.startswith("SKIP"):
        return "SKIP"
    if t.startswith("ERROR"):
        return "ERROR"
    return "OTHER"


def run_one(args) -> tuple[str, list[tuple[str, str]], str | None]:
    zovia, upstream, path, timeout = args
    fname = os.path.basename(path)
    cmd = [zovia, "-q", "dev", "selftest-file", path, "--upstream", upstream]
    try:
        p = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout, errors="replace"
        )
        out = p.stdout + "\n" + p.stderr
    except subprocess.TimeoutExpired:
        return fname, [], "timeout"
    except Exception as e:  # noqa: BLE001
        return fname, [], f"spawn:{e}"
    recs: list[tuple[str, str]] = []
    seen: set[str] = set()
    for ln in out.splitlines():
        m = VERDICT_RE.match(ln)
        if not m:
            continue
        verdict = classify(m.group(1))
        if verdict not in _KNOWN:  # log noise / unknown bracket tag
            continue
        prog = m.group(2)
        if prog in seen:
            continue
        seen.add(prog)
        recs.append((prog, verdict))
    err = None if recs else ("no-verdicts (compile-fail?)")
    return fname, recs, err


def load_ref(path: str) -> dict[str, str]:
    d: dict[str, str] = {}
    with open(path) as f:
        for ln in f:
            ln = ln.rstrip("\n")
            if not ln or "\t" not in ln:
                continue
            k, v = ln.split("\t", 1)
            d[k] = v
    return d


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--zovia", default="./target/release/zovia")
    ap.add_argument("--upstream", default="vendor/linux")
    ap.add_argument(
        "--progs",
        default="vendor/linux/tools/testing/selftests/bpf/progs",
        help="directory of upstream selftest .c files",
    )
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 8)
    ap.add_argument("--timeout", type=int, default=120, help="per-file seconds")
    ap.add_argument("--out", required=True, help="write the TSV verdict report here")
    ap.add_argument("--baseline", help="reference TSV to diff against (gate)")
    a = ap.parse_args()

    files = sorted(
        os.path.join(a.progs, f)
        for f in os.listdir(a.progs)
        if f.endswith(".c")
    )
    if not files:
        print(f"no .c files under {a.progs}", file=sys.stderr)
        return 2
    print(
        f"[parallel_selftest] {len(files)} files, jobs={a.jobs}, "
        f"timeout={a.timeout}s, zovia={a.zovia}",
        file=sys.stderr,
    )

    report: dict[str, str] = {}
    errs: list[str] = []
    done = 0
    with ProcessPoolExecutor(max_workers=a.jobs) as ex:
        futs = {
            ex.submit(run_one, (a.zovia, a.upstream, p, a.timeout)): p
            for p in files
        }
        for fut in as_completed(futs):
            fname, recs, err = fut.result()
            for prog, verdict in recs:
                report[f"{fname}::{prog}"] = verdict
            if err:
                errs.append(f"{fname}: {err}")
            done += 1
            if done % 100 == 0:
                print(f"[parallel_selftest] {done}/{len(files)}", file=sys.stderr)

    with open(a.out, "w") as f:
        for k in sorted(report):
            f.write(f"{k}\t{report[k]}\n")

    from collections import Counter

    c = Counter(report.values())
    print(f"[parallel_selftest] wrote {a.out}: {dict(c)}", file=sys.stderr)
    if errs:
        print(
            f"[parallel_selftest] {len(errs)} files with no verdicts "
            f"(timeout/compile-fail) — first 10:",
            file=sys.stderr,
        )
        for e in errs[:10]:
            print(f"    {e}", file=sys.stderr)

    fa = sorted(k for k, v in report.items() if v == "FALSE_ACCEPT")
    print(f"\nFALSE_ACCEPT: {len(fa)}")
    for k in fa:
        print(f"  FA  {k}")

    rc = 0
    if fa:
        rc = 1
    if a.baseline:
        ref = load_ref(a.baseline)
        regr = sorted(
            k
            for k, v in report.items()
            if ref.get(k) == "PASS" and v != "PASS"
        )
        impr = sorted(
            k
            for k, v in report.items()
            if k in ref and ref[k] != "PASS" and v == "PASS"
        )
        print(f"\nvs {a.baseline}:  regressions={len(regr)}  improvements={len(impr)}")
        for k in regr:
            print(f"  REGRESSION  {k}  {ref.get(k)} -> {report[k]}")
        for k in impr[:40]:
            print(f"  IMPROVEMENT {k}  {ref[k]} -> PASS")
        if regr:
            rc = 1
    print(f"\nEXIT={rc} (0 = no FALSE_ACCEPT and no regressions)")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
