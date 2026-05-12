#!/usr/bin/env python3
"""
Phase 2 corpus harness for the userspace-BCF pipeline (D-thin in the
plan in `memory/project_userspace_bcf.md`).

Runs `zovia verify` over a directory of `.bpf.o` programs both **with**
and **without** `--bcf`, classifies the outcome of each pair, and
reports the refinement gain (programs that flipped from REJECT → ACCEPT
once the BCF deriver was turned on).

Outcomes per run:
  ACCEPT  — exit 0, "Pass: 1" in stdout
  REJECT  — exit 0, "Fail: ..." but a known failure category
  TIMEOUT — wall-clock exceeded (--timeout)
  ERROR   — non-zero exit / panic / unknown

Usage:
    scripts/bcf_corpus.py [DIR] [--zovia PATH] [--timeout SECS]
                          [--out RESULTS.json]

Defaults:
    DIR      = /Users/yalucai/BCF/bpf-progs/collected
    --zovia  = ./target/release/zovia (build first: `cargo build --release`)
    --timeout= 60

Exit code is 0 unless the corpus run itself errored — *not* the number
of rejections. Read the summary or RESULTS.json for that.

This script is intentionally minimal: it's the Phase-2 D-thin starting
point, not a final harness. Once we have ALU broadening + more
refinement sites, expand sample size and add a match-vs-BCF-accepted
column.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable, Optional

DEFAULT_CORPUS = Path("/Users/yalucai/BCF/bpf-progs/collected")
DEFAULT_ZOVIA = Path("target/release/zovia")
DEFAULT_TIMEOUT = 60


@dataclass
class RunResult:
    program: str
    bcf: bool
    outcome: str  # ACCEPT, REJECT, TIMEOUT, ERROR
    elapsed_s: float
    fail_reason: Optional[str] = None  # first failure line from stdout, if REJECT
    bundle_size: Optional[int] = None  # bytes, if bcf=True and bundle written


PASS_RE = re.compile(r"^Pass:\s*1\b", re.M)
FAIL_RE = re.compile(r"^Fail:\s*(\d+)", re.M)
FAILURE_LINE_RE = re.compile(r"^\s+(\S+):\s*(.+)$", re.M)


def classify(stdout: str, returncode: int) -> tuple[str, Optional[str]]:
    """Map verifier output to (outcome, fail_reason)."""
    if returncode != 0:
        # zovia normally exits 0 even on REJECT; non-zero = real error/panic
        return ("ERROR", f"exit={returncode}")
    if PASS_RE.search(stdout):
        return ("ACCEPT", None)
    fail_match = FAIL_RE.search(stdout)
    if fail_match and int(fail_match.group(1)) > 0:
        # Try to pull the first "  <section>: <reason>" line from the
        # --- FAILURES --- block.
        in_failures = False
        for line in stdout.splitlines():
            if "--- FAILURES ---" in line:
                in_failures = True
                continue
            if in_failures and line.strip():
                m = FAILURE_LINE_RE.match(line)
                if m:
                    return ("REJECT", f"{m.group(1)}: {m.group(2)}")
                return ("REJECT", line.strip())
        return ("REJECT", None)
    return ("ERROR", "unclassified output")


def run_one(zovia: Path, prog: Path, with_bcf: bool, timeout: float) -> RunResult:
    args = [str(zovia), "-q"]
    if with_bcf:
        args.append("--bcf")
    args += ["verify", str(prog)]
    bundle_path = prog.with_suffix(prog.suffix + ".bcf-bundle") if with_bcf else None
    if bundle_path and bundle_path.exists():
        bundle_path.unlink()

    start = time.monotonic()
    try:
        result = subprocess.run(
            args, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return RunResult(
            program=prog.name, bcf=with_bcf, outcome="TIMEOUT", elapsed_s=elapsed
        )

    elapsed = time.monotonic() - start
    outcome, reason = classify(result.stdout, result.returncode)
    bundle_size = (
        bundle_path.stat().st_size if bundle_path and bundle_path.exists() else None
    )
    return RunResult(
        program=prog.name,
        bcf=with_bcf,
        outcome=outcome,
        elapsed_s=round(elapsed, 2),
        fail_reason=reason,
        bundle_size=bundle_size,
    )


def iter_programs(corpus_dir: Path) -> Iterable[Path]:
    for p in sorted(corpus_dir.iterdir()):
        if p.is_file() and (p.suffix == ".o" or p.name.endswith(".bpf.o")):
            yield p


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "dir", nargs="?", default=str(DEFAULT_CORPUS), help="corpus directory"
    )
    parser.add_argument(
        "--zovia", default=str(DEFAULT_ZOVIA), help="path to zovia binary"
    )
    parser.add_argument(
        "--timeout", type=float, default=DEFAULT_TIMEOUT, help="seconds per program"
    )
    parser.add_argument("--out", default=None, help="write results JSON here")
    parser.add_argument(
        "--no-baseline",
        action="store_true",
        help="only run with --bcf (skip the baseline-off pass)",
    )
    args = parser.parse_args()

    corpus = Path(args.dir)
    zovia = Path(args.zovia)
    if not zovia.exists():
        print(f"error: zovia binary not found at {zovia}", file=sys.stderr)
        print("hint: cargo build --release", file=sys.stderr)
        return 2
    if not corpus.exists():
        print(f"error: corpus dir not found: {corpus}", file=sys.stderr)
        return 2

    progs = list(iter_programs(corpus))
    if not progs:
        print(f"error: no .bpf.o programs under {corpus}", file=sys.stderr)
        return 2

    print(f"# bcf_corpus: {len(progs)} program(s) under {corpus}")
    print(f"#   zovia    = {zovia}")
    print(f"#   timeout  = {args.timeout}s per run")
    print()

    results: list[RunResult] = []
    for prog in progs:
        # Baseline (no --bcf), unless suppressed.
        if not args.no_baseline:
            r0 = run_one(zovia, prog, with_bcf=False, timeout=args.timeout)
            results.append(r0)
        else:
            r0 = None
        r1 = run_one(zovia, prog, with_bcf=True, timeout=args.timeout)
        results.append(r1)

        flip = ""
        if r0 and r0.outcome == "REJECT" and r1.outcome == "ACCEPT":
            flip = "  ← refined"
        bundle = f" (bundle {r1.bundle_size}B)" if r1.bundle_size else ""
        baseline = f"{r0.outcome:7}" if r0 else "       "
        print(f"{prog.name:48} {baseline} --bcf:{r1.outcome:7}{bundle}{flip}")

    # Summary
    print()
    print("Summary:")
    if not args.no_baseline:
        n = sum(1 for r in results if not r.bcf)
        ab = sum(1 for r in results if not r.bcf and r.outcome == "ACCEPT")
        print(f"  baseline (no --bcf): {ab}/{n} ACCEPT")
    n = sum(1 for r in results if r.bcf)
    ab = sum(1 for r in results if r.bcf and r.outcome == "ACCEPT")
    print(f"  with --bcf:          {ab}/{n} ACCEPT")
    if not args.no_baseline:
        flips = 0
        prog_to_outs: dict[str, dict[bool, str]] = {}
        for r in results:
            prog_to_outs.setdefault(r.program, {})[r.bcf] = r.outcome
        for prog, outs in prog_to_outs.items():
            if outs.get(False) == "REJECT" and outs.get(True) == "ACCEPT":
                flips += 1
        print(f"  refinement gain:     {flips} program(s) REJECT → ACCEPT")

    if args.out:
        Path(args.out).write_text(json.dumps([asdict(r) for r in results], indent=2))
        print(f"\nresults JSON: {args.out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
