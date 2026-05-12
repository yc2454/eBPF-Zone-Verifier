#!/usr/bin/env python3
"""
Phase 2 corpus harness for the userspace-BCF pipeline.

Two modes:

**Single-dir mode (D-thin):** point at a flat directory of `.bpf.o`
files (default: BCF's curated `collected/`). Reports our accept count
with and without `--bcf`, plus the refinement gain.

**Match-vs-BCF mode:** with `--accepted-index PATH`, walks the
multi-source corpus (cilium/, calico/, bcc/, inspektor-gadget/ under
`--root`), runs only the file variants BCF claims to accept (per the
accepted-index JSON), and reports our match rate against BCF.

Outcomes per run:
  ACCEPT  — exit 0, "Pass: 1" in stdout
  REJECT  — exit 0, "Fail: ..." but a known failure category
  TIMEOUT — wall-clock exceeded (--timeout)
  ERROR   — non-zero exit / panic / unknown

Usage:
    scripts/bcf_corpus.py [DIR] [--zovia PATH] [--timeout SECS]
                          [--out RESULTS.json] [--jobs N]
                          [--no-baseline] [--accepted-index PATH]
                          [--source NAME]

Defaults:
    DIR      = /Users/yalucai/BCF/bpf-progs/collected
    --zovia  = ./target/release/zovia (build first: `cargo build --release`)
    --timeout= 60
    --jobs   = 1 (set higher for multi-file batches)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
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
    source: Optional[str] = None  # corpus-source bucket (e.g. "cilium")


PASS_RE = re.compile(r"^Pass:\s*(\d+)", re.M)
FAIL_RE = re.compile(r"^Fail:\s*(\d+)", re.M)
FAILURE_LINE_RE = re.compile(r"^\s+(\S+):\s*(.+)$", re.M)


def classify(stdout: str, returncode: int) -> tuple[str, Optional[str]]:
    """Map verifier output to (outcome, fail_reason). A program is ACCEPT
    when at least one section passed and none failed; REJECT when any
    section failed; ERROR otherwise (no Pass/Fail summary found, panic,
    or non-zero exit)."""
    if returncode != 0:
        # zovia normally exits 0 even on REJECT; non-zero = real error/panic
        return ("ERROR", f"exit={returncode}")
    pass_match = PASS_RE.search(stdout)
    fail_match = FAIL_RE.search(stdout)
    pass_count = int(pass_match.group(1)) if pass_match else None
    fail_count = int(fail_match.group(1)) if fail_match else None
    if fail_count is not None and fail_count > 0:
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
    if pass_count is not None and pass_count > 0:
        return ("ACCEPT", None)
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


def iter_accepted(
    root: Path, accepted_index: dict, sources: Optional[list[str]]
) -> Iterable[tuple[Path, str]]:
    """Yield (path, source) for every file variant listed in the BCF
    accepted-index, restricted to the given source subset."""
    for source, progs in accepted_index.items():
        if sources and source not in sources:
            continue
        src_dir = root / source
        if not src_dir.is_dir():
            print(f"warning: no source dir for '{source}' at {src_dir}", file=sys.stderr)
            continue
        for _base, variants in progs.items():
            for fname in variants:
                p = src_dir / fname
                if p.is_file():
                    yield p, source


def _run_pair(args: tuple) -> tuple[Optional[RunResult], RunResult]:
    """ProcessPoolExecutor entry point (must be top-level for pickling)."""
    zovia, prog, do_baseline, timeout, source = args
    r0 = None
    if do_baseline:
        r0 = run_one(zovia, prog, with_bcf=False, timeout=timeout)
        r0.source = source
    r1 = run_one(zovia, prog, with_bcf=True, timeout=timeout)
    r1.source = source
    return r0, r1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "dir", nargs="?", default=str(DEFAULT_CORPUS), help="corpus directory or --root in match-vs-BCF mode"
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
    parser.add_argument(
        "--accepted-index",
        default=None,
        help="BCF accepted_prog_index.json; enables match-vs-BCF mode",
    )
    parser.add_argument(
        "--source",
        action="append",
        default=None,
        help="restrict to one corpus source (cilium/calico/bcc/inspektor-gadget); repeatable",
    )
    parser.add_argument(
        "--jobs", type=int, default=1, help="parallel workers (each is one verifier subprocess)"
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

    # Determine the program list. In match-vs-BCF mode we walk subdirs;
    # otherwise it's a flat dir.
    progs_with_src: list[tuple[Path, Optional[str]]]
    if args.accepted_index:
        idx_path = Path(args.accepted_index)
        if not idx_path.exists():
            print(f"error: accepted index not found: {idx_path}", file=sys.stderr)
            return 2
        accepted_index = json.loads(idx_path.read_text())
        progs_with_src = list(iter_accepted(corpus, accepted_index, args.source))
        if not progs_with_src:
            print(f"error: no accepted files found under {corpus}", file=sys.stderr)
            return 2
        print(
            f"# bcf_corpus (match-vs-BCF): {len(progs_with_src)} accepted file(s) "
            f"from sources={args.source or list(accepted_index.keys())}"
        )
    else:
        progs = list(iter_programs(corpus))
        if not progs:
            print(f"error: no .bpf.o programs under {corpus}", file=sys.stderr)
            return 2
        progs_with_src = [(p, None) for p in progs]
        print(f"# bcf_corpus: {len(progs_with_src)} program(s) under {corpus}")

    print(f"#   zovia    = {zovia}")
    print(f"#   timeout  = {args.timeout}s per run")
    print(f"#   jobs     = {args.jobs}")
    print()

    do_baseline = not args.no_baseline
    task_args = [(zovia, p, do_baseline, args.timeout, src) for p, src in progs_with_src]
    results: list[RunResult] = []

    if args.jobs > 1:
        with ProcessPoolExecutor(max_workers=args.jobs) as ex:
            futures = {ex.submit(_run_pair, a): a[1] for a in task_args}
            for fut in as_completed(futures):
                r0, r1 = fut.result()
                if r0 is not None:
                    results.append(r0)
                results.append(r1)
                flip = "  ← refined" if (r0 and r0.outcome == "REJECT" and r1.outcome == "ACCEPT") else ""
                bundle = f" (bundle {r1.bundle_size}B)" if r1.bundle_size else ""
                baseline = f"{r0.outcome:7}" if r0 else "       "
                src_tag = f"[{r1.source}] " if r1.source else ""
                print(f"{src_tag}{r1.program:60} {baseline} --bcf:{r1.outcome:7}{bundle}{flip}")
    else:
        for a in task_args:
            r0, r1 = _run_pair(a)
            if r0 is not None:
                results.append(r0)
            results.append(r1)
            flip = "  ← refined" if (r0 and r0.outcome == "REJECT" and r1.outcome == "ACCEPT") else ""
            bundle = f" (bundle {r1.bundle_size}B)" if r1.bundle_size else ""
            baseline = f"{r0.outcome:7}" if r0 else "       "
            src_tag = f"[{r1.source}] " if r1.source else ""
            print(f"{src_tag}{r1.program:60} {baseline} --bcf:{r1.outcome:7}{bundle}{flip}")

    # Summary
    print()
    print("Summary:")
    bcf_runs = [r for r in results if r.bcf]
    if do_baseline:
        base_runs = [r for r in results if not r.bcf]
        ab_base = sum(1 for r in base_runs if r.outcome == "ACCEPT")
        print(f"  baseline (no --bcf): {ab_base}/{len(base_runs)} ACCEPT")
    ab_bcf = sum(1 for r in bcf_runs if r.outcome == "ACCEPT")
    rj_bcf = sum(1 for r in bcf_runs if r.outcome == "REJECT")
    to_bcf = sum(1 for r in bcf_runs if r.outcome == "TIMEOUT")
    er_bcf = sum(1 for r in bcf_runs if r.outcome == "ERROR")
    print(
        f"  with --bcf:          {ab_bcf}/{len(bcf_runs)} ACCEPT  "
        f"({rj_bcf} reject, {to_bcf} timeout, {er_bcf} error)"
    )
    if do_baseline:
        prog_to_outs: dict[str, dict[bool, str]] = {}
        for r in results:
            prog_to_outs.setdefault(r.program, {})[r.bcf] = r.outcome
        flips = sum(
            1
            for outs in prog_to_outs.values()
            if outs.get(False) == "REJECT" and outs.get(True) == "ACCEPT"
        )
        print(f"  refinement gain:     {flips} program(s) REJECT → ACCEPT")

    if args.accepted_index:
        # In match-vs-BCF mode every program counted is a file BCF
        # claims to accept, so `ab_bcf / total` IS our match rate.
        print(f"  match rate vs BCF:   {ab_bcf}/{len(bcf_runs)} = {100*ab_bcf/len(bcf_runs):.1f}%")
        per_src: dict[str, list[RunResult]] = {}
        for r in bcf_runs:
            per_src.setdefault(r.source or "(none)", []).append(r)
        for src in sorted(per_src):
            rs = per_src[src]
            ab = sum(1 for r in rs if r.outcome == "ACCEPT")
            print(f"    {src:20} {ab:4}/{len(rs):4} = {100*ab/len(rs):5.1f}%")

    if args.out:
        Path(args.out).write_text(json.dumps([asdict(r) for r in results], indent=2))
        print(f"\nresults JSON: {args.out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
