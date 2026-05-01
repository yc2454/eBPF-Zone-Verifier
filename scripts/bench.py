#!/usr/bin/env python3
"""Recursive ELF-corpus benchmark — Python port of the old `dev bcf-benchmark`.

Walks a directory for `.o` files (or reads an explicit list), filters by
project/compiler/opt/source, hands the surviving file list to
`zovia dev verify-corpus`, then aggregates the JSONL records into a
human report and a JSON results file under `results/bcf/`.

Filename convention (BCF/Cilium-style): `clang-<VER>_-<OPT>_<SOURCE>.o`.
Files that don't match the pattern fall back to compiler/opt = "[unknown ...]"
and source_prog = the filename — i.e. they're still benched, just not grouped.

Usage:
    scripts/bench.py <dir> [--project NAME] [--compiler NAME] [--opt LEVEL]
                           [--source NAME] [--input-list FILE]
                           [--zovia PATH] [--zovia-flag FLAG ...]
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Optional

DEFAULT_ZOVIA = "./target/release/zovia"
RESULTS_DIR = Path("results/bcf")


def parse_bcf_filename(name: str) -> tuple[str, str, str]:
    """Mirror Rust `parse_benchmark_filename`: clang-<VER>_-<OPT>_<SOURCE>.o"""
    fallback = ("[unknown compiler]", "[unknown optimization level]", name)
    if not name.startswith("clang-"):
        return fallback
    parts = name.split("_", 2)
    if len(parts) < 3:
        return fallback
    compiler = parts[0]
    opt = parts[1]
    source = parts[2]
    if source.endswith(".o"):
        source = source[:-2]
    return (compiler, opt, source)


def collect_files(root: Optional[Path], input_list: Optional[Path]) -> list[Path]:
    if input_list is not None:
        with open(input_list) as f:
            return [Path(line.strip()) for line in f if line.strip()]
    if root is None:
        return []
    return sorted(p for p in root.rglob("*.o") if p.is_file())


def project_of(path: Path, root: Optional[Path]) -> str:
    if root is None:
        return "unknown"
    try:
        rel = path.relative_to(root)
    except ValueError:
        return "unknown"
    parts = rel.parts
    return parts[0] if len(parts) > 1 else "unknown"


def filter_files(
    files: list[Path],
    root: Optional[Path],
    project: Optional[str],
    compiler: Optional[str],
    opt: Optional[str],
    source: Optional[str],
) -> list[tuple[Path, str, str, str, str]]:
    """Return [(path, project, compiler, opt, source_prog)] after filtering."""
    out = []
    for p in files:
        c, o, s = parse_bcf_filename(p.name)
        proj = project_of(p, root)
        if project and proj != project:
            continue
        if compiler and c != compiler:
            continue
        if opt and o != opt:
            continue
        if source and s != source:
            continue
        out.append((p, proj, c, o, s))
    return out


def run_zovia_jsonl(
    zovia: str,
    files: list[Path],
    extra_flags: list[str],
) -> list[dict]:
    """Invoke `zovia dev verify-corpus --input-list ... --out ...` and return parsed records."""
    with tempfile.TemporaryDirectory() as td:
        list_path = Path(td) / "files.txt"
        out_path = Path(td) / "out.jsonl"
        list_path.write_text("\n".join(str(p) for p in files) + "\n")
        cmd = [
            zovia,
            "-q",
            *extra_flags,
            "dev",
            "verify-corpus",
            "--input-list",
            str(list_path),
            "--out",
            str(out_path),
        ]
        # Discard stdout chatter — verifier println! noise.
        subprocess.run(cmd, stdout=subprocess.DEVNULL, check=True)
        return [json.loads(ln) for ln in out_path.read_text().splitlines() if ln.strip()]


def aggregate(
    tasks: list[tuple[Path, str, str, str, str]],
    records: list[dict],
) -> dict:
    """Collapse per-(file, section) records into per-file results, grouped by source."""
    by_file: dict[str, list[dict]] = defaultdict(list)
    for rec in records:
        by_file[rec["file"]].append(rec)

    grouped: dict[str, list[dict]] = defaultdict(list)
    summary = {
        "files_processed": 0,
        "files_passed": 0,
        "files_timeout": 0,
        "sections_processed": 0,
        "sections_passed": 0,
        "sections_timeout": 0,
    }

    for path, project, compiler, opt, source_prog in tasks:
        secs = by_file.get(str(path), [])
        sec_passed = sum(1 for r in secs if r["status"] == "PASS")
        sec_timeout = sum(1 for r in secs if r["status"] == "TIMEOUT")
        sec_fail = sum(1 for r in secs if r["status"] not in ("PASS", "TIMEOUT"))

        all_pass = bool(secs) and sec_passed == len(secs)
        only_timeout = bool(secs) and sec_timeout > 0 and sec_fail == 0 and not all_pass

        summary["files_processed"] += 1
        if all_pass:
            summary["files_passed"] += 1
        elif only_timeout:
            summary["files_timeout"] += 1
        summary["sections_processed"] += len(secs)
        summary["sections_passed"] += sec_passed
        summary["sections_timeout"] += sec_timeout

        grouped[source_prog].append(
            {
                "file": path.name,
                "project": project,
                "compiler": compiler,
                "opt": opt,
                "passed": all_pass,
                "timeout": only_timeout,
                "sections": [
                    {
                        "name": r.get("section"),
                        "status": r["status"],
                        "time_ms": r.get("time_ms"),
                        "error": r.get("error"),
                    }
                    for r in secs
                ],
            }
        )

    return {"summary": summary, "results_by_source": dict(grouped)}


def write_text_report(report_path: Path, agg: dict, filters: dict, duration_s: float) -> None:
    s = agg["summary"]
    lines = []
    lines.append("BPF Verifier Benchmark Report")
    lines.append("=============================")
    lines.append(f"Date:     {datetime.datetime.now().isoformat(timespec='seconds')}")
    lines.append(f"Duration: {duration_s:.2f}s")
    for k, v in filters.items():
        if v:
            lines.append(f"Filter [{k}]: {v}")

    pct = lambda a, b: (100.0 * a / b) if b else 0.0
    lines.append("")
    lines.append("--- Program Statistics ---")
    lines.append(f"Total Files Found: {s['files_processed']}")
    lines.append(
        f"Files Passing:     {s['files_passed']} "
        f"({pct(s['files_passed'], s['files_processed']):.1f}%)"
    )
    lines.append(
        f"Files Timeout:     {s['files_timeout']} "
        f"({pct(s['files_timeout'], s['files_processed']):.1f}%)"
    )
    lines.append("")
    lines.append("--- Section Statistics ---")
    lines.append(f"Total Sections:    {s['sections_processed']}")
    lines.append(
        f"Sections Passing:  {s['sections_passed']} "
        f"({pct(s['sections_passed'], s['sections_processed']):.1f}%)"
    )
    lines.append(
        f"Sections Timeout:  {s['sections_timeout']} "
        f"({pct(s['sections_timeout'], s['sections_processed']):.1f}%)"
    )
    lines.append("")
    lines.append("--- Breakdown by Source Program ---")
    for source in sorted(agg["results_by_source"]):
        runs = sorted(
            agg["results_by_source"][source],
            key=lambda r: (r["project"], r["compiler"], r["opt"]),
        )
        lines.append(f"\nSource: {source}")
        for run in runs:
            status = "PASS" if run["passed"] else "FAIL"
            lines.append(
                f"  [{status}] [{run['project']}] {run['compiler']} {run['opt']}: {run['file']}"
            )
            if not run["passed"]:
                for sec in run["sections"]:
                    if sec["status"] != "PASS":
                        msg = sec.get("error") or sec["status"]
                        lines.append(f"      - {sec['name']}: {msg}")
    report_path.write_text("\n".join(lines) + "\n")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("dir", nargs="?", help="Root directory to walk for .o files")
    p.add_argument("--input-list", help="File of newline-separated .o paths (alternative to dir)")
    p.add_argument("--project", help="Filter by first-level subdir")
    p.add_argument("--compiler", help="Filter by clang-<VER> token")
    p.add_argument("--opt", help="Filter by -O<N> token")
    p.add_argument("--source", help="Filter by source program name")
    p.add_argument("--zovia", default=os.environ.get("ZOVIA", DEFAULT_ZOVIA))
    p.add_argument(
        "--zovia-flag",
        action="append",
        default=[],
        help="Pass an extra flag through to zovia (e.g. --zovia-flag=--max-insn=500000). Repeatable.",
    )
    args = p.parse_args()

    if not args.dir and not args.input_list:
        p.error("provide a directory or --input-list FILE")

    if not shutil.which(args.zovia) and not Path(args.zovia).exists():
        p.error(f"zovia binary not found at {args.zovia} (set --zovia or $ZOVIA)")

    root = Path(args.dir).expanduser() if args.dir else None
    list_path = Path(args.input_list).expanduser() if args.input_list else None

    files = collect_files(root, list_path)
    tasks = filter_files(files, root, args.project, args.compiler, args.opt, args.source)

    print(f"=== bench.py ===")
    print(f"Root:           {root or '(input list)'}")
    if args.project: print(f"Filter Project: {args.project}")
    if args.compiler: print(f"Filter Compiler:{args.compiler}")
    if args.opt: print(f"Filter Opt:     {args.opt}")
    if args.source: print(f"Filter Source:  {args.source}")
    print(f"Files matched:  {len(tasks)} (of {len(files)} found)")
    if not tasks:
        return 0

    paths = [t[0] for t in tasks]
    started = datetime.datetime.now()
    records = run_zovia_jsonl(args.zovia, paths, args.zovia_flag)
    duration = (datetime.datetime.now() - started).total_seconds()

    agg = aggregate(tasks, records)
    s = agg["summary"]

    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    suffix_parts = ["benchmark"]
    if args.input_list: suffix_parts.append("custom_list")
    if args.project: suffix_parts.append(args.project)
    if args.compiler: suffix_parts.append(args.compiler)
    if args.opt: suffix_parts.append(args.opt)
    if args.source: suffix_parts.append(args.source)
    suffix_parts.append(datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S"))
    base = "_".join(suffix_parts)

    report_path = RESULTS_DIR / f"{base}_report.txt"
    json_path = RESULTS_DIR / f"{base}_results.json"

    write_text_report(
        report_path,
        agg,
        {
            "Project": args.project,
            "Compiler": args.compiler,
            "Opt": args.opt,
            "Source": args.source,
        },
        duration,
    )
    json_path.write_text(json.dumps({**agg, "summary": {**s, "duration_secs": duration}}, indent=2))

    pct = lambda a, b: (100.0 * a / b) if b else 0.0
    print()
    print(f"Programs: {s['files_passed']}/{s['files_processed']} "
          f"({pct(s['files_passed'], s['files_processed']):.1f}%)")
    print(f"Sections: {s['sections_passed']}/{s['sections_processed']} "
          f"({pct(s['sections_passed'], s['sections_processed']):.1f}%)")
    print(f"Report:   {report_path}")
    print(f"JSON:     {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
