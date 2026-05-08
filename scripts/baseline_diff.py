#!/usr/bin/env python3
"""Diff two zovia selftest baselines.

A baseline is the JSON file written by `zovia dev selftest-baseline-write`
or `zovia dev selftest-baseline-write-upstream`. This script replaces the
report-printing logic of `zovia dev selftest-baseline-check{,-modern}`:
the typical workflow is now

    zovia dev selftest-baseline-write-upstream vendor/linux /tmp/current.json
    scripts/baseline_diff.py selftests/baseline_v6.15_full.json /tmp/current.json

Categories
----------
PASS-likes:  PASS
non-PASS:    FALSE_REJECT, FALSE_ACCEPT, ERROR, OUT_OF_SCOPE, SKIPPED,
             anything else

OUT_OF_SCOPE is the verdict for tests that need loader-side
pre-processing we deliberately don't implement (libbpf static linking,
CO-RE relocation, weak-ksym address folding). It's distinct from
SKIPPED — SKIPPED means "no static-analysis question to answer here"
(subprog-only, JIT-only, `__msg()` log-line asserts, race tests).

* regression: PASS in baseline, non-PASS now (gates the build, exits 1)
* improvement: non-PASS in baseline, PASS now (just informational)
* neutral change: ours-field changed but neither side is PASS (e.g.
  ERROR <-> FALSE_REJECT shuffles when a kernel-rejection mask gets
  unmasked, or FALSE_REJECT -> OUT_OF_SCOPE when a test gets
  reclassified)
* new entry: prog is in current but not baseline (UNTRACKED — does not
  fail the gate, but worth flagging)
* removed entry: in baseline but missing from current

Filtered SKIPPED: the Rust fast-check path emits `ours == "SKIPPED"` with
a `note` starting with "filtered" for rows it deliberately didn't re-run
to save time. We honor the same convention and treat those as unchanged.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from typing import Optional

PASS = "PASS"


def load_baseline(path: str) -> dict:
    with open(path) as f:
        return json.load(f)


def per_prog_view(baseline: dict, modern_only: bool) -> dict:
    """Flatten the baseline to {(file, prog): ProgEntry} for easy diffing."""
    out = {}
    for fname, fe in baseline.get("files", {}).items():
        if modern_only and fname.startswith("legacy/"):
            continue
        for pname, pe in fe.get("progs", {}).items():
            out[(fname, pname)] = pe
    return out


def is_filtered_skip(entry: dict) -> bool:
    return entry.get("ours") == "SKIPPED" and (entry.get("note") or "").startswith(
        "filtered"
    )


def tally(view: dict) -> Counter:
    c: Counter = Counter()
    for e in view.values():
        c[e.get("ours", "?")] += 1
    return c


def print_counts(prev: Counter, curr: Counter) -> None:
    keys = sorted(set(prev) | set(curr))
    width = max((len(k) for k in keys), default=0)
    print("=== Counts ===")
    for k in keys:
        a, b = prev.get(k, 0), curr.get(k, 0)
        delta = b - a
        marker = "" if delta == 0 else f"  ({delta:+d})"
        print(f"  {k:<{width}}  {a:5d} -> {b:5d}{marker}")


def fmt_entry(file: str, prog: str, was: str, now: str) -> str:
    return f"  {file}::{prog}  {was} -> {now}"


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("baseline", help="Stored baseline JSON (the reference)")
    p.add_argument("current", help="Fresh baseline JSON (compared against the reference)")
    p.add_argument(
        "--modern-only",
        action="store_true",
        help="Skip rows under `legacy/...` in both files. Mirrors the "
        "old `selftest-baseline-check-modern` gate.",
    )
    p.add_argument(
        "--show-improvements",
        action="store_true",
        help="Also list non-PASS -> PASS transitions (otherwise just counted).",
    )
    p.add_argument(
        "--max-list",
        type=int,
        default=200,
        help="Cap the number of rows printed per category (default 200).",
    )
    args = p.parse_args()

    base = per_prog_view(load_baseline(args.baseline), args.modern_only)
    curr = per_prog_view(load_baseline(args.current), args.modern_only)

    print_counts(tally(base), tally(curr))
    print()

    shared = set(base) & set(curr)
    only_in_base = sorted(set(base) - set(curr))
    only_in_curr = sorted(set(curr) - set(base))

    regressions: list[tuple[str, str, str, str]] = []
    improvements: list[tuple[str, str, str, str]] = []
    neutral: list[tuple[str, str, str, str]] = []
    unchanged = 0

    for key in sorted(shared):
        b, c = base[key], curr[key]
        if is_filtered_skip(c):
            unchanged += 1
            continue
        bo, co = b.get("ours"), c.get("ours")
        if bo == co:
            unchanged += 1
            continue
        row = (key[0], key[1], bo or "?", co or "?")
        if bo == PASS and co != PASS:
            regressions.append(row)
        elif bo != PASS and co == PASS:
            improvements.append(row)
        else:
            neutral.append(row)

    print("=== Diff summary ===")
    print(f"  unchanged:       {unchanged}")
    print(f"  regressions:     {len(regressions)}   (PASS -> non-PASS, gates build)")
    print(f"  improvements:    {len(improvements)}   (non-PASS -> PASS)")
    print(f"  neutral changes: {len(neutral)}   (e.g. ERROR <-> FALSE_REJECT shuffles)")
    print(f"  new entries:     {len(only_in_curr)}   (in current, absent from baseline)")
    print(f"  removed entries: {len(only_in_base)}   (in baseline, absent from current)")

    if regressions:
        print(f"\n=== REGRESSIONS ({len(regressions)}) ===")
        for f, prog, was, now in regressions[: args.max_list]:
            print(fmt_entry(f, prog, was, now))
        if len(regressions) > args.max_list:
            print(f"  ... ({len(regressions) - args.max_list} more)")

    if neutral:
        print(f"\n=== Neutral changes ({len(neutral)}) ===")
        for f, prog, was, now in neutral[: args.max_list]:
            print(fmt_entry(f, prog, was, now))
        if len(neutral) > args.max_list:
            print(f"  ... ({len(neutral) - args.max_list} more)")

    if args.show_improvements and improvements:
        print(f"\n=== Improvements ({len(improvements)}) ===")
        for f, prog, was, now in improvements[: args.max_list]:
            print(fmt_entry(f, prog, was, now))
        if len(improvements) > args.max_list:
            print(f"  ... ({len(improvements) - args.max_list} more)")

    if only_in_curr:
        print(f"\n=== New entries ({len(only_in_curr)}) ===")
        for f, prog in only_in_curr[: args.max_list]:
            now = curr[(f, prog)].get("ours", "?")
            print(f"  {f}::{prog}  ours={now}")
        if len(only_in_curr) > args.max_list:
            print(f"  ... ({len(only_in_curr) - args.max_list} more)")

    if only_in_base:
        print(f"\n=== Removed entries ({len(only_in_base)}) ===")
        for f, prog in only_in_base[: args.max_list]:
            was = base[(f, prog)].get("ours", "?")
            print(f"  {f}::{prog}  was={was}")
        if len(only_in_base) > args.max_list:
            print(f"  ... ({len(only_in_base) - args.max_list} more)")

    return 1 if regressions else 0


if __name__ == "__main__":
    sys.exit(main())
