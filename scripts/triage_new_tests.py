#!/usr/bin/env python3
"""Filter the v6.15 baseline to tests newly classified in the
expansion session (commits since the pre-session baseline at 0f1ff45).

A prog is considered "new in this session" if it was SKIPPED in the
pre-session baseline AND has a non-SKIPPED outcome now. Original
__success/__failure-annotated progs (the 1844 that passed before)
are excluded.

Usage:

    scripts/triage_new_tests.py                    # summary
    scripts/triage_new_tests.py --outcome FALSE_REJECT
    scripts/triage_new_tests.py --outcome FALSE_ACCEPT --jsonl
    scripts/triage_new_tests.py --before-ref 0f1ff45 --outcome FALSE_REJECT
"""

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

PRE_SESSION_REF = "1ab0ac6"  # last commit before the expansion session
                              # (1844 PASS / 1667 SKIPPED / 0 FR / 0 FA).
                              # 0f1ff45 is mid-session (post-batch-1).
BASELINE_PATH = "selftests/baseline_v6.15_full.json"


def load_baseline(ref: str | None) -> dict:
    if ref is None:
        return json.loads(Path(BASELINE_PATH).read_text())
    out = subprocess.run(
        ["git", "show", f"{ref}:{BASELINE_PATH}"],
        capture_output=True, text=True, check=True,
    ).stdout
    return json.loads(out)


def progs(baseline: dict):
    for fname, fdata in baseline["files"].items():
        for pname, pdata in fdata.get("progs", {}).items():
            yield fname, pname, pdata


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--before-ref", default=PRE_SESSION_REF,
                   help=f"Pre-session git ref (default: {PRE_SESSION_REF})")
    p.add_argument("--outcome",
                   choices=["PASS", "FALSE_REJECT", "FALSE_ACCEPT", "ERROR", "SKIPPED"],
                   help="Filter by outcome (default: all non-SKIPPED)")
    p.add_argument("--jsonl", action="store_true",
                   help="Emit one JSON object per line for piping")
    p.add_argument("--summary-only", action="store_true",
                   help="Print outcome counts only")
    args = p.parse_args()

    before = load_baseline(args.before_ref)
    after = load_baseline(None)

    before_skipped: set[tuple[str, str]] = {
        (f, n) for f, n, d in progs(before) if d.get("ours") == "SKIPPED"
    }

    new_tests = []
    for fname, pname, pdata in progs(after):
        if (fname, pname) not in before_skipped:
            continue
        outcome = pdata.get("ours", "?")
        if args.outcome and outcome != args.outcome:
            continue
        if not args.outcome and outcome == "SKIPPED":
            continue
        new_tests.append((fname, pname, pdata))

    counts = Counter(d.get("ours", "?") for _, _, d in new_tests)

    if args.summary_only or not args.jsonl:
        print(f"Pre-session ref: {args.before_ref}", file=sys.stderr)
        print(f"New tests in this session: {len(new_tests)}", file=sys.stderr)
        print(f"  by outcome: {dict(counts)}", file=sys.stderr)
        if args.summary_only:
            return 0

    if args.jsonl:
        for fname, pname, pdata in new_tests:
            print(json.dumps({"file": fname, "prog": pname, **pdata}))
    else:
        for fname, pname, pdata in new_tests:
            outcome = pdata.get("ours", "?")
            note = pdata.get("note", "")
            note_str = f" -- {note[:100]}" if note else ""
            print(f"  [{outcome:13}]  {fname}::{pname}{note_str}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
