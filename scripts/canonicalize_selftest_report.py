#!/usr/bin/env python3
"""Strip timing from selftest/prevail JSON reports into a stable canonical form.

Usage: canonicalize.py <input.json> <output.json>

Produces: sorted list of {test, outcome, expected, actual} entries plus totals
(without time_ms). Stable across runs; any diff reflects a real behavior change.
"""
import json
import sys


def canon_selftest(d: dict) -> dict:
    tests = []
    for f in d.get("files", []):
        for t in f.get("tests", []):
            tests.append({
                "test": f"{f['file']}::{t['name']}",
                "outcome": t.get("outcome"),
                "expected": t.get("expected"),
                "actual": t.get("actual"),
            })
    tests.sort(key=lambda x: x["test"])
    return {
        "totals": {k: d[k] for k in
                   ("total_files", "total_tests", "passed",
                    "false_positives", "false_negatives", "skipped", "errors")
                   if k in d},
        "tests": tests,
    }


def canon_prevail(d):
    # Prevail benchmark uses a different shape; attempt best-effort flatten.
    tests = []
    def walk(obj, prefix=""):
        if isinstance(obj, dict):
            if "name" in obj and ("outcome" in obj or "result" in obj or "status" in obj):
                tests.append({
                    "test": f"{prefix}{obj['name']}",
                    "outcome": obj.get("outcome") or obj.get("result") or obj.get("status"),
                    "expected": obj.get("expected"),
                    "actual": obj.get("actual"),
                })
            for k, v in obj.items():
                if k in ("time_ms", "duration_ms"):
                    continue
                walk(v, prefix)
        elif isinstance(obj, list):
            for item in obj:
                walk(item, prefix)
    walk(d)
    tests.sort(key=lambda x: x["test"])
    return {"tests": tests}


def main():
    if len(sys.argv) != 3:
        sys.exit("usage: canonicalize.py <in.json> <out.json>")
    with open(sys.argv[1]) as f:
        d = json.load(f)
    if isinstance(d, dict) and "files" in d:
        out = canon_selftest(d)
    else:
        out = canon_prevail(d)
    with open(sys.argv[2], "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
        f.write("\n")


if __name__ == "__main__":
    main()
