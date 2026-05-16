#!/usr/bin/env python3
"""
Per-program false-accept (FA) audit harness.

Established fact (do NOT re-derive): the BCF corpus is BY CONSTRUCTION
kernel-rejected programs. So any zovia `Pass` section on a corpus
object that is not backed by a real discharging .bcf-bundle is a FALSE
ACCEPT (faithfulness defect). This tool measures, per program-section:

  - PASS / FAIL (parsed from `Section 'X'... PASS/FAIL` lines)
  - whether a `.bcf-bundle` sidecar was produced for the object
  - the set + counts of `Unknown helper N` skip warnings (the systemic
    FA mechanism: checks.rs validate_helper_args returns without
    env.fail when get_helper_proto==None)

Run kernel-mode + --bcf (faithful mirror). gtimeout-bounded per object.

Usage:
  scripts/fa_audit.py --list FILE_OF_PATHS [--timeout 90] [--out audit.json]
  scripts/fa_audit.py PATH [PATH ...] [--timeout 90] [--out audit.json]
"""
from __future__ import annotations
import argparse, json, re, subprocess, sys, time
from pathlib import Path

ZOVIA = Path("target/release/zovia")
SEC_RE = re.compile(r"^Section '(.+?)'\.\.\. (PASS|FAIL)\s*$", re.M)
TOT_RE = re.compile(r"^Total:\s*(\d+)", re.M)
PASS_RE = re.compile(r"^Pass:\s*(\d+)", re.M)
FAIL_RE = re.compile(r"^Fail:\s*(\d+)", re.M)
UNK_RE = re.compile(r"Unknown helper (\d+) at pc (\d+)")


def run_one(o: Path, timeout: float) -> dict:
    bundle = o.with_suffix(o.suffix + ".bcf-bundle")
    if bundle.exists():
        bundle.unlink()
    cmd = ["gtimeout", str(int(timeout)), str(ZOVIA),
           "--bcf", "--kernel-mode", "verify", str(o)]
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True,
                            timeout=timeout + 10)
        out = r.stdout + r.stderr
        rc = r.returncode
    except subprocess.TimeoutExpired:
        return {"obj": str(o), "outcome": "TIMEOUT",
                "elapsed": round(time.monotonic() - t0, 1)}
    secs = [{"name": n, "pass": v == "PASS"} for n, v in SEC_RE.findall(out)]
    npass = sum(1 for s in secs if s["pass"])
    nfail = len(secs) - npass
    unk = {}
    for hid, pc in UNK_RE.findall(out):
        unk.setdefault(hid, set()).add(pc)
    unk_counts = {h: len(p) for h, p in unk.items()}
    has_bundle = bundle.exists()
    bsize = bundle.stat().st_size if has_bundle else None
    # rc 124 = gtimeout kill
    outcome = "TIMEOUT" if rc == 124 else ("ERROR" if rc not in (0,) else "OK")
    return {
        "obj": str(o), "outcome": outcome, "rc": rc,
        "elapsed": round(time.monotonic() - t0, 1),
        "n_sections": len(secs), "n_pass": npass, "n_fail": nfail,
        "unknown_helpers": unk_counts,
        "has_bundle": has_bundle, "bundle_size": bsize,
        "pass_sections": [s["name"] for s in secs if s["pass"]],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--list")
    ap.add_argument("--timeout", type=float, default=90)
    ap.add_argument("--out")
    a = ap.parse_args()
    objs: list[Path] = [Path(p) for p in a.paths]
    if a.list:
        objs += [Path(l.strip()) for l in open(a.list) if l.strip()]
    objs = [o for o in objs if o.exists()]
    results = []
    agg = {"objs": 0, "pass_sec": 0, "fail_sec": 0,
           "objs_with_unk": 0, "objs_with_bundle": 0,
           "fa_pass_sec_no_bundle": 0, "fa_pass_sec_unk": 0}
    helper_hist: dict[str, int] = {}
    for i, o in enumerate(objs):
        res = run_one(o, a.timeout)
        results.append(res)
        agg["objs"] += 1
        if res["outcome"] != "OK":
            print(f"[{i+1}/{len(objs)}] {o.name}: {res['outcome']}")
            continue
        agg["pass_sec"] += res["n_pass"]
        agg["fail_sec"] += res["n_fail"]
        has_unk = bool(res["unknown_helpers"])
        if has_unk:
            agg["objs_with_unk"] += 1
        if res["has_bundle"]:
            agg["objs_with_bundle"] += 1
        else:
            # corpus = kernel-rejected by construction: PASS w/o bundle = FA
            agg["fa_pass_sec_no_bundle"] += res["n_pass"]
        if has_unk and res["n_pass"] > 0:
            agg["fa_pass_sec_unk"] += res["n_pass"]
        for h, c in res["unknown_helpers"].items():
            helper_hist[h] = helper_hist.get(h, 0) + c
        print(f"[{i+1}/{len(objs)}] {o.name}: "
              f"pass={res['n_pass']}/{res['n_sections']} "
              f"bundle={'Y' if res['has_bundle'] else 'N'} "
              f"unk={sorted(res['unknown_helpers'].items())} "
              f"{res['elapsed']}s")
    print("\n==== AGGREGATE ====")
    for k, v in agg.items():
        print(f"  {k}: {v}")
    print(f"  unknown_helper_hist (id->#distinct-pcs summed): "
          f"{dict(sorted(helper_hist.items(), key=lambda kv:-kv[1]))}")
    if a.out:
        json.dump({"agg": agg, "helper_hist": helper_hist,
                   "results": results}, open(a.out, "w"), indent=1)
        print(f"  wrote {a.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
