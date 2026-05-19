#!/usr/bin/env python3
"""
Diff an l3_sweep.py results JSON against BCF's accept oracle
(accepted_prog_index.json), per source, enforcing the <=-BCF invariant.

The corpus is 512 objects ALL wrongly rejected by the stock verifier;
accepted_prog_index.json is the curated/dedup'd set of variants BCF
itself loads. Our pipeline is derivative of BCF -> at best a SUBSET of
BCF's accepts. Accepting an object BCF does NOT accept is a RED FLAG
(measurement artifact / soundness), never a celebrated win.

A "real win" here = l3_outcome ACCEPT *with our bundle attached*
(bundle_exists True). An L3 ACCEPT with no bundle = kernel loaded it
natively => attribute to the newer kernel, NOT to us.

Usage:
  scripts/diff_vs_bcf.py RESULTS.json [RESULTS2.json ...] \
      [--accepted /Users/yalucai/BCF/bpf-progs/accepted_prog_index.json]
"""
from __future__ import annotations

import argparse
import json
import os
from collections import Counter, defaultdict
from pathlib import Path

DEFAULT_ACCEPTED = Path("/Users/yalucai/BCF/bpf-progs/accepted_prog_index.json")


def accepted_variant_set(accepted: dict, source: str) -> set[str]:
    """Flatten {group.o:[variant.o,...]} -> set of accepted variant basenames."""
    s: set[str] = set()
    for variants in accepted.get(source, {}).items():
        for v in variants[1]:
            s.add(os.path.basename(v))
    return s


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("results", nargs="+", type=Path)
    ap.add_argument("--accepted", type=Path, default=DEFAULT_ACCEPTED)
    args = ap.parse_args()

    accepted = json.load(args.accepted.open())

    records: list[dict] = []
    for rp in args.results:
        records.extend(json.load(rp.open()))

    by_src: dict[str, list[dict]] = defaultdict(list)
    for r in records:
        by_src[r["source"]].append(r)

    red_flags: list[tuple[str, str]] = []

    for src in sorted(by_src):
        recs = by_src[src]
        acc = accepted_variant_set(accepted, src)
        n = len(recs)
        l2 = Counter(r["l2_outcome"] for r in recs)
        l3 = Counter(r["l3_outcome"] for r in recs)

        # "our win" = L3 ACCEPT *with our bundle*
        our_wins = [r for r in recs
                    if r["l3_outcome"] == "ACCEPT" and r.get("bundle_exists")]
        native = [r for r in recs
                  if r["l3_outcome"] == "ACCEPT" and not r.get("bundle_exists")]

        def base(r):
            return os.path.basename(r["program"])

        we_inter_bcf = [r for r in our_wins if base(r) in acc]
        we_not_bcf = [r for r in our_wins if base(r) not in acc]
        bcf_we_miss = sorted(acc - {base(r) for r in our_wins})

        print(f"\n===== {src} =====")
        print(f"  objects swept       : {n}")
        print(f"  BCF accepts (oracle): {len(acc)} variants")
        print(f"  L2 {dict(l2)}")
        print(f"  L3 {dict(l3)}")
        print(f"  our wins (L3 ACCEPT + our bundle): {len(our_wins)}")
        print(f"  L3 ACCEPT bundle-less (kernel-native, NOT our win): {len(native)}")
        print(f"  we ∩ BCF : {len(we_inter_bcf)}")
        print(f"  we miss BCF (subset, OK / below BCF): {len(bcf_we_miss)}")
        print(f"  we accept, BCF doesn't (RED FLAG): {len(we_not_bcf)}")
        for r in we_not_bcf:
            print(f"      !! {base(r)}  bundle={r.get('bundle_size')}B")
            red_flags.append((src, base(r)))
        if native:
            print("  bundle-less L3 ACCEPT (attribute to kernel, not us):")
            for r in native[:10]:
                print(f"      ~ {base(r)}")

        # L2-accept but L3-reject = discharge failure (most informative)
        disc_fail = [r for r in recs
                     if r["l2_outcome"] == "ACCEPT" and r["l3_outcome"] != "ACCEPT"]
        if disc_fail:
            print(f"  L2-ACCEPT -> L3-REJECT (discharge fail): {len(disc_fail)}")
            for r in disc_fail[:5]:
                print(f"      x {base(r)} -> {r['l3_outcome']}")

        # dominant L2 fail reason
        fr = Counter(r["l2_fail_reason"] for r in recs
                     if r["l2_outcome"] != "ACCEPT" and r["l2_fail_reason"])
        for reason, c in fr.most_common(3):
            print(f"  L2-fail x{c}: {reason[:140]}")

    print("\n===== <=-BCF INVARIANT =====")
    if red_flags:
        print(f"  RED FLAGS ({len(red_flags)}) — investigate per "
              f"benchmark-semantics (kernel-version? harness? soundness?):")
        for src, b in red_flags:
            print(f"    {src}/{b}")
    else:
        print("  CLEAN: no object accepted that BCF rejects. We are ⊆ BCF.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
