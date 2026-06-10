#!/usr/bin/env python3
"""Minimal pass-config solver.

For each object: queried-hash set (from capture_queried.sh) vs the 4 per-pass
hash sets (from pass_surgery.sh). Brute-forces all 15 non-empty pass subsets
and reports, per object, every subset whose UNION covers the queried set —
plus the minimal ones — and the corpus-wide minimal config.

Soundness of the criterion: if every hash the kernel queried during the
full-bundle load is still present in the retained passes' union, the kernel
walks the identical discharge path, so the load outcome is unchanged.

Usage: mincover.py <surgery_outdir> <objbase>...
Expects per obj: <dir>/<objbase>.queried.hashes and
                 <dir>/<objbase>.pass_{baseline,a,b,c}.hashes
"""
import itertools, sys, os

PASSES = ["baseline", "a", "b", "c"]

def load(fn):
    if not os.path.exists(fn):
        return None
    return set(l.strip() for l in open(fn) if l.strip())

def main():
    d = sys.argv[1]
    objs = sys.argv[2:]
    corpus_ok = {frozenset(s) for n in range(1, 5) for s in itertools.combinations(PASSES, n)}
    for ob in objs:
        q = load(f"{d}/{ob}.queried.hashes")
        if q is None:
            print(f"{ob}: NO queried set — skip"); continue
        ph = {p: load(f"{d}/{ob}.pass_{p}.hashes") or set() for p in PASSES}
        full = set().union(*ph.values())
        missing_from_full = q - full
        ok_sets = []
        for n in range(1, 5):
            for s in itertools.combinations(PASSES, n):
                u = set().union(*(ph[p] for p in s))
                if q - missing_from_full <= u:
                    ok_sets.append(frozenset(s))
        min_n = min((len(s) for s in ok_sets), default=0)
        minimal = sorted(["+".join(sorted(s)) for s in ok_sets if len(s) == min_n])
        per_pass_unique_queried = {
            p: len((q & ph[p]) - set().union(*(ph[o] for o in PASSES if o != p)))
            for p in PASSES
        }
        print(f"{ob}: queried={len(q)}  "
              f"{'⚠️ ' + str(len(missing_from_full)) + ' queried NOT in any pass (env mismatch?)  ' if missing_from_full else ''}"
              f"minimal={minimal}  uniquely-needed-per-pass={per_pass_unique_queried}")
        corpus_ok &= set(ok_sets)
    if objs:
        min_n = min((len(s) for s in corpus_ok), default=0)
        print("\nCORPUS-WIDE viable configs:",
              sorted(["+".join(sorted(s)) for s in corpus_ok], key=len) or "NONE")
        print("CORPUS-WIDE minimal:",
              sorted(["+".join(sorted(s)) for s in corpus_ok if len(s) == min_n]) or "NONE")

if __name__ == "__main__":
    main()
