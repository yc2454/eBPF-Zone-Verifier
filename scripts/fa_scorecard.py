#!/usr/bin/env python3
"""
Faithfulness scorecard: zovia (per ELF section) vs the per-program
kernel oracle (test_loader --per-prog, section-keyed), joined on the
ELF section name.

Inputs:
  --oracle FILE   captured VM output, blocks of:
                    === <path-with-objname> ===
                    PERPROG OK   [i] sec=<S> <name>
                    PERPROG FAIL [i] sec=<S> <name> errno=<E>
                    PERPROG SUMMARY loaded=x/n
  --list FILE     Mac absolute object paths (basename joins the oracle)
  [--zovia P] [--timeout S] [--out J]

Per ELF section S of an object:
  oracle verdict(S): the set of libbpf programs whose section_name==S.
    1:1 section  -> that program's OK/FAIL.
    multi-prog S -> kernel-accepts-S iff ALL its programs OK (a section
      "loads" only if every program in it loads); flagged `multi`.
  zovia verdict(S): PASS/FAIL from `Section 'S'... PASS|FAIL`.

Classification (the honest faithfulness table):
  CA correct-accept  kernel OK   & zovia PASS
  CR correct-reject  kernel FAIL & zovia FAIL
  FA FALSE ACCEPT    kernel FAIL & zovia PASS   <-- the number we want
  FR false-reject    kernel OK   & zovia FAIL
  plus: unmatched-zovia (section zovia verified, no libbpf program),
        unmatched-oracle (libbpf program's section zovia didn't report).
`multi`-tagged rows are counted but reported separately (one zovia
verdict vs several kernel programs — inherently coarser).
"""
from __future__ import annotations
import argparse, json, re, subprocess, sys, time
from pathlib import Path
from collections import defaultdict

ZOVIA = "target/release/zovia"
SEC_RE = re.compile(r"^Section '(.+?)'\.\.\. (PASS|FAIL)\s*$", re.M)
PP_RE = re.compile(r"^PERPROG (OK|FAIL)\s+\[\d+\] sec=(\S+) (\S+)(?: errno=(\d+))?",
                   re.M)
HDR_RE = re.compile(r"^=== .*?/([^/ ]+) ===\s*$", re.M)


def parse_oracle(path: str) -> dict:
    """obj basename -> {section: [(name, ok_bool, errno)]}"""
    txt = Path(path).read_text(errors="replace")
    out: dict = {}
    cur = None
    for line in txt.splitlines():
        h = HDR_RE.match(line)
        if h:
            cur = h.group(1)
            out.setdefault(cur, {})
            continue
        m = PP_RE.match(line)
        if m and cur is not None:
            ok = m.group(1) == "OK"
            sec, name = m.group(2), m.group(3)
            errno = int(m.group(4)) if m.group(4) else 0
            out[cur].setdefault(sec, []).append((name, ok, errno))
    return out


def run_zovia(zov: str, obj: Path, timeout: float) -> dict:
    """section -> (passed_bool, reason_or_None)"""
    try:
        r = subprocess.run(
            ["gtimeout", str(int(timeout)), zov, "-q", "--bcf",
             "--kernel-mode", "verify", str(obj)],
            capture_output=True, text=True, timeout=timeout + 10)
    except subprocess.TimeoutExpired:
        return {}
    out = r.stdout + r.stderr
    verd = {s: (v == "PASS") for s, v in SEC_RE.findall(out)}
    reasons: dict = {}
    in_f = False
    for ln in out.splitlines():
        if "--- FAILURES ---" in ln:
            in_f = True
            continue
        if in_f:
            m = re.match(r"^\s+(\S+):\s*(.+)$", ln)
            if m:
                reasons[m.group(1)] = m.group(2)
    return {s: (p, reasons.get(s)) for s, p in verd.items()}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--oracle", required=True)
    ap.add_argument("--list", required=True)
    ap.add_argument("--zovia", default=ZOVIA)
    ap.add_argument("--timeout", type=float, default=150)
    ap.add_argument("--out")
    a = ap.parse_args()

    oracle = parse_oracle(a.oracle)
    objs = [Path(l.strip()) for l in open(a.list) if l.strip()]
    agg = defaultdict(int)
    fa_list, fr_list, rows = [], [], []

    for obj in objs:
        base = obj.name
        if not obj.exists() or base not in oracle:
            print(f"[skip] {base} (no oracle or file)")
            continue
        ksec = oracle[base]
        zsec = run_zovia(a.zovia, obj, a.timeout)
        if not zsec:
            print(f"[skip] {base} (zovia no output / timeout)")
            continue
        for sec, progs in ksec.items():
            multi = len(progs) > 1
            kernel_ok = all(p[1] for p in progs)
            if sec not in zsec:
                agg["unmatched_oracle"] += 1
                continue
            zpass, zreason = zsec[sec]
            tag = "multi" if multi else "1:1"
            if kernel_ok and zpass:
                cls = "CA"
            elif (not kernel_ok) and (not zpass):
                cls = "CR"
            elif (not kernel_ok) and zpass:
                cls = "FA"
                fa_list.append((base, sec, [p[0] for p in progs],
                                [p[2] for p in progs if not p[1]]))
            else:
                cls = "FR"
                fr_list.append((base, sec, [p[0] for p in progs], zreason))
            agg[f"{cls}_{tag}"] += 1
            agg[cls] += 1
            rows.append((base, sec, tag, cls))
        for sec in zsec:
            if sec not in ksec:
                agg["unmatched_zovia"] += 1
        print(f"[ok] {base}: "
              f"CA={agg['CA']} CR={agg['CR']} FA={agg['FA']} FR={agg['FR']}"
              f" (running totals)")

    print("\n==== FAITHFULNESS SCORECARD ====")
    for k in ("CA", "CR", "FA", "FR"):
        print(f"  {k}: {agg[k]}  "
              f"(1:1={agg[f'{k}_1:1']}, multi={agg[f'{k}_multi']})")
    print(f"  unmatched_oracle(libbpf prog, zovia silent): "
          f"{agg['unmatched_oracle']}")
    print(f"  unmatched_zovia(zovia sec, no libbpf prog): "
          f"{agg['unmatched_zovia']}")
    if fa_list:
        print("\n  *** FALSE ACCEPTS (kernel REJECT, zovia PASS) ***")
        for base, sec, names, errnos in fa_list:
            print(f"   {base} sec={sec} progs={names} kernel_errno={errnos}")
    else:
        print("\n  *** ZERO FALSE ACCEPTS in scored set ***")
    print(f"\n  false-rejects: {len(fr_list)} "
          f"(kernel OK, zovia FAIL — faithfulness-of-reason gap)")
    if a.out:
        json.dump({"agg": dict(agg), "fa": fa_list, "fr": fr_list,
                   "rows": rows}, open(a.out, "w"), indent=1)
        print(f"  wrote {a.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
