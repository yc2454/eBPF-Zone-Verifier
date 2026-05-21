#!/usr/bin/env python3
"""End-to-end BCF bundle benchmark harness.

For each .o in the input list:
  Phase 1 (parallel, zovia-side): build a unified bundle by running
    zovia 3× with ZOVIA_BUNDLE_KEEP=1 — flag-OFF, flag-ON AND,
    flag-ON OR. Each mode contributes different rejection-discharge
    entries (kernel writes dedup by hash via write_bundle).
  Phase 2 (sequential, kernel-side via cloudlab→VM ssh chain):
    ship anchor + bundle, run test_loader, parse loaded=N/M.

Output: TSV with columns
  obj  zovia_ok  bundle_bytes  zovia_elapsed  kernel_loaded  kernel_total

Usage:
  scripts/bench_e2e.py --list /tmp/calico_repr_list.txt --jobs 8 \\
      --out /tmp/bench_calico71.tsv --kernel-test

  # skip the kernel-load step (just build bundles + measure zovia):
  scripts/bench_e2e.py --list ... --no-kernel-test

  # rerun only the kernel-load step against existing bundles:
  scripts/bench_e2e.py --list ... --skip-bundle-build --kernel-test
"""
from __future__ import annotations

import argparse
import os
import re
import shlex
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Optional


# ───── Phase 1: parallel zovia bundle build ─────────────────────────


def build_one(args):
    obj_path, zovia_bin, timeout = args
    bundle = f"{obj_path}.bcf-bundle"
    try:
        if os.path.exists(bundle):
            os.remove(bundle)
    except OSError:
        pass

    modes = [
        ("OFF", {}),
        ("AND", {"ZOVIA_KERNEL_ENGINE": "1", "ZOVIA_KERNEL_ENGINE_AND": "1"}),
        ("OR",  {"ZOVIA_KERNEL_ENGINE": "1"}),
    ]
    t0 = time.time()
    notes = []
    for label, extra_env in modes:
        env = {**os.environ, "ZOVIA_BUNDLE_KEEP": "1", **extra_env}
        cmd = [zovia_bin, "-q", "--bcf", "--kernel-mode", "verify", obj_path]
        try:
            r = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=timeout)
            # we only care that the bundle file ends up populated;
            # individual mode rc=1 is fine if other modes added entries
            notes.append(f"{label}:rc{r.returncode}")
        except subprocess.TimeoutExpired:
            notes.append(f"{label}:TO")
    elapsed = time.time() - t0
    ok = os.path.exists(bundle)
    size = os.path.getsize(bundle) if ok else 0
    return (obj_path, ok, size, elapsed, ",".join(notes))


def phase1_build_bundles(objs: list[str], zovia: str, jobs: int, timeout: int) -> list[tuple]:
    print(f"[bench] phase 1: building bundles for {len(objs)} objects "
          f"(jobs={jobs}, per-obj timeout={timeout}s)", file=sys.stderr)
    work = [(o, zovia, timeout) for o in objs]
    results: list[tuple] = []
    with ProcessPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(build_one, w): w[0] for w in work}
        for i, fut in enumerate(as_completed(futs), 1):
            results.append(fut.result())
            if i % 5 == 0 or i == len(objs):
                print(f"[bench] phase 1: {i}/{len(objs)}", file=sys.stderr)
    return results


# ───── Phase 2: sequential VM kernel-side load test ─────────────────


def map_to_vm_path(local_path: str) -> str:
    """Translate Mac-local path to the VM's /root/bcf/... view.

    The cloudlab virtiofs mount exposes /users/yc1795/BCF at /root/bcf
    inside the VM. The calico repr list uses /Users/yalucai/BCF/... on
    Mac, which is the SAME directory tree (rsync'd or symlinked).
    Replace the Mac prefix wholesale to preserve the full subdirectory
    structure (e.g. bpf-progs/calico/<file>).
    """
    return local_path.replace("/Users/yalucai/BCF", "/root/bcf", 1)


def phase2_kernel_load(objs: list[str], cloudlab_host: str, timeout: int) -> dict[str, tuple]:
    """For each .o, scp the bundle to cloudlab (its virtiofs is the VM's
    /root/bcf), then ssh to VM and run test_loader --per-prog (gives a
    deterministic 'PERPROG SUMMARY loaded=N/M' line regardless of
    success/failure).

    Caveat: --per-prog isolates each program (no subprog stitching) so
    bundle-discharged hashes may not match → bundle-helped programs
    can show as failing here. Whole-object load is the realistic kernel
    test; this gives a uniform N/M number for aggregation. Whole-object
    success will be a strict subset improvement reflected in the
    `whole_object_full_load` extra column.

    Returns map: obj → (per_prog_loaded, per_prog_total, whole_obj_full,
    first_fail_name).
    """
    print(f"[bench] phase 2: kernel-side load for {len(objs)} objects "
          f"(sequential, host={cloudlab_host})", file=sys.stderr)
    out: dict[str, tuple] = {}

    # Step A: rsync bundles to cloudlab in one batch (fast, single ssh).
    # Mac /Users/yalucai/BCF/bpf-progs/calico/<obj>.bcf-bundle  →
    # cloudlab /users/yc1795/BCF/bpf-progs/calico/<obj>.bcf-bundle
    bundles = [f"{o}.bcf-bundle" for o in objs if os.path.exists(f"{o}.bcf-bundle")]
    if not bundles:
        print("[bench] phase 2: no bundles to ship", file=sys.stderr)
        return out

    # Group by parent dir for rsync efficiency
    by_dir: dict[str, list[str]] = {}
    for b in bundles:
        by_dir.setdefault(os.path.dirname(b), []).append(b)
    for d, group in by_dir.items():
        # Map Mac dir → cloudlab dir
        # /Users/yalucai/BCF/bpf-progs/calico → /users/yc1795/BCF/bpf-progs/calico
        cl_dir = d.replace("/Users/yalucai/BCF", "/users/yc1795/BCF")
        print(f"[bench] rsync {len(group)} bundles → {cloudlab_host}:{cl_dir}", file=sys.stderr)
        subprocess.run(
            ["rsync", "-aq", *group, f"{cloudlab_host}:{cl_dir}/"],
            check=False, timeout=300,
        )

    # Step B: write a small VM-side runner script and exec it via nested ssh.
    # For each object, run TWO test_loader invocations:
    #   1. whole-object (the realistic kernel test; SUCCESS line iff all loaded)
    #   2. --per-prog (always emits 'PERPROG SUMMARY loaded=N/M' line)
    vm_script_lines = ["#!/bin/sh", "set -u"]
    for o in objs:
        vm_obj = map_to_vm_path(o)
        vm_bundle = f"{vm_obj}.bcf-bundle"
        vm_script_lines.append(f"echo '===OBJ {os.path.basename(o)}==='")
        vm_script_lines.append(
            f"/root/bcf/build/test_loader --type classifier {vm_obj} {vm_bundle} 2>&1 | "
            f"grep -E 'SUCCESS:|libbpf: prog .* failed to load:|programs:' | head -10"
        )
        vm_script_lines.append("echo '---perprog---'")
        vm_script_lines.append(
            f"/root/bcf/build/test_loader --type classifier --per-prog {vm_obj} {vm_bundle} 2>&1 | "
            f"grep -E 'PERPROG SUMMARY' | tail -1"
        )
    vm_script = "\n".join(vm_script_lines)
    cmd = (
        f"ssh -i /users/yc1795/BCF/imgs/bookworm.id_rsa -p 10023 "
        f"-o BatchMode=yes -o StrictHostKeyChecking=no root@localhost 'bash -s'"
    )
    print(f"[bench] phase 2: invoking test_loader (whole+per-prog) on {len(objs)} objects", file=sys.stderr)
    r = subprocess.run(
        ["ssh", "-o", "BatchMode=yes", cloudlab_host, cmd],
        input=vm_script, capture_output=True, text=True, timeout=timeout,
    )
    raw = r.stdout
    sections = re.split(r"^===OBJ ([^=]+)===\n", raw, flags=re.M)
    for i in range(1, len(sections), 2):
        name = sections[i].strip()
        body = sections[i + 1] if i + 1 < len(sections) else ""
        # parse
        whole_full = bool(re.search(r"^SUCCESS:", body, flags=re.M))
        first_fail = ""
        mf = re.search(r"libbpf: prog '([^']+)': failed to load:", body)
        if mf:
            first_fail = mf.group(1)
        m = re.search(r"PERPROG SUMMARY\s+loaded=(\d+)/(\d+)", body)
        if m:
            pp_loaded, pp_total = int(m.group(1)), int(m.group(2))
        else:
            pp_loaded, pp_total = None, None
        # parse total programs from whole-object output for fallback
        if pp_total is None:
            mt = re.search(r"programs:\s+(\d+)\s+in object", body)
            if mt:
                pp_total = int(mt.group(1))
        for o in objs:
            if os.path.basename(o) == name:
                out[o] = (pp_loaded, pp_total, whole_full, first_fail)
                break
    return out


# ───── Driver ───────────────────────────────────────────────────────


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--list", required=True, help="file of .o paths, one per line")
    ap.add_argument("--zovia", default="./target/release/zovia")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=300, help="per-object zovia timeout (s)")
    ap.add_argument("--cloudlab", help="cloudlab ssh target (e.g. yc1795@ms0802.utah.cloudlab.us). "
                    "if unset, read from /Users/yalucai/bpf-next-zovia git remote.")
    ap.add_argument("--out", default="/tmp/bench_e2e.tsv")
    ap.add_argument("--kernel-test", action="store_true", default=True,
                    help="run phase 2 kernel-load test (default on)")
    ap.add_argument("--no-kernel-test", dest="kernel_test", action="store_false")
    ap.add_argument("--skip-bundle-build", action="store_true",
                    help="skip phase 1; reuse existing bundles on disk")
    args = ap.parse_args()

    # Resolve cloudlab from git remote if not provided
    if args.kernel_test and not args.cloudlab:
        r = subprocess.run(
            ["git", "-C", "/Users/yalucai/bpf-next-zovia", "remote", "get-url", "cloudlab"],
            capture_output=True, text=True, check=True,
        )
        url = r.stdout.strip()
        args.cloudlab = url.split(":")[0]

    with open(args.list) as f:
        objs = [ln.strip() for ln in f if ln.strip() and not ln.startswith("#")]

    print(f"[bench] {len(objs)} objects", file=sys.stderr)
    if args.cloudlab:
        print(f"[bench] cloudlab={args.cloudlab}", file=sys.stderr)

    # Phase 1
    if not args.skip_bundle_build:
        p1 = phase1_build_bundles(objs, args.zovia, args.jobs, args.timeout)
        p1_by_obj = {r[0]: r for r in p1}
    else:
        p1_by_obj = {o: (o, os.path.exists(f"{o}.bcf-bundle"),
                         os.path.getsize(f"{o}.bcf-bundle") if os.path.exists(f"{o}.bcf-bundle") else 0,
                         0.0, "reused") for o in objs}

    # Phase 2
    if args.kernel_test:
        ok_objs = [o for o in objs if p1_by_obj[o][1]]
        kresults = phase2_kernel_load(ok_objs, args.cloudlab, timeout=600)
    else:
        kresults = {}

    # Emit TSV
    with open(args.out, "w") as f:
        f.write("obj\tzovia_ok\tbundle_bytes\tzovia_elapsed\tpp_loaded\tpp_total\twhole_full\tfirst_fail\tnotes\n")
        for o in sorted(objs):
            obj, ok, size, elapsed, notes = p1_by_obj[o]
            pp_l, pp_t, whole, ff = (None, None, False, "")
            if o in kresults:
                pp_l, pp_t, whole, ff = kresults[o]
            pp_l_s = str(pp_l) if pp_l is not None else "-"
            pp_t_s = str(pp_t) if pp_t is not None else "-"
            f.write(f"{os.path.basename(obj)}\t{ok}\t{size}\t{elapsed:.1f}\t"
                    f"{pp_l_s}\t{pp_t_s}\t{whole}\t{ff}\t{notes}\n")

    # Summary
    n_ok = sum(1 for r in p1_by_obj.values() if r[1])
    n_whole = sum(1 for v in kresults.values() if v[2])
    n_pp_full = sum(1 for v in kresults.values() if v[0] is not None and v[0] == v[1] and v[1] is not None)
    n_pp_partial = sum(1 for v in kresults.values() if v[0] is not None and v[1] is not None and 0 < v[0] < v[1])
    n_pp_zero = sum(1 for v in kresults.values() if v[0] == 0)
    print(f"\n[bench] phase 1: bundle built for {n_ok}/{len(objs)}", file=sys.stderr)
    if args.kernel_test:
        print(f"[bench] phase 2: whole-object FULL kernel load: {n_whole}/{len(kresults)}", file=sys.stderr)
        print(f"[bench]          per-prog (lower-bound): full={n_pp_full} "
              f"partial={n_pp_partial} zero={n_pp_zero}", file=sys.stderr)
    print(f"[bench] wrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
