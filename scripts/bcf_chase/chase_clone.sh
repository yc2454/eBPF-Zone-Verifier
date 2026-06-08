#!/bin/bash
# Lightweight chase: clone-based bundles, classify misses against a precomputed
# superset hash set. RAM-trivial + fast (no big-bundle re-parse per iteration).
# Requires a DONOR bundle with at least one kind=2 (UNREACHABLE) entry.
#
# Usage env: SUPHASH (function's superset hash set, from build_superset.sh),
#   DONOR (any bundle w/ a kind=2 entry), HOST VMKEY OBJ PROG, ITERS, DIR.
# Outputs: $DIR/real.txt, $DIR/fake.txt and a FINAL real:engine-shape tally.
set -u
SUPHASH="${SUPHASH:?set SUPHASH=function superset hashset}"
DONOR="${DONOR:-/tmp/smoke.bundle}"
HOST="${HOST:-yc1795@ms0802.utah.cloudlab.us}"
VMKEY="${VMKEY:-/users/yc1795/BCF/imgs/bookworm.id_rsa}"
OBJ="${OBJ:-/root/bcf/bpf-progs/calico/clang-15_-O1_felix_bin_bpf_from_nat_no_log.o}"
PROG="${PROG:?set PROG=--prog name}"
DIR="${DIR:-/tmp}"; ITERS="${ITERS:-300}"
HERE="$(cd "$(dirname "$0")" && pwd)"
SSHO="-o ConnectTimeout=20 -o StrictHostKeyChecking=no"
REAL="$DIR/real.txt"; FAKE="$DIR/fake.txt"; ALL="$DIR/all.txt"
: > "$REAL"; : > "$FAKE"; : > "$ALL"

for iter in $(seq 1 "$ITERS"); do
  python3 "$HERE/bundle_tool.py" clone "$DONOR" "$ALL" "$DIR/probe.bundle" >/dev/null 2>&1
  scp $SSHO "$DIR/probe.bundle" "$HOST":/tmp/probe.bundle >/dev/null 2>&1
  OUT=$(timeout 150 ssh $SSHO "$HOST" "
    scp -o StrictHostKeyChecking=no -i $VMKEY -P 10023 /tmp/probe.bundle root@localhost:/root/bcf/sweep/probe.bundle >/dev/null 2>&1
    ssh -o StrictHostKeyChecking=no -i $VMKEY -p 10023 root@localhost '
      dmesg -C >/dev/null 2>&1
      /root/bcf/sweep/ll2_loader --prog $PROG $OBJ /root/bcf/sweep/probe.bundle >/tmp/load.out 2>&1
      grep -E \"bpf_object__load err\" /tmp/load.out | tail -1
      grep \"ZK summary. END\" /tmp/load.out | tail -1
      echo ===HASHES===
      dmesg | grep -oE \"hash=0x[0-9a-f]+ off=0\" | sed -E \"s/hash=0x([0-9a-f]+).*/\\1/\"
    '
  " 2>&1)
  ERR=$(echo "$OUT" | grep "err=")
  MISS=$(echo "$OUT" | awk '/===HASHES===/{f=1;next} f' | tail -1)
  if echo "$OUT" | grep -q "err=0"; then echo "[$iter] LOAD OK real=$(wc -l<$REAL) engine=$(wc -l<$FAKE)"; break; fi
  if [ -z "$MISS" ]; then echo "[$iter] no-hash other-fail: $ERR — stop"; echo "$OUT"|grep -i "ZK summary"; break; fi
  if grep -qix "$MISS" "$ALL"; then echo "[$iter] STUCK on $MISS (already added) — stop"; break; fi
  echo "$MISS" >> "$ALL"
  if grep -qix "$MISS" "$SUPHASH"; then echo "$MISS" >> "$REAL"; tag=real; else echo "$MISS" >> "$FAKE"; tag=ENGINE; fi
  [ $((iter % 10)) = 0 ] && echo "[$iter] real=$(wc -l<$REAL) engine=$(wc -l<$FAKE) last=$tag"
done
R=$(wc -l<"$REAL"); F=$(wc -l<"$FAKE"); T=$((R+F))
echo "=== $PROG FINAL: total=$T real=$R engine-shape=$F  ($([ $T -gt 0 ] && echo $((100*R/T))||echo 0)% generated) ==="
