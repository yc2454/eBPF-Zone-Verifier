#!/bin/bash
# Capture the kernel's QUERIED cond_hash set for one object's whole-object load.
# Loads the object's on-disk full bundle via the SAME loader bench uses
# (test_loader, whole-object), then reads every `bcf_canonical_hash:` dmesg
# line (the kernel logs EVERY discharge query). Output: zero-padded 16-hex
# sorted-unique hash list + the load err code on stderr.
#
# Usage: capture_queried.sh <obj_local_path> <out_hashfile>
# Env: HOST, VMKEY (defaults = current cloudlab setup; hostname rotates — pass
# HOST explicitly when it does).
set -u
OBJ="$1"; OUT="$2"
HOST="${HOST:-yc1795@ms0802.utah.cloudlab.us}"
VMKEY="${VMKEY:-/users/yc1795/BCF/imgs/bookworm.id_rsa}"
SSHO="-o ConnectTimeout=20 -o StrictHostKeyChecking=no"
BASE="$(basename "$OBJ")"
BUNDLE="$OBJ.bcf-bundle"
[ -s "$BUNDLE" ] || { echo "no bundle: $BUNDLE" >&2; exit 1; }

scp $SSHO "$BUNDLE" "$HOST":/tmp/cq.bundle >/dev/null 2>&1
# 600s outer budget: two-hop scp of a 20-30MB no_log bundle + the 300s
# per-load inner timeout must BOTH fit (200s silently truncated the big
# objects -> empty capture, masquerading as "queried=0").
timeout 600 ssh $SSHO "$HOST" "
  scp -o StrictHostKeyChecking=no -i $VMKEY -P 10023 /tmp/cq.bundle root@localhost:/root/bcf/sweep/cq.bundle >/dev/null 2>&1
  ssh -o StrictHostKeyChecking=no -i $VMKEY -p 10023 root@localhost '
    dmesg -C >/dev/null 2>&1
    timeout 300 /root/bcf/build/test_loader /root/bcf/bpf-progs/calico/$BASE /root/bcf/sweep/cq.bundle >/tmp/cq.out 2>&1
    grep -E \"err=|loaded\" /tmp/cq.out | tail -2 >&2
    dmesg | grep -oE \"bcf_canonical_hash: buf.len=[0-9]+ hash=0x[0-9a-f]+\" | grep -oE \"0x[0-9a-f]+\$\"
  '
" 2> >(sed "s/^/[$BASE] /" >&2) | sed 's/^0x//' | awk '{printf "%016s\n",$0}' | sort -u > "$OUT"
echo "[$BASE] queried: $(wc -l < "$OUT" | tr -d ' ') unique hashes" >&2
