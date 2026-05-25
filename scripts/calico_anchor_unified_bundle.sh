#!/bin/bash
# Builds a kernel-loadable BCF bundle for the calico anchor object
# (clang-15_-O1_felix_bin_bpf_to_tnl_debug_v6.o, 7 programs).
#
# Iterates over all 7 programs and runs `zovia --bcf` once per
# program — `--bcf` enables zovia's internal thorough mode by default,
# so each invocation already spawns the multi-pass children that
# previously had to be driven from the outside.
#
# The legacy three-mode driver lives at
# `calico_anchor_unified_bundle_legacy.sh` for archival reference
# (manually setting ZOVIA_KERNEL_ENGINE / _AND and looping).
#
# Usage:
#   ANCHOR=/path/to/anchor.o ZOVIA=./target/release/zovia ./calico_anchor_unified_bundle.sh

set -u
ZOVIA=${ZOVIA:-./target/release/zovia}
ANCHOR=${ANCHOR:-/tmp/anchor_to_tnl_debug.o}
BUNDLE=$ANCHOR.bcf-bundle

PROGS=(
  calico_tc_main
  calico_tc_skb_accepted_entrypoint
  calico_tc_skb_new_flow_entrypoint
  calico_tc_skb_icmp_inner_nat
  calico_tc_skb_send_icmp_replies
  calico_tc_host_ct_conflict
  calico_tc_skb_drop
)

rm -f "$BUNDLE"
echo "=== thorough-mode unified bundle build for $ANCHOR ==="
for prog in "${PROGS[@]}"; do
  echo ""
  echo "### $prog ###"
  # ZOVIA_BUNDLE_KEEP=1 prevents the per-invocation wipe so each
  # program's contribution accumulates into the same bundle file.
  ZOVIA_BUNDLE_KEEP=1 \
    "$ZOVIA" --bcf --kernel-mode verify "$ANCHOR" --func "$prog" 2>&1 \
    | grep -E 'Verified|bundle:|FAILURE|TIMEOUT|Aborting|^--- pass' \
    | tail -5 | sed 's/^/    /'
done

echo ""
echo "=== final bundle ==="
ls -l "$BUNDLE" 2>/dev/null
