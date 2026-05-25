#!/bin/bash
# Phase 2 watcher: polls bench/calico71/bundle_status.tsv and runs
# kernel-load phase 2 on each completed batch as soon as it lands.
#
# Bookkeeping: bench/calico71/phase2_done.txt records which batch
# numbers have been phase-2'd. Per-batch results are written to
# bench/calico71/2026-05-23_phase2_batch{N}.tsv.
#
# Idempotent: safe to Ctrl-C and rerun; already-processed batches
# are skipped.
#
# Usage: scripts/calico71_phase2_watcher.sh [POLL_INTERVAL_SEC]
# Default poll interval: 60s.

set -u
POLL=${1:-60}

STATUS=bench/calico71/bundle_status.tsv
PATHS=/tmp/calico71_paths.txt
DONE=bench/calico71/phase2_done.txt
OUTDIR=bench/calico71

mkdir -p "$OUTDIR"
touch "$DONE"

if [ ! -f "$PATHS" ]; then
  echo "ERROR: $PATHS missing" >&2
  exit 1
fi

echo "[watcher] starting; poll=${POLL}s; status=$STATUS; done=$DONE"

# We need to track which objs each batch covers; the batched runner
# uses BATCH_SIZE=8 by default and slices objs sequentially. We
# reconstruct that mapping from /tmp/calico71_paths.txt.
BATCH_SIZE=8

while true; do
  # No status file yet → wait
  if [ ! -f "$STATUS" ]; then
    sleep "$POLL"
    continue
  fi

  # Find batches in status TSV that we haven't phase-2'd yet.
  # Skip header (line 1).
  changed=0
  while IFS=$'\t' read -r batch_num objs_in_batch built elapsed ts; do
    [ "$batch_num" = "batch" ] && continue
    if grep -qE "^${batch_num}\$" "$DONE"; then
      continue  # already done
    fi
    # Slice the corresponding object lines from PATHS.
    # Batch N covers lines (N-1)*BATCH_SIZE+1 .. (N-1)*BATCH_SIZE+objs_in_batch
    start=$(( (batch_num - 1) * BATCH_SIZE + 1 ))
    end=$(( (batch_num - 1) * BATCH_SIZE + objs_in_batch ))
    BATCH_LIST=$(mktemp /tmp/calico71_p2_batch_XXXXXX.txt)
    sed -n "${start},${end}p" "$PATHS" > "$BATCH_LIST"

    n=$(wc -l < "$BATCH_LIST" | tr -d ' ')
    echo ""
    echo "[watcher] phase 2 on batch $batch_num (objs $start..$end, n=$n)"

    OUT="$OUTDIR/2026-05-23_phase2_batch${batch_num}.tsv"
    python3 scripts/bench_e2e.py \
      --list "$BATCH_LIST" \
      --skip-bundle-build \
      --kernel-test \
      --vm-jobs 4 \
      --per-call-timeout 60 \
      --phase2-timeout 1200 \
      --out "$OUT" 2>&1 | tail -6

    if [ -f "$OUT" ]; then
      full=$(awk -F'\t' 'NR>1 && $7=="True"' "$OUT" | wc -l | tr -d ' ')
      echo "[watcher] batch $batch_num phase 2 done: $full/$n FULL load → $OUT"
      echo "$batch_num" >> "$DONE"
      changed=1
    else
      echo "[watcher] batch $batch_num phase 2 FAILED (no $OUT)" >&2
    fi
    rm -f "$BATCH_LIST"
  done < "$STATUS"

  # Cumulative summary
  if [ "$changed" = "1" ]; then
    cum_full=0
    cum_total=0
    for f in "$OUTDIR"/2026-05-23_phase2_batch*.tsv; do
      [ -f "$f" ] || continue
      n=$(awk -F'\t' 'NR>1' "$f" | wc -l | tr -d ' ')
      ff=$(awk -F'\t' 'NR>1 && $7=="True"' "$f" | wc -l | tr -d ' ')
      cum_total=$((cum_total + n))
      cum_full=$((cum_full + ff))
    done
    echo "[watcher] cumulative: $cum_full / $cum_total FULL kernel load"
  fi

  # Stop condition: all 9 batches done (covers 69 objs, 8*8+5)
  if [ "$(wc -l < "$DONE" | tr -d ' ')" -ge 9 ]; then
    echo "[watcher] all batches phase-2'd — exiting"
    break
  fi

  # Phase 1 finished and no new batches → exit gracefully.
  if ! pgrep -f "calico71_batched_bundles" >/dev/null; then
    # Drain one more pass; if no changes, exit.
    if [ "$changed" = "0" ]; then
      echo "[watcher] phase 1 runner gone, no new work — exiting"
      break
    fi
  fi

  sleep "$POLL"
done

echo "[watcher] done. final results in $OUTDIR/2026-05-23_phase2_batch*.tsv"
