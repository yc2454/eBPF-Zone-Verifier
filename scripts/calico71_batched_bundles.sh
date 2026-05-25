#!/bin/bash
# Persistent batched bundle build for calico-71.
#
# Memory safety: previous full --jobs 8 run consumed 100GB+ RAM and froze
# the Mac (memory 2026-05-21). This wrapper runs bench_e2e.py in
# small batches with --jobs 2 + --cache-bundles, so:
#   - per-batch peak memory bounded (only --jobs 2 concurrent zovia)
#   - bookkeeping via .bcf-bundle mtime: fresh bundles skipped on rerun
#   - status TSV tracks which batches completed
#   - safe to Ctrl-C and resume (next run skips done bundles)
#
# Usage:
#   scripts/calico71_batched_bundles.sh [BATCH_SIZE] [JOBS] [TIMEOUT]
# Default: BATCH_SIZE=8 JOBS=2 TIMEOUT=300

set -u
BATCH=${1:-8}
JOBS=${2:-2}
TIMEOUT=${3:-300}

LIST=/tmp/calico71_paths.txt
STATUS=bench/calico71/bundle_status.tsv
BUNDLE_DIR=/Users/yalucai/BCF/bpf-progs/calico

if [ ! -f "$LIST" ]; then
  echo "ERROR: $LIST missing — generate via:" >&2
  echo "  awk -F'\t' 'NR>1 {print \"$BUNDLE_DIR/\"\$1}' bench/calico71/2026-05-21_f4f853c.tsv > $LIST" >&2
  exit 1
fi

mkdir -p "$(dirname "$STATUS")"
[ -f "$STATUS" ] || echo -e "batch\tobjs_in_batch\tbundles_built\telapsed_s\ttimestamp" > "$STATUS"

TOTAL=$(wc -l < "$LIST" | tr -d ' ')
echo "[batched] $TOTAL objects, batch=$BATCH, jobs=$JOBS, timeout=${TIMEOUT}s"

i=0
batch_num=0
while [ $i -lt $TOTAL ]; do
  batch_num=$((batch_num + 1))
  BATCH_FILE=$(mktemp /tmp/calico71_batch_XXXXXX.txt)
  trap "rm -f $BATCH_FILE" EXIT
  sed -n "$((i+1)),$((i+BATCH))p" "$LIST" > "$BATCH_FILE"
  N=$(wc -l < "$BATCH_FILE" | tr -d ' ')

  # Count bundles already fresh (skip-eligible) BEFORE this batch
  pre_count=0
  while read obj; do
    b="$obj.bcf-bundle"
    [ -f "$b" ] && [ "$b" -nt "./target/release/zovia" ] && pre_count=$((pre_count+1))
  done < "$BATCH_FILE"

  echo ""
  echo "=== batch $batch_num  objs $((i+1))..$((i+N))  ($pre_count/$N already fresh) ==="
  t0=$(date +%s)

  python3 scripts/bench_e2e.py \
    --list "$BATCH_FILE" \
    --jobs "$JOBS" \
    --timeout "$TIMEOUT" \
    --no-kernel-test \
    --cache-bundles \
    --out /tmp/bench_phase1_batch.tsv 2>&1 | tail -8

  t1=$(date +%s)
  elapsed=$((t1 - t0))

  # Count newly built (fresh) bundles after
  post_count=0
  while read obj; do
    b="$obj.bcf-bundle"
    [ -f "$b" ] && post_count=$((post_count+1))
  done < "$BATCH_FILE"

  built=$((post_count - pre_count))
  echo "[batched] batch $batch_num done: built=$built/$N elapsed=${elapsed}s"
  echo -e "$batch_num\t$N\t$built\t$elapsed\t$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$STATUS"

  rm -f "$BATCH_FILE"
  i=$((i + BATCH))

  # brief pause to let memory release between batches
  sleep 2
done

# Final summary
total_bundles=$(find "$BUNDLE_DIR" -name "*.bcf-bundle" | wc -l | tr -d ' ')
echo ""
echo "=== ALL BATCHES DONE ==="
echo "bundles on disk: $total_bundles / $TOTAL"
echo "status log: $STATUS"
