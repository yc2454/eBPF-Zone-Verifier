#!/bin/bash
# Q2 batch: for every object in a list —
#   1. build the FULL thorough bundle (current default config) fresh
#   2. capture the kernel's queried-hash set (whole-object load; doubles as a
#      per-object load validation of the current default config)
#   3. build the 4 per-pass isolated bundles + hash sets (pass_surgery.sh)
# Then mincover.py answers: smallest pass config covering every queried set.
#
# Serial (jobs 1) on purpose — no_log builds OOM under parallelism.
# Usage: q2_batch.sh <list_file> <outdir> [timeout_s=1800]
set -u
LIST="$1"; OUTDIR="$2"; TMO="${3:-1800}"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
ZOVIA="$ROOT/target/release/zovia"
mkdir -p "$OUTDIR"
PASSED=(); FAILED=()

while read -r OBJ; do
  [ -z "$OBJ" ] && continue
  BASE="$(basename "$OBJ" .o)"
  echo "===== $BASE ====="
  # 1. fresh thorough bundle, default config (no experimental knobs)
  rm -f "$OBJ.bcf-bundle"
  (
    unset ZOVIA_KERNEL_ENGINE ZOVIA_KERNEL_ENGINE_AND ZOVIA_BCF_FAITHFUL_FOLD \
          ZOVIA_BCF_FOLD_PRENARROW ZOVIA_BCF_REPLAY ZOVIA_BCF_ANCESTOR_DEPTH \
          ZOVIA_EXP_FLAG_SKIP_BASE ZOVIA_EXP_LOOP_ENTRY_BASE \
          ZOVIA_EXP_SKIP_LOOP_HEADER_UNSAFE ZOVIA_EXP_LOOP_SUFFIX_BASE \
          ZOVIA_BCF_PRECISION_FAITHFUL ZOVIA_BCF_THOROUGH_PASS
    timeout "$TMO" "$ZOVIA" -q --bcf --kernel-mode verify "$OBJ" \
      > "$OUTDIR/$BASE.thorough.log" 2>&1
  )
  if [ ! -s "$OBJ.bcf-bundle" ]; then
    echo "  THOROUGH BUILD FAILED/TIMEOUT — skip"; FAILED+=("$BASE(build)"); continue
  fi
  python3 "$HERE/bundle_tool.py" hashes "$OBJ.bcf-bundle" \
    | awk '{printf "%016s\n",$0}' | sort -u > "$OUTDIR/$BASE.full.hashes"
  # 2. queried set (whole-object load via test_loader; also validates load)
  bash "$HERE/capture_queried.sh" "$OBJ" "$OUTDIR/$BASE.queried.hashes" \
    2> "$OUTDIR/$BASE.capture.err"
  if grep -qE "err=0" "$OUTDIR/$BASE.capture.err"; then
    PASSED+=("$BASE")
  else
    FAILED+=("$BASE(load:$(grep -oE 'err=-?[0-9]+' "$OUTDIR/$BASE.capture.err" | tail -1))")
  fi
  # 3. per-pass surgery (clobbers + finally removes the sidecar)
  bash "$HERE/pass_surgery.sh" "$OBJ" "$OUTDIR" "$TMO"
done < "$LIST"

echo
echo "=== LOAD VALIDATION (default config, fresh bundles) ==="
echo "PASS (${#PASSED[@]}): ${PASSED[*]:-}"
echo "FAIL (${#FAILED[@]}): ${FAILED[*]:-}"
echo
echo "=== MIN-COVER ==="
OBJS=$(sed 's#.*/##; s#\.o$##' "$LIST" | tr '\n' ' ')
python3 "$HERE/mincover.py" "$OUTDIR" $OBJS
