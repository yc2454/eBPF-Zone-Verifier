#!/usr/bin/env bash
# Run the baseline-check sweep on ONLY the 584 files added during the
# 2026-05-03 skipped-bucket expansion session (per
# selftests/expectations_session_new.json).
#
# Default workflow during FA/FR closure work: see
# memory/feedback_sweep_only_new_files.md. Use the full sweep
# (`dev selftest-baseline-check-upstream vendor/linux selftests/baseline_v6.15_full.json`)
# only when changing cross-cutting primitives.
set -euo pipefail
cd "$(dirname "$0")/.."

NEW_LIST="selftests/expectations_session_new.json"
FULL_BASELINE="selftests/baseline_v6.15_full.json"
FILTERED="${TMPDIR:-/tmp}/baseline_new_only.json"

python3 - "$NEW_LIST" "$FULL_BASELINE" "$FILTERED" <<'PY'
import json, sys
new_list = json.load(open(sys.argv[1]))["files"]
baseline = json.load(open(sys.argv[2]))
keep = set(new_list)
baseline["files"] = {k: v for k, v in baseline["files"].items() if k in keep}
json.dump(baseline, open(sys.argv[3], "w"), indent=2)
print(f"[sweep_new_only] filtered baseline: {len(baseline['files'])} files", file=sys.stderr)
PY

exec ./target/release/zovia -q dev selftest-baseline-check-upstream vendor/linux "$FILTERED" "$@"
