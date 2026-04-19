#!/usr/bin/env bash
# Re-run the three baseline suites, canonicalize, and diff against tests/baselines/*.
# Exit non-zero if any diff is non-empty. Run from the repo root.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

BIN="./target/release/zovia"
[ -x "$BIN" ] || cargo build --release

for f in tests/baselines/selftest_zone.json \
         tests/baselines/selftest_kernel.json \
         tests/baselines/selftest_zone_backport.json \
         tests/baselines/selftest_kernel_backport.json \
         tests/baselines/prevail.json; do
    if [ ! -f "$f" ]; then
        echo "Missing $f — run tests/baselines/capture_baseline.sh first." >&2
        exit 2
    fi
done

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fail=0

run_selftest() {
    local mode="$1"
    local flag="$2"
    local suite="$3"
    local dir="$4"
    local tag="${mode}${suite:+_$suite}"
    local baseline="tests/baselines/selftest_${tag}.json"
    echo "== selftest ($mode${suite:+, $suite}) =="
    $BIN -q $flag --max-insn 100000 selftest-suite "$dir" > "$TMP/$tag.log" 2>&1
    python3 tests/baselines/canonicalize.py results/selftest/selftest_report.json "$TMP/selftest_$tag.json"
    if ! diff -u "$baseline" "$TMP/selftest_$tag.json"; then
        echo "DIFF in selftest $tag"
        fail=1
    fi
}

run_prevail() {
    echo "== prevail =="
    $BIN -q prevail-benchmark ~/ebpf-samples > "$TMP/prevail.log" 2>&1
    local src
    src="$(ls -t results/prevail/prevail_benchmark_*_results.json | head -1)"
    python3 - "$src" "$TMP/prevail.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
canon = {
    'summary': {k: v for k, v in d['summary'].items() if k not in ('duration_secs', 'filters')},
    'results': sorted([{'file': r['file'], 'project': r.get('project'),
                        'expected_accept': r['expected_accept'],
                        'passed': r['passed'], 'matches': r['matches_expectation']}
                       for r in d['results']],
                      key=lambda x: (x.get('project') or '', x['file'])),
}
json.dump(canon, open(sys.argv[2], 'w'), indent=2, sort_keys=True)
open(sys.argv[2], 'a').write('\n')
PY
    if ! diff -u tests/baselines/prevail.json "$TMP/prevail.json"; then
        echo "DIFF in prevail"
        fail=1
    fi
}

run_selftest zone ""          ""        ./selftests/legacy/verifier
run_selftest kernel "--kernel-mode" ""  ./selftests/legacy/verifier
run_selftest zone ""          backport  ./selftests/legacy/verifier_backport
run_selftest kernel "--kernel-mode" backport ./selftests/legacy/verifier_backport
run_prevail

if [ $fail -eq 0 ]; then
    echo
    echo "All baselines match."
else
    echo
    echo "BASELINE DIFF DETECTED — review above."
    exit 1
fi
