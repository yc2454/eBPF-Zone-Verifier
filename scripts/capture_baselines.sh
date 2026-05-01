#!/usr/bin/env bash
# Capture fresh baselines into tests/baselines/{selftest_zone,selftest_kernel,prevail}.json.
# Run from the repo root. Full JSON baselines are gitignored; only known_outcomes.json
# (the compact known-failures summary) is checked in.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BIN="./target/release/zovia"
[ -x "$BIN" ] || cargo build --release

capture_selftest() {
    local mode="$1" flag="$2" suite="$3" dir="$4"
    echo "== capturing selftest ($mode${suite:+, $suite}) =="
    $BIN -q $flag --max-insn 100000 dev selftest-suite "$dir" > /dev/null 2>&1
    python3 scripts/canonicalize_selftest_report.py \
        results/selftest/selftest_report.json \
        "tests/baselines/selftest_${mode}${suite:+_$suite}.json"
}

capture_prevail() {
    echo "== capturing prevail =="
    # Prevail moved to scripts/prevail.py (Pass 2 step 4); same JSON shape.
    scripts/prevail.py --output-dir results/prevail benchmark ~/ebpf-samples > /dev/null 2>&1
    local src
    src="$(ls -t results/prevail/prevail_benchmark_*_results.json | head -1)"
    python3 - "$src" tests/baselines/prevail.json <<'PY'
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
}

capture_selftest zone ""          ""        ./selftests/legacy/verifier
capture_selftest kernel "--kernel-mode" ""  ./selftests/legacy/verifier
capture_selftest zone ""          backport  ./selftests/legacy/verifier_backport
capture_selftest kernel "--kernel-mode" backport ./selftests/legacy/verifier_backport
capture_prevail

echo
echo "Baselines written. Diff against them with scripts/diff_baselines.sh"
