#!/bin/bash
# zovia memory cop: polls ps and SIGKILLs any zovia process whose RSS
# exceeds a threshold. Lets us run phase 1 at high --jobs without the
# risk of one pathological program OOM-thrashing the box.
#
# Usage:
#   scripts/zovia_memory_cop.sh [RSS_CAP_MB] [POLL_SEC]
# Defaults: 4096 MB, 5s poll.
#
# The cop logs each kill (and current top RSS) to /tmp/zovia_memory_cop.log
# so we can later inspect which objects blew up.

set -u
CAP_MB=${1:-4096}
POLL=${2:-5}
LOG=/tmp/zovia_memory_cop.log

echo "[cop] starting; cap=${CAP_MB}MB; poll=${POLL}s; log=$LOG" | tee -a "$LOG"

while true; do
  # ps reports RSS in KB.
  # We match `./target/release/zovia` to scope to bench workers and
  # avoid accidentally killing other rust binaries.
  while IFS= read -r line; do
    rss_kb=$(echo "$line" | awk '{print $1}')
    pid=$(echo "$line" | awk '{print $2}')
    obj=$(echo "$line" | grep -oE '/[^ ]+\.o' | head -1)
    rss_mb=$((rss_kb / 1024))
    if [ "$rss_mb" -gt "$CAP_MB" ]; then
      ts=$(date -u +%Y-%m-%dT%H:%M:%SZ)
      echo "[cop] KILL pid=$pid rss=${rss_mb}MB > cap=${CAP_MB}MB  obj=$obj  ts=$ts" | tee -a "$LOG"
      kill -9 "$pid" 2>/dev/null
    fi
  done < <(ps -ax -o rss,pid,command | awk '/[\.]\/target\/release\/zovia / {print}')
  sleep "$POLL"
done
