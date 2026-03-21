#!/bin/bash
cd /opt/verifiedjs
export ELAN_HOME=/opt/elan PATH=/opt/elan/bin:/usr/local/bin:$PATH

STATS_FILE=/opt/verifiedjs/logs/stats.csv
mkdir -p logs

if [ ! -f "$STATS_FILE" ]; then
  echo "timestamp,sorry_count,e2e_total,lean_files,lean_loc,theorems_total,build_ok" > "$STATS_FILE"
fi

TS=$(date -Iseconds)
SORRY=$(grep -rc "sorry" --include="*.lean" VerifiedJS/ 2>/dev/null | awk -F: "{s+=\$2} END {print s+0}")
E2E_TOTAL=$(ls tests/e2e/*.js 2>/dev/null | wc -l)
LEAN_FILES=$(find VerifiedJS/ -name "*.lean" 2>/dev/null | wc -l)
LEAN_LOC=$(find VerifiedJS/ -name "*.lean" -exec cat {} + 2>/dev/null | wc -l)
THMS_TOTAL=$(grep -rcE "^(private )?(theorem|lemma) " --include="*.lean" VerifiedJS/Proofs/ 2>/dev/null | awk -F: "{s+=\$2} END {print s+0}")

# Quick build check — just see if binary exists and is recent
BUILD=0
if [ -f .lake/build/bin/verifiedjs ]; then
  AGE=$(( $(date +%s) - $(stat -c %Y .lake/build/bin/verifiedjs) ))
  [ "$AGE" -lt 7200 ] && BUILD=1
fi

echo "$TS,$SORRY,$E2E_TOTAL,$LEAN_FILES,$LEAN_LOC,$THMS_TOTAL,$BUILD" >> "$STATS_FILE"
