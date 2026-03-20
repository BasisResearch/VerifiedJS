#!/bin/bash
cd /opt/verifiedjs
export PATH=/opt/elan/bin:/usr/local/bin:$PATH
export ELAN_HOME=/opt/elan

STATS_FILE=/opt/verifiedjs/logs/stats.csv
mkdir -p /opt/verifiedjs/logs

if [ ! -f "$STATS_FILE" ]; then
  echo "timestamp,sorry_count,e2e_pass,e2e_fail,lean_files,lean_loc,theorems_total,theorems_sorry,build_ok" > "$STATS_FILE"
fi

TS=$(date -Iseconds)
SORRY=$(grep -rc "sorry" --include="*.lean" VerifiedJS/ 2>/dev/null | awk -F: "{s+=\$2} END {print s+0}")
E2E_OUT=$(bash scripts/run_e2e.sh 2>/dev/null | tail -1)
E2E_PASS=$(echo "$E2E_OUT" | grep -oP "\d+ passed" | grep -oP "\d+" || echo 0)
E2E_FAIL=$(echo "$E2E_OUT" | grep -oP "\d+ failed" | grep -oP "\d+" || echo 0)
LEAN_FILES=$(find VerifiedJS/ -name "*.lean" | wc -l)
LEAN_LOC=$(find VerifiedJS/ -name "*.lean" -exec cat {} + 2>/dev/null | wc -l)
THMS_TOTAL=$(grep -rcE "^(private )?(theorem|lemma) " --include="*.lean" VerifiedJS/Proofs/ 2>/dev/null | awk -F: "{s+=\$2} END {print s+0}")
THMS_SORRY=$(grep -l "sorry" VerifiedJS/Proofs/*.lean 2>/dev/null | while read f; do grep -cE "^(private )?(theorem|lemma) " "$f"; done | awk "{s+=\$1} END {print s+0}")
BUILD=$(lake build 2>&1 | grep -q "successfully" && echo 1 || echo 0)

echo "$TS,$SORRY,$E2E_PASS,$E2E_FAIL,$LEAN_FILES,$LEAN_LOC,$THMS_TOTAL,$THMS_SORRY,$BUILD" >> "$STATS_FILE"
