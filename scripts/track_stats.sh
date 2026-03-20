#!/bin/bash
cd /opt/verifiedjs
export PATH=/opt/elan/bin:/usr/local/bin:$PATH
export ELAN_HOME=/opt/elan

STATS_FILE=/opt/verifiedjs/logs/stats.csv
mkdir -p /opt/verifiedjs/logs

# Header if new file
if [ ! -f "$STATS_FILE" ]; then
  echo "timestamp,sorry_count,e2e_pass,e2e_fail,lean_files,lean_loc,theorems_proved,theorems_sorry,theorems_todo,build_ok" > "$STATS_FILE"
fi

TS=$(date -Iseconds)
SORRY=$(grep -rc "sorry" --include="*.lean" VerifiedJS/ 2>/dev/null | awk -F: "{s+=\$2} END {print s+0}")
E2E_PASS=$(bash scripts/run_e2e.sh 2>/dev/null | grep "^PASS" | wc -l)
E2E_FAIL=$(bash scripts/run_e2e.sh 2>/dev/null | grep "^FAIL" | wc -l)
LEAN_FILES=$(find VerifiedJS/ -name "*.lean" | wc -l)
LEAN_LOC=$(cat VerifiedJS/**/*.lean VerifiedJS/*.lean 2>/dev/null | wc -l)
PROVED=$(grep -rn "^theorem\|^private theorem\|^lemma\|^private lemma" --include="*.lean" VerifiedJS/Proofs/ 2>/dev/null | wc -l)
SORRY_THMS=$(grep -A20 "^theorem\|^private theorem\|^lemma\|^private lemma" --include="*.lean" VerifiedJS/Proofs/ 2>/dev/null | grep -c "sorry" || echo 0)
TODO_THMS=$(grep -c "^-- theorem\|^-- lemma" VerifiedJS/Proofs/*.lean 2>/dev/null || echo 0)
BUILD=$(lake build 2>&1 | grep -q "successfully" && echo 1 || echo 0)

echo "$TS,$SORRY,$E2E_PASS,$E2E_FAIL,$LEAN_FILES,$LEAN_LOC,$PROVED,$SORRY_THMS,$TODO_THMS,$BUILD" >> "$STATS_FILE"
