#!/bin/bash
# Quick test262 run for stats tracking — deterministic sample
cd /opt/verifiedjs
export ELAN_HOME=/opt/elan PATH=/opt/elan/bin:/usr/local/bin:$PATH
OUT=$(bash scripts/run_test262_compare.sh --fast --sample 200 --seed stats 2>&1)
SUMMARY=$(echo "$OUT" | grep "TEST262_SUMMARY")
PASS=$(echo "$SUMMARY" | grep -oP "pass=\K\d+")
FAIL=$(echo "$SUMMARY" | grep -oP "fail=\K\d+")
SKIP=$(echo "$SUMMARY" | grep -oP "skip=\K\d+")
TOTAL=$(echo "$SUMMARY" | grep -oP "total=\K\d+")
echo "${PASS:-0},${FAIL:-0},${SKIP:-0},${TOTAL:-0}"
