#!/bin/bash
# Cron job: run test262 sample, save results for dashboard + agents
cd /opt/verifiedjs
export ELAN_HOME=/opt/elan PATH=/opt/elan/bin:/usr/local/bin:$PATH

RESULTS_FILE=/opt/verifiedjs/logs/test262_latest.txt
STATS_FILE=/opt/verifiedjs/logs/test262_history.csv
mkdir -p logs

# Header if new
if [ ! -f "$STATS_FILE" ]; then
  echo "timestamp,pass,fail,xfail,skip,total" > "$STATS_FILE"
fi

# Run with 200 sample (takes ~5-10 min)
OUT=$(bash scripts/run_test262_compare.sh --fast --sample 200 --seed stats 2>&1)

# Save full output for agents to read
echo "$OUT" > "$RESULTS_FILE"

# Parse summary
SUMMARY=$(echo "$OUT" | grep "TEST262_SUMMARY")
PASS=$(echo "$SUMMARY" | grep -oP "pass=\K\d+" || echo 0)
FAIL=$(echo "$SUMMARY" | grep -oP "fail=\K\d+" || echo 0)
XFAIL=$(echo "$SUMMARY" | grep -oP "xfail=\K\d+" || echo 0)
SKIP=$(echo "$SUMMARY" | grep -oP "skip=\K\d+" || echo 0)
TOTAL=$(echo "$SUMMARY" | grep -oP "total=\K\d+" || echo 0)

echo "$(date -Iseconds),$PASS,$FAIL,$XFAIL,$SKIP,$TOTAL" >> "$STATS_FILE"

# Also save failure details for agents
echo "$OUT" | grep "TEST262_FAIL" | head -50 > /opt/verifiedjs/logs/test262_failures.txt

# Make readable by agents
chmod 644 "$RESULTS_FILE" "$STATS_FILE" /opt/verifiedjs/logs/test262_failures.txt 2>/dev/null
python3 /opt/verifiedjs/scripts/test262_summarize.py
