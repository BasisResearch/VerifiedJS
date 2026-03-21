#!/bin/bash
FILE=/opt/verifiedjs/logs/agent_liveness.csv
mkdir -p /opt/verifiedjs/logs
if [ ! -f "$FILE" ]; then
  echo "timestamp,jsspec,wasmspec,proof,supervisor" > "$FILE"
fi
TS=$(date -Iseconds)
JS=0; WS=0; PR=0; SU=0
pgrep -u jsspec -f claude >/dev/null 2>&1 && JS=1
pgrep -u wasmspec -f claude >/dev/null 2>&1 && WS=1
pgrep -u proof -f claude >/dev/null 2>&1 && PR=1
pgrep -u supervisor -f claude >/dev/null 2>&1 && SU=1
echo "$TS,$JS,$WS,$PR,$SU" >> "$FILE"
# Keep last 2000 entries (~33 hours at 1/min)
tail -2001 "$FILE" > "$FILE.tmp" && mv "$FILE.tmp" "$FILE"
