#!/bin/bash
FILE=/opt/verifiedjs/logs/agent_liveness.csv
mkdir -p /opt/verifiedjs/logs
if [ ! -f "$FILE" ]; then
  echo "timestamp,jsspec,wasmspec,proof,supervisor" > "$FILE"
fi
TS=$(date -Iseconds)
JS=0; WS=0; PR=0; SU=0

for agent in jsspec wasmspec proof supervisor; do
  alive=0
  if pgrep -u $agent -f claude >/dev/null 2>&1; then
    # Process exists - but is it actually working or just hanging on auth?
    latest=$(ls -t /var/log/verifiedjs/${agent}_*.log 2>/dev/null | head -1)
    if [ -n "$latest" ]; then
      # Check if last log line is an auth error
      last_line=$(tail -1 "$latest" 2>/dev/null)
      if echo "$last_line" | grep -qi "not logged in\|login\|auth\|credential"; then
        alive=0  # hanging on auth = dead
      else
        alive=1
      fi
    else
      alive=1  # running, no log yet = assume alive
    fi
  fi
  case $agent in
    jsspec) JS=$alive;;
    wasmspec) WS=$alive;;
    proof) PR=$alive;;
    supervisor) SU=$alive;;
  esac
done

echo "$TS,$JS,$WS,$PR,$SU" >> "$FILE"
tail -2001 "$FILE" > "$FILE.tmp" && mv "$FILE.tmp" "$FILE"
