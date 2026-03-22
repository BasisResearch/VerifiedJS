#!/bin/bash
LOG=/opt/verifiedjs/logs/auth_watchdog.log

# Step 1: Check if root token is near expiry (< 2 hours)
REMAINING=$(python3 -c "
import json, datetime
creds = json.load(open(\"$HOME/.claude/.credentials.json\"))
exp = creds.get(\"claudeAiOauth\", {}).get(\"expiresAt\", 0)
now = datetime.datetime.now().timestamp() * 1000
print(int((exp - now) / 1000 / 60))
" 2>/dev/null || echo "0")

if [ "$REMAINING" -lt 120 ]; then
  echo "$(date -Iseconds) Token expires in ${REMAINING}m, refreshing..." >> "$LOG"
  cd /opt/verifiedjs && python3 scripts/claude_refresh.py >> "$LOG" 2>&1
fi

# Step 2: Copy creds to any agent that is failing auth
for agent in jsspec wasmspec proof supervisor; do
  # Check if agent has a recent auth failure in run logs
  latest=$(ls -t /var/log/verifiedjs/${agent}_*.log 2>/dev/null | head -1)
  if [ -n "$latest" ]; then
    if grep -qi "not logged in\|login\|credential" "$latest" 2>/dev/null; then
      cp ~/.claude/.credentials.json /opt/verifiedjs/.claude-$agent/.credentials.json
      chown $agent:pipeline /opt/verifiedjs/.claude-$agent/.credentials.json
      chmod 600 /opt/verifiedjs/.claude-$agent/.credentials.json
      pkill -u $agent -f claude 2>/dev/null
      echo "$(date -Iseconds) FIXED: $agent re-authed" >> "$LOG"
    fi
  fi
done
