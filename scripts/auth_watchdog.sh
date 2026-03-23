#!/bin/bash
LOG=/opt/verifiedjs/logs/auth_watchdog.log

# Step 1: Refresh root token if near expiry
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

# Step 2: Check each agent, fix and RESTART if failing
for agent in jsspec wasmspec proof supervisor; do
  latest=$(ls -t /var/log/verifiedjs/${agent}_*.log 2>/dev/null | head -1)
  if [ -n "$latest" ]; then
    # Check for auth failure in the run log
    if grep -q "authentication_error\|Invalid authentication\|not logged in" "$latest" 2>/dev/null; then
      # Copy fresh creds
      cp ~/.claude/.credentials.json /opt/verifiedjs/.claude-$agent/.credentials.json
      chown $agent:pipeline /opt/verifiedjs/.claude-$agent/.credentials.json
      chmod 600 /opt/verifiedjs/.claude-$agent/.credentials.json
      
      # Kill the dead process
      pkill -u $agent -f claude 2>/dev/null
      sleep 1
      
      # Restart immediately (dont wait for cron)
      nohup sudo -u $agent /opt/verifiedjs/agents/runner.sh $agent > /dev/null 2>&1 &
      
      echo "$(date -Iseconds) FIXED+RESTARTED: $agent" >> "$LOG"
    fi
  fi
done
