#!/bin/bash
# Watchdog: refresh root auth, then copy to agents if needed

LOG=/opt/verifiedjs/logs/auth_watchdog.log

# Step 1: Refresh root token by running claude briefly
# This triggers the OAuth token refresh using the refresh_token
timeout 30 claude --print -p "auth refresh ping" < /dev/null > /dev/null 2>&1
if [ $? -ne 0 ]; then
  echo "$(date -Iseconds) ROOT-AUTH-FAIL: claude could not refresh token. Manual login required." >> "$LOG"
  exit 1
fi

# Step 2: Check each agent, copy fresh creds if they are failing
for agent in jsspec wasmspec proof supervisor; do
  result=$(sudo -u $agent bash -c "export CLAUDE_CONFIG_DIR=/opt/verifiedjs/.claude-$agent && timeout 15 claude --print -p hi < /dev/null 2>&1" | head -1)
  
  if echo "$result" | grep -qi "not logged in\|error\|login\|credential\|unauthorized"; then
    cp ~/.claude/.credentials.json /opt/verifiedjs/.claude-$agent/.credentials.json
    chown $agent:pipeline /opt/verifiedjs/.claude-$agent/.credentials.json
    chmod 600 /opt/verifiedjs/.claude-$agent/.credentials.json
    pkill -u $agent -f claude 2>/dev/null
    echo "$(date -Iseconds) FIXED: $agent re-authed and restarted" >> "$LOG"
  fi
done
