#!/bin/bash
# Watchdog: check if agents can auth, if not copy root creds and restart them
for agent in jsspec wasmspec proof supervisor; do
  # Quick auth test
  result=$(sudo -u $agent bash -c "export CLAUDE_CONFIG_DIR=/opt/verifiedjs/.claude-$agent && timeout 10 claude --print -p hi < /dev/null 2>&1" | head -1)
  if echo "$result" | grep -qi "not logged in\|error\|login\|auth"; then
    # Copy fresh creds from root
    cp ~/.claude/.credentials.json /opt/verifiedjs/.claude-$agent/.credentials.json
    chown $agent:pipeline /opt/verifiedjs/.claude-$agent/.credentials.json
    chmod 600 /opt/verifiedjs/.claude-$agent/.credentials.json
    echo "$(date -Iseconds) AUTH-FIX: $agent re-authed" >> /opt/verifiedjs/logs/auth_watchdog.log
    
    # Kill and let cron restart
    pkill -u $agent -f claude 2>/dev/null
    echo "$(date -Iseconds) AUTH-FIX: $agent killed for restart" >> /opt/verifiedjs/logs/auth_watchdog.log
  fi
done
