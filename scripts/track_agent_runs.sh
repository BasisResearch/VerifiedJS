#!/bin/bash
# Called by runner.sh or cron to record agent run start/stop times
# Usage: track_agent_runs.sh <agent> <start|stop>
AGENT="${1:?}" 
EVENT="${2:?}"
FILE=/opt/verifiedjs/logs/agent_runs.csv
mkdir -p /opt/verifiedjs/logs
if [ ! -f "$FILE" ]; then
  echo "timestamp,agent,event" > "$FILE"
fi
echo "$(date -Iseconds),$AGENT,$EVENT" >> "$FILE"
