#!/bin/bash
set -euo pipefail

AGENT_NAME="${1:?Usage: runner.sh <jsspec|wasmspec|proof|supervisor>}"
PROJECT="/opt/verifiedjs"
PROMPT_FILE="$PROJECT/agents/$AGENT_NAME/prompt.md"
LOG_FILE="$PROJECT/agents/$AGENT_NAME/log.md"
RUN_LOG="/var/log/verifiedjs/${AGENT_NAME}_$(date +%Y%m%d_%H%M%S).log"
LOCK_FILE="/var/lock/verifiedjs-${AGENT_NAME}.lock"
MAX_TURNS=200
TIMEOUT_SECS=3600

if [[ ! "$AGENT_NAME" =~ ^(jsspec|wasmspec|proof|supervisor)$ ]]; then
  echo "ERROR: Unknown agent" >&2; exit 1
fi

if [[ "$(whoami)" != "$AGENT_NAME" ]]; then
  echo "ERROR: must run as $AGENT_NAME, not $(whoami)" >&2; exit 1
fi

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "ERROR: Prompt not found: $PROMPT_FILE" >&2; exit 1
fi

exec 9>"$LOCK_FILE"
if ! flock -n 9; then
  echo "$(date -Iseconds) SKIP: already running" >> "$LOG_FILE"
  exit 0
fi

mkdir -p "$(dirname "$RUN_LOG")"

{
  echo ""
  echo "## Run: $(date -Iseconds)"
  echo ""
} >> "$LOG_FILE"

export HOME="$PROJECT"
export PATH="/opt/elan/bin:/usr/local/bin:/usr/bin:/bin"
export ELAN_HOME="/opt/elan"
export CLAUDE_CONFIG_DIR="$PROJECT/.claude-$AGENT_NAME"

cd "$PROJECT"

# Use stream-json for real-time output, pipe through jq to extract text
timeout "$TIMEOUT_SECS" stdbuf -oL claude \
  --print \
  --verbose \
  --output-format stream-json \
  --max-turns "$MAX_TURNS" \
  --dangerously-skip-permissions \
  -p "You are the $AGENT_NAME agent working in $(pwd). Date: $(date -Iseconds).
Read agents/$AGENT_NAME/prompt.md for your full instructions, then execute them.
Log progress to agents/$AGENT_NAME/log.md.
NEVER break the build." \
  < /dev/null 2>&1 \
  | while IFS= read -r line; do
      echo "$line" >> "$RUN_LOG"
    done || {
    EXIT_CODE=$?
    echo "$(date -Iseconds) EXIT: code $EXIT_CODE" >> "$LOG_FILE"
    [[ $EXIT_CODE -eq 124 ]] && echo "$(date -Iseconds) TIMEOUT" >> "$LOG_FILE"
  }

echo "$(date -Iseconds) DONE" >> "$LOG_FILE"
exec 9>&-
