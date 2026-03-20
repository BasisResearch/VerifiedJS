#!/bin/bash
LOG_DIR=/var/log/verifiedjs
for agent in jsspec wasmspec proof supervisor; do
  COUNT=$(ls -1 $LOG_DIR/${agent}_*.log 2>/dev/null | wc -l)
  if [ "$COUNT" -gt 50 ]; then
    ls -1t $LOG_DIR/${agent}_*.log | tail -n +51 | xargs rm -f
  fi
done
# Also trim agent log.md files to last 500 lines
for agent in jsspec wasmspec proof supervisor; do
  LOG=/opt/verifiedjs/agents/$agent/log.md
  LINES=$(wc -l < "$LOG" 2>/dev/null || echo 0)
  if [ "$LINES" -gt 500 ]; then
    tail -500 "$LOG" > "$LOG.tmp" && mv "$LOG.tmp" "$LOG"
    chown $agent:pipeline "$LOG" 2>/dev/null
  fi
done
