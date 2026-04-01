#!/bin/bash
# Copy root Claude auth to all agent configs
for agent in jsspec wasmspec proof supervisor; do
  cp ~/.claude/.credentials.json /opt/verifiedjs/.claude-$agent/.credentials.json
  chown $agent:pipeline /opt/verifiedjs/.claude-$agent/.credentials.json
  chmod 600 /opt/verifiedjs/.claude-$agent/.credentials.json
  echo "$agent: auth refreshed"
done
echo "done"
