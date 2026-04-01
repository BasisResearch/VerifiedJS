#!/bin/bash
cd /opt/verifiedjs
export ELAN_HOME=/opt/elan PATH=/opt/elan/bin:/usr/local/bin:/usr/bin:/bin
export HOME=/opt/verifiedjs

OUT=$(bash scripts/lake_build_concise.sh 2>&1)
STATUS=$?
TS=$(date -Iseconds)

# Save latest result as JSON
python3 -c "
import json, sys
text = sys.stdin.read()
errors = []
for line in text.splitlines():
    if \"error:\" in line.lower() or \"✖\" in line or \"build failed\" in line:
        errors.append(line.strip())
# Parse summary line
summary = \"\"
for line in text.splitlines():
    if \"lake build:\" in line:
        summary = line.strip()
        break
json.dump({
    \"timestamp\": \"$TS\",
    \"status\": \"PASS\" if $STATUS == 0 else \"FAIL\",
    \"errors\": errors[:20],
    \"summary\": summary,
    \"full_output\": text[-3000:],
}, open(\"/opt/verifiedjs/logs/build_status.json\", \"w\"))
" <<< "$OUT"

chmod 644 /opt/verifiedjs/logs/build_status.json
