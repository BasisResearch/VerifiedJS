#!/bin/bash
# Generate a sorry report for the project.
# Exits nonzero if sorry count exceeds threshold.

set -euo pipefail

REPORT="SORRY_REPORT.md"
THRESHOLD="${SORRY_THRESHOLD:-100}"

echo "# Sorry Report ($(date))" > "$REPORT"
echo "" >> "$REPORT"

grep -rn "sorry" --include="*.lean" VerifiedJS/ 2>/dev/null | \
  grep -v -e "-- sorry OK:" | \
  grep -v "sorry_report" | \
  grep -v -e "-- PROVED:" | \
  while IFS=: read -r file line content; do
    name=$(head -n "$line" "$file" | grep -oE '(theorem|lemma|def)\s+\S+' | tail -1 || echo "unknown")
    echo "- [ ] \`$file:$line\` — \`$name\` — \`$(echo "$content" | xargs)\`" >> "$REPORT"
  done

COUNT=$(grep -c "^\- \[" "$REPORT" 2>/dev/null || echo "0")
echo "" >> "$REPORT"
echo "**Total: $COUNT sorries**" >> "$REPORT"

echo "Sorry count: $COUNT (threshold: $THRESHOLD)"

if [ "$COUNT" -gt "$THRESHOLD" ]; then
  echo "ERROR: sorry count ($COUNT) exceeds threshold ($THRESHOLD)"
  exit 1
fi
