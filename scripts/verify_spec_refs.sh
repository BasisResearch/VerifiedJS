#!/bin/bash
# Verify SPEC: references in Lean files contain verbatim spec text.
set -euo pipefail

SPEC="${1:-spec.md}"
LEAN_DIR="${2:-VerifiedJS}"
ERRORS=0
REFS=0
TMPFILE=$(mktemp)

if [ ! -f "$SPEC" ]; then
  echo "ERROR: spec not found: $SPEC"; exit 1
fi

for lean_file in $(find "$LEAN_DIR" -name "*.lean" 2>/dev/null); do
  while IFS= read -r line_info; do
    line_no=$(echo "$line_info" | cut -d: -f1)
    line=$(echo "$line_info" | cut -d: -f2-)

    spec_range=$(echo "$line" | grep -oE 'L[0-9]+-L[0-9]+' || true)
    [ -z "$spec_range" ] && continue
    start=$(echo "$spec_range" | grep -oE '^L[0-9]+' | tr -d 'L')
    end=$(echo "$spec_range" | grep -oE 'L[0-9]+$' | tr -d 'L')
    REFS=$((REFS + 1))

    # Collect -- | lines after this line
    next=$((line_no + 1))
    quoted=""
    while IFS= read -r qline; do
      if echo "$qline" | grep -qE '^\s*-- \|'; then
        content=$(echo "$qline" | sed 's/^\s*-- | \?//')
        quoted="${quoted}${content}
"
      else
        break
      fi
    done < <(sed -n "${next},\$p" "$lean_file")

    [ -z "$quoted" ] && continue

    spec_text=$(sed -n "${start},${end}p" "$SPEC")
    q_clean=$(echo "$quoted" | sed '/^$/d')
    s_clean=$(echo "$spec_text" | sed '/^$/d')

    if [ "$q_clean" != "$s_clean" ]; then
      echo "MISMATCH $lean_file:$line_no L${start}-L${end}"
      ERRORS=$((ERRORS + 1))
    fi

    # Track covered lines
    seq "$start" "$end" >> "$TMPFILE"
  done < <(grep -n "SPEC: L[0-9]" "$lean_file" 2>/dev/null || true)
done

COVERED=$(sort -u "$TMPFILE" | wc -l)
TOTAL=$(wc -l < "$SPEC")
rm -f "$TMPFILE"

echo "Spec coverage: $COVERED/$TOTAL lines ($(( COVERED * 100 / TOTAL ))%), $REFS refs, $ERRORS mismatches"
[ "$ERRORS" -gt 0 ] && exit 1 || exit 0
