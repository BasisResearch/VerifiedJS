#!/bin/bash
# Verify that all spec references in Lean files contain verbatim spec text.
#
# Convention: In Lean files, use this comment syntax:
#   -- SPEC: L1234-L1240
#   -- | verbatim line 1 from spec.md
#   -- | verbatim line 2 from spec.md
#
# This script checks that the quoted text matches spec.md exactly.
# Exit 1 if any mismatches found.

set -euo pipefail

SPEC="${1:-spec.md}"
LEAN_DIR="${2:-VerifiedJS}"

if [ ! -f "$SPEC" ]; then
  echo "ERROR: spec file not found: $SPEC"
  exit 1
fi

ERRORS=0
REFS=0
COVERED_LINES=""

find "$LEAN_DIR" -name "*.lean" | while read lean_file; do
  line_no=0
  while IFS= read -r line; do
    line_no=$((line_no + 1))

    # Match: -- SPEC: L<start>-L<end>
    if echo "$line" | grep -qE '^\s*-- SPEC: L[0-9]+-L[0-9]+'; then
      REFS=$((REFS + 1))
      spec_range=$(echo "$line" | grep -oE 'L[0-9]+-L[0-9]+')
      start=$(echo "$spec_range" | grep -oE '^L[0-9]+' | tr -d 'L')
      end=$(echo "$spec_range" | grep -oE 'L[0-9]+$' | tr -d 'L')

      # Collect the -- | lines that follow
      quoted_lines=""
      next_line=$((line_no + 1))
      while IFS= read -r qline; do
        if echo "$qline" | grep -qE '^\s*-- \|'; then
          content=$(echo "$qline" | sed 's/^\s*-- | //' | sed 's/^\s*-- |//')
          quoted_lines="${quoted_lines}${content}\n"
          next_line=$((next_line + 1))
        else
          break
        fi
      done < <(tail -n +$((line_no + 1)) "$lean_file")

      if [ -z "$quoted_lines" ]; then
        echo "WARN: $lean_file:$line_no: SPEC ref L${start}-L${end} has no quoted text (add -- | lines)"
        continue
      fi

      # Extract spec lines
      spec_text=$(sed -n "${start},${end}p" "$SPEC")
      quoted_clean=$(printf "$quoted_lines" | sed '/^$/d')
      spec_clean=$(echo "$spec_text" | sed '/^$/d')

      # Compare
      if [ "$quoted_clean" != "$spec_clean" ]; then
        echo "MISMATCH: $lean_file:$line_no: SPEC ref L${start}-L${end}"
        echo "  Expected (from spec.md):"
        echo "$spec_clean" | head -3 | sed 's/^/    /'
        echo "  Got (in lean file):"
        echo "$quoted_clean" | head -3 | sed 's/^/    /'
        ERRORS=$((ERRORS + 1))
      fi

      # Track coverage
      for i in $(seq $start $end); do
        COVERED_LINES="$COVERED_LINES $i"
      done
    fi
  done < "$lean_file"
done

# Count coverage
TOTAL_SPEC_LINES=$(wc -l < "$SPEC")
UNIQUE_COVERED=$(echo "$COVERED_LINES" | tr ' ' '\n' | sort -un | wc -l)

echo ""
echo "=== Spec Reference Summary ==="
echo "Total spec lines: $TOTAL_SPEC_LINES"
echo "Lines covered by refs: $UNIQUE_COVERED"
echo "Coverage: $(( UNIQUE_COVERED * 100 / TOTAL_SPEC_LINES ))%"
echo "Mismatches: $ERRORS"

if [ "$ERRORS" -gt 0 ]; then
  echo "FAIL: $ERRORS spec references have stale/incorrect quoted text"
  exit 1
fi
echo "PASS: All spec references are up to date"
