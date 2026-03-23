#!/bin/bash
# Verify that WasmCert-Coq references in Lean files contain verbatim Coq text.
#
# Convention: In Lean files, use this comment syntax:
#   -- WASMCERT: theories/opsem.v:L100-L110
#   -- | verbatim line 1 from the Coq file
#   -- | verbatim line 2 from the Coq file
#
# This script checks that the quoted text matches the WasmCert-Coq source.
# Exit 1 if any mismatches found.

set -euo pipefail

WASMCERT_DIR="${1:-/opt/WasmCert-Coq}"
LEAN_DIR="${2:-VerifiedJS}"

if [ ! -d "$WASMCERT_DIR" ]; then
  echo "WARN: WasmCert-Coq not found at $WASMCERT_DIR — skipping verification"
  exit 0
fi

ERRORS=0
REFS=0

find "$LEAN_DIR" -name "*.lean" | while read lean_file; do
  line_no=0
  while IFS= read -r line; do
    line_no=$((line_no + 1))

    # Match: -- WASMCERT: path/to/file.v:L<start>-L<end>
    if echo "$line" | grep -qE '^\s*-- WASMCERT: '; then
      REFS=$((REFS + 1))
      ref=$(echo "$line" | sed 's/.*-- WASMCERT: //')
      coq_file=$(echo "$ref" | cut -d: -f1)
      range=$(echo "$ref" | cut -d: -f2)
      start=$(echo "$range" | grep -oE '^L[0-9]+' | tr -d 'L')
      end=$(echo "$range" | grep -oE 'L[0-9]+$' | tr -d 'L')

      coq_path="$WASMCERT_DIR/$coq_file"
      if [ ! -f "$coq_path" ]; then
        echo "ERROR: $lean_file:$line_no: Coq file not found: $coq_path"
        ERRORS=$((ERRORS + 1))
        continue
      fi

      # Collect quoted lines
      quoted_lines=""
      while IFS= read -r qline; do
        if echo "$qline" | grep -qE '^\s*-- \|'; then
          content=$(echo "$qline" | sed 's/^\s*-- | //' | sed 's/^\s*-- |//')
          quoted_lines="${quoted_lines}${content}\n"
        else
          break
        fi
      done < <(tail -n +$((line_no + 1)) "$lean_file")

      if [ -z "$quoted_lines" ]; then
        echo "WARN: $lean_file:$line_no: WASMCERT ref $coq_file:L${start}-L${end} has no quoted text"
        continue
      fi

      # Extract Coq lines
      coq_text=$(sed -n "${start},${end}p" "$coq_path")
      quoted_clean=$(printf "$quoted_lines" | sed '/^$/d')
      coq_clean=$(echo "$coq_text" | sed '/^$/d')

      if [ "$quoted_clean" != "$coq_clean" ]; then
        echo "MISMATCH: $lean_file:$line_no: WASMCERT ref $coq_file:L${start}-L${end}"
        echo "  Expected (from Coq):"
        echo "$coq_clean" | head -3 | sed 's/^/    /'
        echo "  Got (in lean file):"
        echo "$quoted_clean" | head -3 | sed 's/^/    /'
        ERRORS=$((ERRORS + 1))
      fi
    fi
  done < "$lean_file"
done

echo ""
echo "=== WasmCert Reference Summary ==="
echo "References checked: $REFS"
echo "Mismatches: $ERRORS"

if [ "$ERRORS" -gt 0 ]; then
  echo "FAIL: $ERRORS WasmCert references have stale/incorrect quoted text"
  exit 1
fi
echo "PASS: All WasmCert references are up to date"
