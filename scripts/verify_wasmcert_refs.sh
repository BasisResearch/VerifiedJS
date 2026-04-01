#!/bin/bash
# Verify WASMCERT: references in Lean files contain verbatim Coq text.
set -euo pipefail

WASMCERT_DIR="${1:-/opt/WasmCert-Coq}"
LEAN_DIR="${2:-VerifiedJS}"

if [ ! -d "$WASMCERT_DIR" ]; then
  echo "WARN: WasmCert-Coq not found at $WASMCERT_DIR — skipping"
  exit 0
fi

ERRORS=0
REFS=0

# Only scan files that actually have WASMCERT references (fast grep first)
for lean_file in $(grep -rl "WASMCERT:" "$LEAN_DIR" --include="*.lean" 2>/dev/null); do
  while IFS= read -r line_info; do
    line_no=$(echo "$line_info" | cut -d: -f1)
    line=$(echo "$line_info" | cut -d: -f2-)

    ref=$(echo "$line" | sed 's/.*WASMCERT: //')
    coq_file=$(echo "$ref" | cut -d: -f1)
    range=$(echo "$ref" | cut -d: -f2)
    start=$(echo "$range" | grep -oE '^L[0-9]+' | tr -d 'L')
    end=$(echo "$range" | grep -oE 'L[0-9]+$' | tr -d 'L')
    REFS=$((REFS + 1))

    coq_path="$WASMCERT_DIR/$coq_file"
    if [ ! -f "$coq_path" ]; then
      echo "ERROR: $lean_file:$line_no: Coq file not found: $coq_path"
      ERRORS=$((ERRORS + 1))
      continue
    fi

    # Collect quoted lines
    quoted=""
    while IFS= read -r qline; do
      if echo "$qline" | grep -qE '^\s*-- \|'; then
        content=$(echo "$qline" | sed 's/^\s*-- | \?//')
        quoted="${quoted}${content}
"
      else
        break
      fi
    done < <(sed -n "$((line_no + 1)),\$p" "$lean_file")

    [ -z "$quoted" ] && continue

    coq_text=$(sed -n "${start},${end}p" "$coq_path")
    q_clean=$(echo "$quoted" | sed '/^$/d')
    c_clean=$(echo "$coq_text" | sed '/^$/d')

    if [ "$q_clean" != "$c_clean" ]; then
      echo "MISMATCH $lean_file:$line_no WASMCERT $coq_file:L${start}-L${end}"
      ERRORS=$((ERRORS + 1))
    fi
  done < <(grep -n "WASMCERT:" "$lean_file")
done

echo "WasmCert refs: $REFS checked, $ERRORS mismatches"
[ "$ERRORS" -gt 0 ] && exit 1 || exit 0
