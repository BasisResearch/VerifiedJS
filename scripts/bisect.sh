#!/bin/bash
# Oracle-based IL-level bisection.
# When an e2e test fails, use this to find which compilation pass introduced the bug.
#
# Usage: ./scripts/bisect.sh test.js

set -euo pipefail

if [ $# -eq 0 ]; then
  echo "Usage: $0 <test.js>"
  exit 1
fi

INPUT="$1"
EXPECTED=$(node "$INPUT" 2>&1 || true)

echo "Expected output (from Node.js):"
echo "$EXPECTED"
echo "---"

for level in core flat anf wasmIR; do
  echo -n "Testing at $level level... "
  ACTUAL=$(lake exe verifiedjs "$INPUT" --run="$level" 2>&1 || echo "ERROR")

  if [ "$EXPECTED" = "$ACTUAL" ]; then
    echo "PASS"
  else
    echo "FAIL"
    echo "  expected: $(echo "$EXPECTED" | head -3)"
    echo "  actual:   $(echo "$ACTUAL" | head -3)"
    echo ""
    echo "Bug introduced at or before the $level level."
    exit 0
  fi
done

echo "All IL levels match Node.js. Bug is in Wasm binary encoding or runtime."
