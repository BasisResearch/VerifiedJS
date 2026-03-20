#!/bin/bash
# Validate all .wasm files with wasm-tools validate.

set -euo pipefail

VALID=0
INVALID=0

for wasm_file in $(find . -name "*.wasm" -not -path "./.lake/*" 2>/dev/null); do
  if command -v wasm-tools &>/dev/null; then
    if wasm-tools validate "$wasm_file" 2>/dev/null; then
      echo "VALID $wasm_file"
      VALID=$((VALID + 1))
    else
      echo "INVALID $wasm_file"
      INVALID=$((INVALID + 1))
    fi
  else
    echo "SKIP $wasm_file (wasm-tools not found)"
  fi
done

echo ""
echo "Wasm validation: $VALID valid, $INVALID invalid"
