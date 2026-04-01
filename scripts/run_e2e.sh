#!/bin/bash
# VerifiedJS end-to-end test runner.
# Compiles JS files to Wasm, runs on wasmtime, compares against Node.js.
#
# Usage:
#   ./scripts/run_e2e.sh                          # run all e2e tests
#   ./scripts/run_e2e.sh --seed XXXX --sample 0.05  # 5% sample
#   ./scripts/run_e2e.sh tests/flagship/prettier/  # specific directory

set -euo pipefail

SAMPLE_RATE="1.0"
SEED=""
TEST_DIR="tests/e2e"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --seed)   SEED="$2"; shift 2 ;;
    --sample) SAMPLE_RATE="$2"; shift 2 ;;
    *)        TEST_DIR="$1"; shift ;;
  esac
done

if [ ! -d "$TEST_DIR" ]; then
  echo "Test directory not found: $TEST_DIR"
  exit 1
fi

PASS=0
FAIL=0
SKIP=0

for test_file in "$TEST_DIR"/*.js; do
  [ -f "$test_file" ] || continue

  # Sampling
  if [ -n "$SEED" ] && [ "$SAMPLE_RATE" != "1.0" ]; then
    hash=$(echo "${SEED}${test_file}" | md5sum 2>/dev/null | head -c 8 || echo "00000000")
    hash_num=$((16#$hash % 100))
    threshold=$(echo "$SAMPLE_RATE * 100" | bc 2>/dev/null | cut -d. -f1 || echo "5")
    if [ "$hash_num" -ge "${threshold:-5}" ]; then
      SKIP=$((SKIP + 1))
      continue
    fi
  fi

  # Get expected output from Node.js
  expected=$(node "$test_file" 2>&1 || true)

  # Compile with VerifiedJS and run on wasmtime
  wasm_file="${test_file%.js}.wasm"
  if lake exe verifiedjs "$test_file" -o "$wasm_file" 2>/dev/null; then
    if command -v wasmtime &>/dev/null; then
      actual=$(wasmtime "$wasm_file" 2>&1 || true)
    else
      actual="WASMTIME_NOT_FOUND"
    fi
  else
    actual="COMPILE_ERROR"
  fi

  if [ "$expected" = "$actual" ]; then
    echo "PASS $test_file"
    PASS=$((PASS + 1))
  else
    echo "FAIL $test_file"
    echo "  expected: $(echo "$expected" | head -3)"
    echo "  actual:   $(echo "$actual" | head -3)"
    FAIL=$((FAIL + 1))
  fi
done

echo ""
echo "E2E: $PASS passed, $FAIL failed, $SKIP skipped"
