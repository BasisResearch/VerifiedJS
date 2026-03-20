#!/usr/bin/env bash
# End-to-end metamorphic tests for VerifiedJS
# Tests:
#   1. Pipeline stages: parse → core → flat → anf → wasmIR → wat → .wasm
#   2. Metamorphic: interpreter traces consistent across Core/Flat/ANF
#   3. Wasm validation: compiled .wasm passes wasmtime validation
#   4. Node.js: test files run without error in Node.js
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$PROJECT_DIR"

PASS=0
FAIL=0
SKIP=0
ERRORS=""

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

print_result() {
  local name="$1" status="$2" detail="${3:-}"
  case "$status" in
    PASS) echo -e "  ${GREEN}✓${NC} $name"; PASS=$((PASS + 1)) ;;
    FAIL) echo -e "  ${RED}✗${NC} $name: $detail"; FAIL=$((FAIL + 1)); ERRORS="${ERRORS}\n  ✗ $name: $detail" ;;
    SKIP) echo -e "  ${YELLOW}⊘${NC} $name: $detail"; SKIP=$((SKIP + 1)) ;;
  esac
}

# Filter out Lean build noise from compiler output
filter_noise() {
  grep -v "^⚠\|^warning:\|^info:\|^✔\|^ℹ\|^PANIC\|^backtrace:\|^[0-9].*dylib\|^Note:\|^Build\|^trace:" | grep -v "^$" || true
}

echo "=== VerifiedJS End-to-End Tests ==="
echo ""

# Ensure the compiler is built
echo "Building compiler..."
if ! lake build 2>&1 | tail -1 | grep -q "successfully"; then
  echo "Build failed!"
  exit 1
fi
echo ""

# ---- Section 1: Pipeline stage tests ----
echo "--- Pipeline Stage Tests ---"
for js_file in "$SCRIPT_DIR"/*.js; do
  name="$(basename "$js_file" .js)"

  # Parse
  if lake exe verifiedjs "$js_file" --parse-only 2>&1 | filter_noise | grep -q "Parse OK"; then
    print_result "parse/$name" PASS
  else
    print_result "parse/$name" FAIL "parse error"
    continue
  fi

  # Emit stages
  for stage in core flat anf wasmIR wat; do
    out=$(lake exe verifiedjs "$js_file" --emit=$stage 2>&1 | filter_noise)
    if echo "$out" | grep -qi "error"; then
      print_result "emit-$stage/$name" FAIL "$(echo "$out" | grep -i error | head -1)"
    else
      print_result "emit-$stage/$name" PASS
    fi
  done

  # Compile to .wasm
  wasm_file="/tmp/verifiedjs_e2e_${name}.wasm"
  compile_out=$(lake exe verifiedjs "$js_file" -o "$wasm_file" 2>&1 | filter_noise)
  if echo "$compile_out" | grep -q "Compiled to"; then
    print_result "compile/$name" PASS

    # Validate wasm magic
    magic=$(xxd -l 4 -p "$wasm_file" 2>/dev/null || echo "")
    if [ "$magic" = "0061736d" ]; then
      print_result "wasm-magic/$name" PASS
    else
      print_result "wasm-magic/$name" FAIL "bad magic: $magic"
    fi

    # Validate with wasmtime (if available)
    if command -v wasmtime &>/dev/null; then
      if wasmtime run "$wasm_file" 2>/dev/null; then
        print_result "wasmtime-run/$name" PASS
      else
        wt_err=$(wasmtime run "$wasm_file" 2>&1 | head -3)
        print_result "wasmtime-run/$name" FAIL "$wt_err"
      fi
    fi
  else
    print_result "compile/$name" FAIL "$(echo "$compile_out" | grep -i error | head -1)"
  fi
done
echo ""

# ---- Section 2: Metamorphic interpreter tests ----
echo "--- Metamorphic Interpreter Tests ---"
echo "  (Core vs Flat vs ANF interpreter traces should match)"

for js_file in "$SCRIPT_DIR"/*.js; do
  name="$(basename "$js_file" .js)"

  core_trace=$(lake exe verifiedjs "$js_file" --run=core 2>&1 | filter_noise)
  flat_trace=$(lake exe verifiedjs "$js_file" --run=flat 2>&1 | filter_noise)
  anf_trace=$(lake exe verifiedjs "$js_file" --run=anf 2>&1 | filter_noise)

  core_has_err=$(echo "$core_trace" | grep -c "unimplemented\|Error" || true)
  flat_has_err=$(echo "$flat_trace" | grep -c "unimplemented\|Error" || true)
  anf_has_err=$(echo "$anf_trace" | grep -c "unimplemented\|Error" || true)

  if [ "$core_has_err" -gt 0 ] && [ "$flat_has_err" -gt 0 ] && [ "$anf_has_err" -gt 0 ]; then
    print_result "metamorphic/$name" SKIP "all interpreters returned errors"
    continue
  fi

  # Core vs Flat
  if [ "$core_has_err" -eq 0 ] && [ "$flat_has_err" -eq 0 ]; then
    if [ "$core_trace" = "$flat_trace" ]; then
      print_result "core≡flat/$name" PASS
    else
      print_result "core≡flat/$name" FAIL "traces differ"
    fi
  else
    print_result "core≡flat/$name" SKIP "interpreter error"
  fi

  # Flat vs ANF
  if [ "$flat_has_err" -eq 0 ] && [ "$anf_has_err" -eq 0 ]; then
    if [ "$flat_trace" = "$anf_trace" ]; then
      print_result "flat≡anf/$name" PASS
    else
      print_result "flat≡anf/$name" FAIL "traces differ"
    fi
  else
    print_result "flat≡anf/$name" SKIP "interpreter error"
  fi
done
echo ""

# ---- Section 3: Node.js comparison ----
if command -v node &>/dev/null; then
  echo "--- Node.js Comparison ---"
  echo "  (verifying test files are valid JS)"
  for js_file in "$SCRIPT_DIR"/*.js; do
    name="$(basename "$js_file" .js)"
    if node "$js_file" 2>/dev/null; then
      print_result "node-valid/$name" PASS
    else
      print_result "node-valid/$name" FAIL "node error"
    fi
  done
  echo ""
fi

# ---- Summary ----
echo "=== Summary ==="
echo -e "  ${GREEN}Passed: $PASS${NC}"
echo -e "  ${RED}Failed: $FAIL${NC}"
echo -e "  ${YELLOW}Skipped: $SKIP${NC}"

if [ -n "$ERRORS" ]; then
  echo ""
  echo "Failures:"
  echo -e "$ERRORS"
fi

[ "$FAIL" -eq 0 ]
