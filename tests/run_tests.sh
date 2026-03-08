#!/bin/bash
# VerifiedJS test runner.
# Supports stage-friendly execution for partially implemented compiler phases.
#
# Modes:
#   --fast (default): quick checks
#   --full: heavier checks
#
# Profiles:
#   --profile core      : unit + wasm only (no parser/e2e)
#   --profile parser    : unit + parser gates + wasm (no e2e)
#   --profile pipeline  : unit + e2e + wasm (+ parse integration in --full)
#
# Output: one summary line to stdout. Details to test_logs/.

set -euo pipefail

MODE="--fast"
PROFILE="pipeline"
PARSER_SAMPLE=200
SEED="$(echo "${HOSTNAME:-local}" | md5sum 2>/dev/null | head -c 8 || echo "deadbeef")"

usage() {
  cat <<'EOF'
Usage: ./tests/run_tests.sh [--fast|--full] [--profile core|parser|pipeline] [--parser-sample N]
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --fast|--full)
      MODE="$1"
      shift
      ;;
    --profile)
      PROFILE="${2:?missing value for --profile}"
      shift 2
      ;;
    --parser-sample)
      PARSER_SAMPLE="${2:?missing value for --parser-sample}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown arg: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

if [[ "${PROFILE}" != "core" && "${PROFILE}" != "parser" && "${PROFILE}" != "pipeline" ]]; then
  echo "ERROR: unsupported profile '${PROFILE}' (expected: core|parser|pipeline)" >&2
  exit 1
fi

LOGDIR="$(mktemp -d "test_logs/$(date +%Y%m%d_%H%M%S)_XXXXXX")"
SECONDS=0

UNIT_PASS=0
UNIT_FAIL=0
UNIT_TOTAL=0
UNIT_STATUS="missing"
UNIT_NOTE=""

E2E_PASS=0
E2E_FAIL=0
E2E_SKIP=0
E2E_TOTAL=0
E2E_STATUS="skipped"

PARSE_PASS=0
PARSE_FAIL=0
PARSE_TOTAL=0
PARSE_STATUS="skipped"

T262_PASS=0
T262_FAIL=0
T262_XFAIL=0
T262_SKIP=0
T262_TOTAL=0
T262_STATUS="skipped"

VALID=0
INVALID=0
WASM_TOTAL=0
WASM_STATUS="missing"

echo "Running Lean unit tests..." >&2
if lake test > "${LOGDIR}/unit.log" 2>&1; then
  UNIT_STATUS="ok"
elif grep -q "no test driver configured" "${LOGDIR}/unit.log"; then
  if lake build Tests >> "${LOGDIR}/unit.log" 2>&1; then
    UNIT_STATUS="ok"
    UNIT_NOTE="build"
  else
    UNIT_STATUS="fail"
  fi
else
  UNIT_STATUS="fail"
fi
UNIT_PASS="$(grep -c "PASS\|✓\|passed" "${LOGDIR}/unit.log" 2>/dev/null || true)"
UNIT_FAIL="$(grep -c "FAIL\|✗\|failed" "${LOGDIR}/unit.log" 2>/dev/null || true)"
UNIT_TOTAL=$((UNIT_PASS + UNIT_FAIL))
if [[ "${UNIT_STATUS}" == "ok" && "${UNIT_TOTAL}" -eq 0 ]]; then
  # Build-only success should still count as one green unit gate.
  UNIT_PASS=1
  UNIT_TOTAL=1
  [[ -z "${UNIT_NOTE}" ]] && UNIT_NOTE="build"
fi

if [[ "${PROFILE}" == "pipeline" && -x "./scripts/run_e2e.sh" ]]; then
  E2E_TOTAL="$(find tests/e2e -maxdepth 1 -type f -name '*.js' | wc -l | tr -d ' ')"
  if [[ "${E2E_TOTAL}" -eq 0 ]]; then
    E2E_STATUS="empty"
    : > "${LOGDIR}/e2e.log"
  else
    E2E_STATUS="ok"
    if [[ "${MODE}" == "--fast" ]]; then
      ./scripts/run_e2e.sh --seed "${SEED}" --sample 0.05 > "${LOGDIR}/e2e.log" 2>&1 || E2E_STATUS="fail"
    else
      ./scripts/run_e2e.sh > "${LOGDIR}/e2e.log" 2>&1 || E2E_STATUS="fail"
    fi
    E2E_PASS="$(grep -c "^PASS " "${LOGDIR}/e2e.log" 2>/dev/null || true)"
    E2E_FAIL="$(grep -c "^FAIL " "${LOGDIR}/e2e.log" 2>/dev/null || true)"
    E2E_SKIP="$(sed -nE 's/^E2E: [0-9]+ passed, [0-9]+ failed, ([0-9]+) skipped$/\1/p' "${LOGDIR}/e2e.log" | tail -n1)"
    [[ -z "${E2E_SKIP}" ]] && E2E_SKIP=0
    E2E_TOTAL=$((E2E_PASS + E2E_FAIL))
  fi
elif [[ "${PROFILE}" == "pipeline" ]]; then
  E2E_STATUS="missing"
fi

if [[ "${PROFILE}" == "parser" && -x "./scripts/parse_flagship_failfast.sh" ]]; then
  PARSE_STATUS="ok"
  if [[ "${MODE}" == "--full" ]]; then
    ./scripts/parse_flagship_failfast.sh --full > "${LOGDIR}/parse_flagship.log" 2>&1 || PARSE_STATUS="fail"
  else
    {
      ./scripts/parse_flagship_failfast.sh --project prettier --sample-per-project "${PARSER_SAMPLE}"
      ./scripts/parse_flagship_failfast.sh --project babel --sample-per-project "${PARSER_SAMPLE}"
      ./scripts/parse_flagship_failfast.sh --project TypeScript --sample-per-project "${PARSER_SAMPLE}"
    } > "${LOGDIR}/parse_flagship.log" 2>&1 || PARSE_STATUS="fail"
  fi
  PARSE_PASS="$(grep -c "^PARSE_PASS " "${LOGDIR}/parse_flagship.log" 2>/dev/null || true)"
  PARSE_FAIL="$(grep -c "^PARSE_FAIL " "${LOGDIR}/parse_flagship.log" 2>/dev/null || true)"
  PARSE_TOTAL=$((PARSE_PASS + PARSE_FAIL))
elif [[ "${MODE}" != "--fast" && -x "./scripts/parse_flagship.sh" ]]; then
  # Keep long-sequence parse gate in full runs for non-parser profiles.
  PARSE_STATUS="ok"
  ./scripts/parse_flagship.sh --full --integration-only > "${LOGDIR}/parse_flagship.log" 2>&1 || PARSE_STATUS="fail"
  PARSE_PASS="$(grep -c "^PARSE_PASS " "${LOGDIR}/parse_flagship.log" 2>/dev/null || true)"
  PARSE_FAIL="$(grep -c "^PARSE_FAIL " "${LOGDIR}/parse_flagship.log" 2>/dev/null || true)"
  PARSE_TOTAL=$((PARSE_PASS + PARSE_FAIL))
fi

if [[ "${PROFILE}" == "pipeline" && -x "./scripts/run_test262_compare.sh" ]]; then
  T262_STATUS="ok"
  if [[ "${MODE}" == "--fast" ]]; then
    ./scripts/run_test262_compare.sh --fast --sample 60 --seed "${SEED}" > "${LOGDIR}/test262.log" 2>&1 || T262_STATUS="fail"
  else
    ./scripts/run_test262_compare.sh --full --sample 500 --seed "${SEED}" > "${LOGDIR}/test262.log" 2>&1 || T262_STATUS="fail"
  fi
  T262_PASS="$(grep -c "^TEST262_PASS " "${LOGDIR}/test262.log" 2>/dev/null || true)"
  T262_FAIL="$(grep -c "^TEST262_FAIL " "${LOGDIR}/test262.log" 2>/dev/null || true)"
  T262_XFAIL="$(grep -c "^TEST262_XFAIL " "${LOGDIR}/test262.log" 2>/dev/null || true)"
  T262_SKIP="$(grep -c "^TEST262_SKIP " "${LOGDIR}/test262.log" 2>/dev/null || true)"
  T262_TOTAL=$((T262_PASS + T262_FAIL + T262_XFAIL + T262_SKIP))
elif [[ "${PROFILE}" == "pipeline" ]]; then
  T262_STATUS="missing"
fi

if [[ -x "./scripts/validate_wasm.sh" ]]; then
  WASM_STATUS="ok"
  ./scripts/validate_wasm.sh > "${LOGDIR}/validate.log" 2>&1 || WASM_STATUS="fail"
  VALID="$(grep -c "^VALID" "${LOGDIR}/validate.log" 2>/dev/null || true)"
  INVALID="$(grep -c "^INVALID" "${LOGDIR}/validate.log" 2>/dev/null || true)"
  WASM_TOTAL=$((VALID + INVALID))
else
  WASM_STATUS="missing"
fi

if [[ "${SECONDS}" -gt 300 ]]; then
  echo "WARNING: test run exceeding 5 minutes (${SECONDS}s). Consider --fast." >&2
fi

UNIT_LABEL="${UNIT_STATUS}"
if [[ -n "${UNIT_NOTE}" ]]; then
  UNIT_LABEL="${UNIT_STATUS}:${UNIT_NOTE}"
fi

E2E_LABEL="${E2E_STATUS}"
if [[ "${E2E_STATUS}" == "ok" || "${E2E_STATUS}" == "fail" ]]; then
  E2E_LABEL="${E2E_STATUS}:skip=${E2E_SKIP}"
fi

echo "Tests: mode=${MODE#--} profile=${PROFILE} unit=${UNIT_PASS}/${UNIT_TOTAL}(${UNIT_LABEL}) e2e=${E2E_PASS}/${E2E_TOTAL}(${E2E_LABEL}) parse=${PARSE_PASS}/${PARSE_TOTAL}(${PARSE_STATUS}) test262=${T262_PASS}/${T262_TOTAL}(fail=${T262_FAIL},xfail=${T262_XFAIL},${T262_STATUS}) wasm=${VALID}/${WASM_TOTAL}(${WASM_STATUS}) [${SECONDS}s] — logs in ${LOGDIR}"

if [[ "${UNIT_STATUS}" == "fail" ]] || [[ "${E2E_FAIL}" -gt 0 ]] || [[ "${PARSE_STATUS}" == "fail" ]] || [[ "${T262_FAIL}" -gt 0 ]] || [[ "${T262_STATUS}" == "fail" ]] || [[ "${INVALID}" -gt 0 ]] || [[ "${WASM_STATUS}" == "fail" ]]; then
  exit 1
fi
