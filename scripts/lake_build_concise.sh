#!/usr/bin/env bash
set -euo pipefail

SHOW_WARNINGS=0
if [[ "${1:-}" == "--show-warnings" ]]; then
  SHOW_WARNINGS=1
  shift
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOG_DIR="${ROOT_DIR}/test_logs"
mkdir -p "${LOG_DIR}"
STAMP="$(date +%Y%m%d_%H%M%S)"
LOG_FILE="${LOG_DIR}/lake_build_${STAMP}.log"

cd "${ROOT_DIR}"

# Pass remaining args to lake build (e.g. module names)
set +e
OUTPUT="$(lake build "$@" 2>&1)"
STATUS=$?
set -e

printf "%s\n" "${OUTPUT}" > "${LOG_FILE}"

ERROR_COUNT="$(printf "%s\n" "${OUTPUT}" | awk BEGIN{IGNORECASE=1} /error:/{c++} END{print c+0})"
WARNING_COUNT="$(printf "%s\n" "${OUTPUT}" | awk BEGIN{IGNORECASE=1} /warning:/{c++} END{print c+0})"

if [[ "${SHOW_WARNINGS}" -eq 1 ]]; then
  printf "%s\n" "${OUTPUT}" | rg -i "warning:|^⚠" || true
else
  printf "%s\n" "${OUTPUT}" | rg -iv "warning:|^⚠" || true
fi

if [[ "${STATUS}" -eq 0 ]]; then
  echo "lake build${1:+ $*}: PASS (errors=${ERROR_COUNT}, warnings=${WARNING_COUNT}) — log: ${LOG_FILE}"
else
  echo "--- errors (summary) ---"
  printf "%s\n" "${OUTPUT}" | rg -i "error:|✖|build failed|failed" || true
  echo "lake build${1:+ $*}: FAIL (errors=${ERROR_COUNT}, warnings=${WARNING_COUNT}) — log: ${LOG_FILE}"
fi

exit "${STATUS}"
