#!/usr/bin/env bash
set -euo pipefail

DRY_RUN=0
if [[ "${1:-}" == "--dry-run" ]]; then
  DRY_RUN=1
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FLAGSHIP_DIR="${ROOT_DIR}/tests/flagship"
LOG_DIR="${ROOT_DIR}/test_logs/flagship_$(date +%Y%m%d_%H%M%S)"
mkdir -p "${LOG_DIR}"

run_cmd() {
  local name="$1"
  local cwd="$2"
  local cmd="$3"
  local log_file="$4"

  echo "[${name}] ${cmd}"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi

  (cd "${cwd}" && bash -lc "${cmd}") >"${log_file}" 2>&1
}

compile_with_verifiedjs() {
  local name="$1"
  local input="$2"
  local out_dir="${LOG_DIR}/${name}"
  mkdir -p "${out_dir}"

  run_cmd "${name}" "${ROOT_DIR}" \
    "lake exe verifiedjs \"${input}\" --emit=core > \"${out_dir}/core.out\"" \
    "${out_dir}/verifiedjs.log"
}

check_exists() {
  local path="$1"
  if [[ ! -e "${path}" ]]; then
    echo "ERROR: missing required path: ${path}"
    exit 1
  fi
}

check_exists "${FLAGSHIP_DIR}/prettier/package.json"
check_exists "${FLAGSHIP_DIR}/babel/package.json"
check_exists "${FLAGSHIP_DIR}/TypeScript/package.json"

run_cmd "prettier" "${FLAGSHIP_DIR}/prettier" \
  "corepack yarn install --immutable && corepack yarn build" \
  "${LOG_DIR}/prettier.build.log"
compile_with_verifiedjs "prettier" "${FLAGSHIP_DIR}/prettier/bin/prettier.cjs"

run_cmd "babel" "${FLAGSHIP_DIR}/babel" \
  "corepack yarn install --immutable && corepack yarn build" \
  "${LOG_DIR}/babel.build.log"
compile_with_verifiedjs "babel" "${FLAGSHIP_DIR}/babel/packages/babel-cli/bin/babel.js"

run_cmd "TypeScript" "${FLAGSHIP_DIR}/TypeScript" \
  "npm ci && npm run build:compiler" \
  "${LOG_DIR}/typescript.build.log"
compile_with_verifiedjs "TypeScript" "${FLAGSHIP_DIR}/TypeScript/lib/tsc.js"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "Flagship build-cycle dry run complete."
else
  echo "Flagship build cycles complete. Logs: ${LOG_DIR}"
fi
