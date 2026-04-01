#!/usr/bin/env bash
set -euo pipefail

# Interactive hackathon demo runner for VerifiedJS.
# Press Enter to run a step, "s" to skip, or "q" to quit.

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

DEMO_JS="${1:-demo_hackathon.js}"
DEMO_WASM="${DEMO_JS%.js}.wasm"
E2E_LOG="/tmp/verifiedjs_hackathon_e2e.log"

highlight_file() {
  local file="$1"
  if [[ ! -f "$file" ]]; then
    echo "Missing file: $file"
    return 1
  fi
  awk '
    BEGIN {
      green = "\033[0;32m"; cyan = "\033[0;36m"; yellow = "\033[0;33m"; reset = "\033[0m";
    }
    {
      line = $0
      gsub(/(function|return|if|else|while|for|var|let|const)/, green "&" reset, line)
      gsub(/(console\.log|print_result|core_trace|flat_trace|anf_trace)/, cyan "&" reset, line)
      gsub(/(PASS|FAIL|SKIP|error|unimplemented)/, yellow "&" reset, line)
      printf "%4d  %s\n", NR, line
    }
  ' "$file"
}

step() {
  local label="$1"
  local cmd="$2"
  local choice=""
  echo
  echo "=== $label ==="
  echo "\$ $cmd"
  if [[ -t 0 ]]; then
    read -r -p "[Enter]=run, s=skip, q=quit > " choice || choice=""
  elif [[ -r /dev/tty ]]; then
    read -r -p "[Enter]=run, s=skip, q=quit > " choice </dev/tty || choice=""
  else
    echo "(non-interactive mode: running step)"
    choice=""
  fi
  case "${choice:-}" in
    q|Q)
      echo "Demo ended by user."
      exit 0
      ;;
    s|S)
      echo "Skipped."
      ;;
    *)
      eval "$cmd"
      ;;
  esac
}

echo "VerifiedJS Hackathon Demo"
echo "Repo: $ROOT_DIR"
echo "Demo file: $DEMO_JS"

step "Build compiler" "lake build verifiedjs"

step "Create demo JavaScript" "cat > \"$DEMO_JS\" <<'EOF'
var x = 1 + 2;
console.log(x);
EOF"

step "Show source file" "cat \"$DEMO_JS\""
step "Parse only" "lake exe verifiedjs \"$DEMO_JS\" --parse-only"
step "Show Core IR" "lake exe verifiedjs \"$DEMO_JS\" --emit=core"
step "Show WAT" "lake exe verifiedjs \"$DEMO_JS\" --emit=wat"
step "Compile to wasm" "lake exe verifiedjs \"$DEMO_JS\" -o \"$DEMO_WASM\""
step "Run with wasmtime" "wasmtime \"$DEMO_WASM\""
step "Run e2e suite" "bash tests/e2e/run_e2e.sh | tee \"$E2E_LOG\""
step "Show highlighted e2e sample: arithmetic.js" "highlight_file tests/e2e/arithmetic.js"
step "Show highlighted e2e sample: functions.js" "highlight_file tests/e2e/functions.js"
step "Show output-comparison code from e2e harness" "sed -n '92,156p' tests/e2e/run_e2e.sh | awk '
  BEGIN { cyan=\"\\033[0;36m\"; green=\"\\033[0;32m\"; reset=\"\\033[0m\" }
  {
    line=\$0
    gsub(/(core_trace|flat_trace|anf_trace)/, cyan \"&\" reset, line)
    gsub(/(if|then|else|PASS|FAIL|SKIP|print_result)/, green \"&\" reset, line)
    printf \"%4d  %s\\n\", NR+91, line
  }'"

echo
echo "Demo complete."
