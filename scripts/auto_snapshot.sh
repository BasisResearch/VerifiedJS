#!/bin/bash
cd /opt/verifiedjs
export PATH=/opt/elan/bin:/usr/local/bin:$PATH
export ELAN_HOME=/opt/elan

/usr/bin/git.real add -A 2>/dev/null

# Only commit if there are actual changes
if /usr/bin/git.real diff --cached --quiet 2>/dev/null; then
  exit 0
fi

# Gather stats for commit message
SORRY=$(grep -rc "sorry" --include="*.lean" VerifiedJS/ 2>/dev/null | awk -F: "{s+=\$2} END {print s}")
E2E_TOTAL=$(ls tests/e2e/*.js 2>/dev/null | wc -l)
LEAN_FILES=$(find VerifiedJS/ -name "*.lean" | wc -l)
LEAN_LOC=$(cat VerifiedJS/**/*.lean VerifiedJS/*.lean 2>/dev/null | wc -l)

# Check which agents changed files
CHANGED=$(/usr/bin/git.real diff --cached --name-only 2>/dev/null)
AGENTS=""
echo "$CHANGED" | grep -q "Source/\|Core/Syntax\|Core/Semantics\|tests/" && AGENTS="$AGENTS jsspec"
echo "$CHANGED" | grep -q "Flat/Syntax\|Flat/Semantics\|ANF/Syntax\|ANF/Semantics\|Wasm/Syntax\|Wasm/Semantics\|Wasm/Typing\|Wasm/Numerics\|Runtime/" && AGENTS="$AGENTS wasmspec"
echo "$CHANGED" | grep -q "Elaborate\|ClosureConvert\|Convert\|Optimize\|Lower\|Emit\|IR\|Binary\|Proofs/\|Driver\|Interp\|Print" && AGENTS="$AGENTS proof"
echo "$CHANGED" | grep -q "PROGRESS\|TASKS\|FAILURES\|PROOF_BLOCKERS\|ARCHITECTURE\|README\|SORRY_REPORT\|MEMORY/\|agents/" && AGENTS="$AGENTS supervisor"
AGENTS=$(echo $AGENTS | xargs)

FILES_CHANGED=$(echo "$CHANGED" | wc -l)

/usr/bin/git.real commit -m "auto: ${SORRY} sorries, ${LEAN_FILES} lean files, ${LEAN_LOC} LOC [${AGENTS:-none}]

Changed: ${FILES_CHANGED} files
Agents active:${AGENTS:- none}" 2>/dev/null
