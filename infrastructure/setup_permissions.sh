#!/bin/bash
set -euo pipefail

PROJECT=/opt/verifiedjs

# ---------- group & users ----------
getent group pipeline >/dev/null || groupadd pipeline
for u in jsspec wasmspec proof supervisor; do
  id -u "$u" &>/dev/null || useradd -r -g pipeline -d "$PROJECT" -s /bin/bash "$u"
done

# ---------- base ownership: root:pipeline, 750 dirs, 640 files ----------
chown -R root:pipeline "$PROJECT"
find "$PROJECT" -type d -exec chmod 750 {} \;
find "$PROJECT" -type f -exec chmod 640 {} \;

# ---------- agent directories ----------
mkdir -p "$PROJECT/agents"/{jsspec,wasmspec,proof,supervisor}

# Create log/prompt files if missing
for agent in jsspec wasmspec proof supervisor; do
  touch "$PROJECT/agents/$agent/log.md"
  touch "$PROJECT/agents/$agent/prompt.md"
done

# ---------- prompt files: supervisor owns all except its own ----------
for agent in jsspec wasmspec proof; do
  chown supervisor:pipeline "$PROJECT/agents/$agent/prompt.md"
  chmod 640 "$PROJECT/agents/$agent/prompt.md"
done
chown root:pipeline "$PROJECT/agents/supervisor/prompt.md"
chmod 440 "$PROJECT/agents/supervisor/prompt.md"

# ---------- log files: each agent owns its own ----------
chown jsspec:pipeline   "$PROJECT/agents/jsspec/log.md"
chown wasmspec:pipeline "$PROJECT/agents/wasmspec/log.md"
chown proof:pipeline    "$PROJECT/agents/proof/log.md"
chown supervisor:pipeline "$PROJECT/agents/supervisor/log.md"
chmod 640 "$PROJECT/agents"/*/log.md

# ---------- jsspec-owned .lean files ----------
jsspec_files=(
  VerifiedJS/Source/AST.lean
  VerifiedJS/Source/Lexer.lean
  VerifiedJS/Source/Parser.lean
  VerifiedJS/Source/Print.lean
  VerifiedJS/Core/Syntax.lean
  VerifiedJS/Core/Semantics.lean
)
for f in "${jsspec_files[@]}"; do
  [ -f "$PROJECT/$f" ] && chown jsspec:pipeline "$PROJECT/$f" && chmod 640 "$PROJECT/$f"
done
# jsspec also owns tests (excluding flagship)
find "$PROJECT/tests/e2e" -type f -exec chown jsspec:pipeline {} \; -exec chmod 640 {} \;
find "$PROJECT/tests/unit" -type f -exec chown jsspec:pipeline {} \; -exec chmod 640 {} \;

# ---------- wasmspec-owned .lean files ----------
wasmspec_files=(
  VerifiedJS/Flat/Syntax.lean
  VerifiedJS/Flat/Semantics.lean
  VerifiedJS/ANF/Syntax.lean
  VerifiedJS/ANF/Semantics.lean
  VerifiedJS/Wasm/Syntax.lean
  VerifiedJS/Wasm/Semantics.lean
  VerifiedJS/Wasm/Typing.lean
  VerifiedJS/Wasm/Numerics.lean
  VerifiedJS/Runtime/Values.lean
  VerifiedJS/Runtime/GC.lean
  VerifiedJS/Runtime/Objects.lean
  VerifiedJS/Runtime/Strings.lean
  VerifiedJS/Runtime/Regex.lean
  VerifiedJS/Runtime/Generators.lean
)
for f in "${wasmspec_files[@]}"; do
  [ -f "$PROJECT/$f" ] && chown wasmspec:pipeline "$PROJECT/$f" && chmod 640 "$PROJECT/$f"
done

# ---------- proof-owned .lean files ----------
proof_files=(
  VerifiedJS/Core/Elaborate.lean
  VerifiedJS/Core/Interp.lean
  VerifiedJS/Core/Print.lean
  VerifiedJS/Flat/ClosureConvert.lean
  VerifiedJS/Flat/Interp.lean
  VerifiedJS/Flat/Print.lean
  VerifiedJS/ANF/Convert.lean
  VerifiedJS/ANF/Optimize.lean
  VerifiedJS/ANF/Interp.lean
  VerifiedJS/ANF/Print.lean
  VerifiedJS/Wasm/Lower.lean
  VerifiedJS/Wasm/Emit.lean
  VerifiedJS/Wasm/IR.lean
  VerifiedJS/Wasm/IRInterp.lean
  VerifiedJS/Wasm/IRPrint.lean
  VerifiedJS/Wasm/Interp.lean
  VerifiedJS/Wasm/Print.lean
  VerifiedJS/Wasm/Binary.lean
  VerifiedJS/Proofs/ElaborateCorrect.lean
  VerifiedJS/Proofs/ClosureConvertCorrect.lean
  VerifiedJS/Proofs/ANFConvertCorrect.lean
  VerifiedJS/Proofs/OptimizeCorrect.lean
  VerifiedJS/Proofs/LowerCorrect.lean
  VerifiedJS/Proofs/EmitCorrect.lean
  VerifiedJS/Proofs/EndToEnd.lean
  VerifiedJS/Driver.lean
)
for f in "${proof_files[@]}"; do
  [ -f "$PROJECT/$f" ] && chown proof:pipeline "$PROJECT/$f" && chmod 640 "$PROJECT/$f"
done

# ---------- supervisor-owned markdown files ----------
supervisor_files=(
  ARCHITECTURE.md
  TASKS.md
  PROGRESS.md
  README.md
  FAILURES.md
  PROOF_BLOCKERS.md
  SORRY_REPORT.md
  MEMORY/AGENTS.md
)
for f in "${supervisor_files[@]}"; do
  [ -f "$PROJECT/$f" ] && chown supervisor:pipeline "$PROJECT/$f" && chmod 640 "$PROJECT/$f"
done

# ---------- shared immutable files: root:pipeline 640 ----------
shared_files=(VerifiedJS.lean VerifiedJS/Util.lean lakefile.lean lake-manifest.json lean-toolchain Dockerfile)
for f in "${shared_files[@]}"; do
  [ -f "$PROJECT/$f" ] && chown root:pipeline "$PROJECT/$f" && chmod 640 "$PROJECT/$f"
done

# ---------- scripts: read-only (root:pipeline) ----------
chown -R root:pipeline "$PROJECT/scripts"
find "$PROJECT/scripts" -type f -exec chmod 440 {} \;
find "$PROJECT/scripts" -type d -exec chmod 550 {} \;

# ---------- tests/flagship: read-only vendor code ----------
chown -R root:pipeline "$PROJECT/tests/flagship"
find "$PROJECT/tests/flagship" -type f -exec chmod 440 {} \; 2>/dev/null || true
find "$PROJECT/tests/flagship" -type d -exec chmod 550 {} \; 2>/dev/null || true

# ---------- .lake/build: setgid so all agents can build ----------
if [ -d "$PROJECT/.lake" ]; then
  chown -R root:pipeline "$PROJECT/.lake"
  find "$PROJECT/.lake" -type d -exec chmod 2770 {} \;
  find "$PROJECT/.lake" -type f -exec chmod 640 {} \;
fi

# ---------- runner script ----------
chmod 550 "$PROJECT/agents/runner.sh" 2>/dev/null || true

# ---------- .claude config dirs per agent ----------
for agent in jsspec wasmspec proof supervisor; do
  mkdir -p "$PROJECT/.claude-$agent"
  chown "$agent:pipeline" "$PROJECT/.claude-$agent"
  chmod 700 "$PROJECT/.claude-$agent"
done

# ---------- log directory ----------
mkdir -p /var/log/verifiedjs
chown root:pipeline /var/log/verifiedjs
chmod 2770 /var/log/verifiedjs

echo "[setup_permissions] Done."
