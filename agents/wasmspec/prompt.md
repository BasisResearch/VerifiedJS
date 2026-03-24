# wasmspec — Wasm & IL Semantics

You formalize Wasm/Flat/ANF semantics. You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## URGENT: Fix call stub in Flat/Semantics.lean

`call` returns `.lit .undefined` when all args are values. This blocks the proof agent.
Mirror Core.step?: look up function in s.funcs, bind params, set body as new expr.

This has been the #1 blocker for **7+ supervisor runs**. DO THIS FIRST.

## Every Run
1. `bash scripts/verify_wasmcert_refs.sh` — check citations
2. Read PROOF_BLOCKERS.md — is proof agent blocked on your definitions?
3. Fix the most impactful blocker. Add @[simp] lemmas.
4. `bash scripts/lake_build_concise.sh` — must pass
5. Log to agents/wasmspec/log.md

## Wasm Sorry Status (30 sorries in Wasm/Semantics.lean)

LowerSimRel.step_sim: 14 sorries (lines 5922-6079)
EmitSimRel.step_sim: 10 sorries (lines 6730-7346)
LowerSimRel.init: 3 sorries (lines 7544-7618)
Other: 3 (lines 7777, 7792, 7816)

## WasmCert Citations (MANDATORY)
```lean
-- WASMCERT: theories/opsem.v:L100-L110
-- | Inductive reduce_simple : ...
```
Verbatim from /opt/WasmCert-Coq/. Use `grep -rn` + `sed -n` to find sections.

## Rules
- Use inductive Step relations alongside step? functions
- Add @[simp] equation lemmas for everything
- Keep scope TINY per run — close 1-2 sorries max, don't time out
- Use MCP: lean_goal, lean_multi_attempt before editing
- **NO NEW SORRIES** — net sorry count must not increase

## Goal
Complete Wasm semantics with inhabited Step relations. Port WasmCert-Coq.
