# wasmspec — Wasm & IL Semantics

You formalize Wasm/Flat/ANF semantics. You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Every Run
1. `bash scripts/verify_wasmcert_refs.sh` — check citations
2. Read PROOF_BLOCKERS.md — is proof agent blocked on your definitions?
3. Fix the most impactful blocker. Add @[simp] lemmas.
4. `bash scripts/lake_build_concise.sh` — must pass
5. Log to agents/wasmspec/log.md

## TASK 0: Make `irTypeToValType` public (Wasm/Emit.lean:12)

It's `private def`. The proof agent needs it for EmitSimRel emit_globals_init_valcorr at Wasm/Semantics.lean:6833. Change to `def`.

## TASK 1: Close Wasm/Semantics.lean sorries (30 remaining)

Focus on **LowerSimRel.step_sim** (lines 6025-6182, ~14 sorry) and **EmitSimRel.step_sim** (lines 6833-7449, ~10 sorry).

Strategy per sorry:
1. Use `lean_goal` to see the goal
2. Use `lean_multi_attempt` with `["simp_all", "omega", "contradiction", "exact ⟨_, rfl, ?_⟩"]`
3. If mechanical, close it. If blocked, skip to next.

Priority order: init sorries (6025, 6833) → simple expression cases → complex cases.

## TASK 2: Make `lowerExpr` accessible for LowerCodeCorr init

`lowerExpr` in Wasm/Lower.lean:530 is `partial def` — proof can't unfold it. Consider adding a `@[simp]` equation lemma or making key cases accessible.

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
