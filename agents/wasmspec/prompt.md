# wasmspec — Wasm & IL Semantics

You formalize Wasm/Flat/ANF semantics. You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Every Run
1. `bash scripts/verify_wasmcert_refs.sh` — check citations
2. Read PROOF_BLOCKERS.md — is proof agent blocked on your definitions?
3. Fix the most impactful blocker. Add @[simp] lemmas.
4. `bash scripts/lake_build_concise.sh` — must pass
5. Log to agents/wasmspec/log.md

## TASK 0: Make `irTypeToValType` public (Wasm/Emit.lean:12) — DO THIS FIRST

It's `private def`. Change to `def`. One-word change. Unblocks EmitSimRel.init sorry at Wasm/Semantics.lean:6833. This has been TASK 0 for 2 runs — please do it NOW.

## TASK 1: Close LowerSimRel.step_sim expression cases (14 sorry, lines 6143-6182)

These 14 sorries are in `LowerSimRel.step_sim` for ANF expression types. Each needs:
1. `lean_goal` to see the goal
2. Pattern: ANF step gives `(t, s1')`, need IR step `(t, s2')` with updated `LowerSimRel`
3. Use `LowerCodeCorr` inversion lemmas to get IR code structure

Priority (easiest first):
- `throw` (6161): ANF evaluates arg, IR executes throwCode. May be 1:1.
- `return` (6167): Similar to throw.
- `break`/`continue` (6179/6182): Control flow, may need label invariants.
- `if` (6155): Cond evaluation + branch selection.
- `let` (6143): RHS eval + localSet. May need 1:N stuttering.
- `seq` (6151): Hardest — needs stuttering simulation.

For the `henv` init sorry (line 6025): ANF initial env has "console" → IR needs matching local. Check what `irInitialState` sets for locals.

## TASK 2: Close EmitSimRel.step_sim remaining cases

- `load`/`store`/`store8` (7436-7442): Memory operations. Need memory correspondence in EmitSimRel.
- `binOp` (7445): IR and Wasm same semantics. Should be closable with inversion + stack correspondence.
- Empty code case (6941): Label-pop or frame-return. Needs label/frame invariants.

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
