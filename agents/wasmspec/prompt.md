# wasmspec — CLOSE P2 + TACKLE noCallFrameReturn

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T23:30
- Total: **42 real sorries** (ANF 30, CC 12). Down from 44 (-2).
- You closed P0 + P1 last run (step_nonError_preserves + step_error_noNonCallFrameTryCatch). EXCELLENT.
- **P2 remains**: L16451 — ¬HasNonCallFrameTryCatchInHead from normalizeExpr .return context.

## P0: Close P2 (L16451) — HIGHEST PRIORITY

Line 16451: `sorry` inside the `suffices h` block of `HasReturnInHead_Steps_steppable`.

Goal: prove `¬HasNonCallFrameTryCatchInHead a` where `a` comes from `normalizeExpr sf.expr (fun t => pure (.return (some (.trivial t))))`.

### Approach:
1. `lean_goal` at L16451 to see exact context — what is `a`?
2. `a` is the result of `normalizeExpr` with a `.return` continuation. The key insight is:
   - `normalizeExpr` never introduces `tryCatch` — only `Flat.step?` does (for function calls)
   - So `normalizeExpr` output has NO tryCatch at all in eval-head position
3. You need a lemma: `normalizeExpr_no_tryCatch_in_head` or similar
4. This should be provable by structural induction on the expression, showing normalizeExpr output has no tryCatch in eval-head position
5. Alternative: show that `normalizeExpr` output expressions only contain tryCatch when the source expression was `.tryCatch`, and those are never in eval-head position for a `.return` continuation

### Specific tactic approach:
```lean
-- At L16451, try:
have : ¬HasNonCallFrameTryCatchInHead a := by
  -- a comes from normalizeExpr with return continuation
  -- normalizeExpr doesn't introduce tryCatch in eval-head
  sorry -- fill with structural argument
```

**Expected: -1 sorry.**

## P1: noCallFrameReturn (L25039) — SECOND PRIORITY

Line 25039: needs `catchParam ≠ "__call_frame_return__"` for tryCatch case in anfConvert_step_star.

This is related to P0 — both are about "__call_frame_return__" invariants. The issue: source Flat programs never have "__call_frame_return__" as a catch param (it's only introduced by Flat.step? for function calls). But during simulation, sf.expr COULD temporarily have it.

### Approach:
1. `lean_goal` at L25039 to see the exact need
2. Consider: add a `NoCallFrameParam` predicate as a precondition to the simulation invariant
3. Prove: normalizeExpr output has no "__call_frame_return__" catch params
4. Prove: preservation — if `NoCallFrameParam sf.expr` and the ANF step doesn't introduce one, then `NoCallFrameParam sf'.expr`
5. The tryCatch case in Flat.step? for function calls DOES introduce "__call_frame_return__", but the call case in anfConvert_step_star handles the entire function execution internally

This may be multi-run infrastructure. Even partial progress (defining the predicate + stating preservation) is valuable.

**Expected: 0 to -1 sorry.**

## DO NOT WORK ON:
- L10799-L11170 (labeled trivial mismatch — proof agent)
- L13809 (compound throw — proof agent)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — P2 HasNonCallFrameTryCatch + noCallFrameReturn" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
