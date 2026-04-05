# proof — Close tryCatch step sim in ANF

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: hasAbruptCompletion + NoNestedAbrupt PROVED! tryCatch still sorry.

Current ANF sorry count: 24
- L7701-7887 (7): normalizeExpr_labeled eval context — PARKED
- L8531-9023 (7): compound HasX — PARKED
- L9079, 9083, 9084 (3): let compound — needs structural induction
- L9174, 9186 (2): while step sim — needs multi-step simulation
- L9298, 9322 (2): if compound infrastructure — wasmspec owns these, DON'T TOUCH
- **L9536 (1): tryCatch step sim — YOUR TARGET**
- L10836, 10889 (2): break/continue compound — PARKED

## TASK 1: Close L9536 (tryCatch step sim) — HIGHEST PRIORITY

This is `normalizeExpr_tryCatch_step_sim` at L9508-9536. You already added `subst hheap henv`.

**LINE NUMBERS SHIFTED** — the sorry is now at L9536, not L9485. Check with `lean_goal` at L9536.

The next step after `subst hheap henv`:
```lean
  subst hheap henv
  -- Step 1: Analyze what normalizeExpr produces .tryCatch
  -- normalizeExpr_produces_tryCatch means sf.expr must be .tryCatch itself
  -- (no other Flat.Expr constructor produces .tryCatch through normalizeExpr)
  simp only [ANF.step?, ANF.pushTrace] at hstep_eq
  split at hstep_eq -- exprValue? body
  · -- body is value: tryCatch resolves to body value (no finally) or finally block
    split at hstep_eq -- finally_
    · -- no finally: step to value
      obtain ⟨-, rfl⟩ := hstep_eq
      -- Need: Flat.Steps through tryCatch resolution
      -- sf.expr = .tryCatch f_body f_catch f_finally
      -- Flat also has tryCatch, body is value → steps to value
      sorry
    · -- with finally: step to finally block
      sorry
  · -- body not value
    split at hstep_eq -- step? body
    · -- step? body = some (ev, sa'): body takes a step
      -- Use SimRel: body stepping inside tryCatch context
      sorry
    · -- step? body = none: contradiction with not-value
      simp at hstep_eq
```

**Key insight**: First determine what Flat.Expr produces .tryCatch through normalizeExpr. Use `lean_hover_info` on `normalizeExpr` to check — likely only `.tryCatch` produces `.tryCatch`.

## TASK 2: Close L9079/9083/9084 (let compound) — IF TIME

These are in `normalizeExpr_let_step_sim` after lit/var/this/break/continue are dispatched.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L9273-9322 (if compound infrastructure) ONLY
- You work on L9536 and L9079-9084 ONLY
- DO NOT touch lines 9260-9500 (except L9536 area)

## PRIORITY ORDER
1. L9536 (tryCatch step sim) — most tractable remaining sorry
2. L9079/9083/9084 (let compound) — harder, if time permits

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
