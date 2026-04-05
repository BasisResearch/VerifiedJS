# proof — Close tryCatch step sim + let compound in ANF

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: hasAbruptCompletion_step_preserved + NoNestedAbrupt_step_preserved PROVED!

Current ANF sorry count: 26
- L7701-7887 (7): normalizeExpr_labeled eval context — PARKED
- L8531-9023 (7): compound HasX — PARKED
- L9079, 9083, 9084 (3): let compound (return/yield some + general) — needs structural induction
- L9174, 9186 (2): while step sim — needs multi-step simulation
- L9367, 9368, 9440, 9441 (4): if compound — wasmspec owns these, DON'T TOUCH
- L9485 (1): tryCatch step sim — YOUR TARGET
- L10785, 10838 (2): break/continue compound — PARKED

## TASK 1: Close L9485 (tryCatch step sim) — HIGHEST PRIORITY

This is in `tryCatch_step_sim` at L9485. Use `lean_goal` at L9485 to see the exact proof state.

Pattern:
```lean
  simp only [ANF.step?, ANF.pushTrace] at hstep_eq
  split at hstep_eq -- exprValue? body
  · -- body is value: tryCatch resolves
    split at hstep_eq -- finally_
    · -- no finally: step to value
      obtain ⟨-, rfl⟩ := hstep_eq
      -- Flat form: need to show Flat.Steps through tryCatch body-value resolution
      sorry
    · -- with finally: step to finally block
      sorry
  · -- body not value
    split at hstep_eq -- step? body
    · -- step? body = some (ev, sa'): body takes a step
      -- Flat form also steps within the body of the tryCatch
      sorry
    · -- step? body = none: contradiction
      simp at hstep_eq
```

For the body-steps sub-case, use the existing SimRel + IH on the body sub-expression.

## TASK 2: Close L9079/9083/9084 (let compound) — IF TIME

These are in `let_step_sim` after lit/var/this/break/continue are dispatched:
- L9079: return (some val) — compound, can produce .let
- L9083: yield (some val) — compound, can produce .let
- L9084: general compound — needs structural induction on Flat.Expr

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L9367-9441 (if compound) ONLY
- You work on L9485 and L9079-9084 ONLY
- DO NOT touch lines 9300-9450

## PRIORITY ORDER
1. L9485 (tryCatch step sim) — most tractable remaining sorry
2. L9079/9083/9084 (let compound) — harder, if time permits

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
