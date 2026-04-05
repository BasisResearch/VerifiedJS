# proof — hasAbrupt + NoNestedAbrupt DONE! Now close remaining ANF sorries.

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

## STATUS: hasAbruptCompletion_step_preserved + NoNestedAbrupt_step_preserved PROVED! GREAT WORK.

Current ANF sorry count: 24
- L7701-7887 (7): eval context lifting — PARKED (needs Flat.step? error propagation)
- L8531-9023 (7): compound HasX — PARKED (same blocker)
- L9067 (1): let compound in let_step_sim — needs structural induction
- L9157, 9169 (2): while step sim — needs multi-step simulation
- L9350, 9351, 9423, 9424 (4): if compound — wasmspec is working on these, DON'T TOUCH
- L9468 (1): tryCatch step sim
- L10768, 10821 (2): break/continue compound — PARKED (same Flat.step? error propagation blocker)

## TASK 1: Close L9468 (tryCatch step sim) — HIGHEST PRIORITY

This is in `tryCatch_step_sim`. The ANF step on `.tryCatch body catchParam catchBody finally_` involves:
- body value case: body done, step to continuation (with/without finally)
- body error case: body threw, step to catch handler (with/without finally)
- body stepping: body takes a step, wrap result back in tryCatch

Use `lean_goal` at L9468 to see the exact proof state.

Pattern:
```lean
  simp only [ANF.step?, ANF.pushTrace] at hstep_eq
  split at hstep_eq -- exprValue? body
  · -- body is value: step to continuation
    sorry
  · -- body not value
    split at hstep_eq -- step? body
    · sorry -- step? body = some (ev, sa')
    · -- step? body = none: contradiction
      simp at hstep_eq
```

For the body-steps sub-case, you need to show the Flat form also steps within the body. Use the `normalizeExpr` structure.

## TASK 2: Close L9067 (let compound expression) — IF TIME

At L9067: `| _ => sorry -- compound expression: needs structural induction on Flat.Expr`

This is in `let_step_sim` after lit/var/this/break/continue are dispatched. The remaining cases are compound expressions (seq, let, if, etc.) that appear in the let-init position. Need to show Flat can simulate the ANF step within the compound init.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L9350-9424 (if compound) ONLY
- You work on L9468 and L9067 ONLY
- DO NOT touch lines 9300-9430

## PRIORITY ORDER
1. L9468 (tryCatch step sim) — most tractable remaining sorry
2. L9067 (let compound) — harder, if time permits

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
