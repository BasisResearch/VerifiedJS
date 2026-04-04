# jsspec — TASK 1 DONE. Now close the 2 new supported sorries.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 14 real sorries. You eliminated forIn/forOf (GOOD). 2 new provable sorries from supported infra.

## TASK 1 — Close L3408 (Core.step preserves supported)

L3408 is:
```lean
have hsupp' : sc'.expr.supported = true := sorry /- TODO: prove Core.step preserves supported -/
```

Write a lemma `Core_step_preserves_supported`:
```lean
theorem Core_step_preserves_supported (sc sc' : Core.State) (ev : Core.TraceEvent)
    (hsupp : sc.expr.supported = true)
    (hstep : Core.step? sc = some (ev, sc')) :
    sc'.expr.supported = true := by
  -- cases on sc.expr, unfold Core.step? in hstep
  -- For each case: sub-expressions are supported by simp on hsupp
  -- Resulting expression: either sub-expression (supported by IH) or .lit (trivially supported)
  sorry
```

This is ~40-80 lines: unfold `Core.step?`, case split, then for each constructor show that the result expression's `supported` field follows from the input's `supported`. Key insight: `Core.Expr.supported` is defined as AND of all sub-expressions' `supported`, so `simp [Core.Expr.supported] at hsupp` extracts sub-expression supported facts.

Use `lean_hover_info` on `Core.step?` and `Core.Expr.supported` to see all cases. Use `lean_multi_attempt` to test approaches.

After proving the lemma, replace `sorry` at L3408 with `Core_step_preserves_supported sc sc' ev hsupp hcstep`.

## TASK 2 — Close L7787 (h_supp parameter)

L7787 is:
```lean
have h_supp : s.body.supported = true := sorry /- TODO: add h_supp param when EndToEnd.lean is updated -/
```

This is in `closureConvert_correct` (the end-to-end CC theorem). Fix:
1. Add `(h_supp : s.body.supported = true)` as a parameter to `closureConvert_correct`
2. Delete the sorry'd `have` line
3. Check if `EndToEnd.lean` calls `closureConvert_correct` — if so, update the call site to pass the supported hypothesis
4. Build and verify

## TASK 3 (ONLY AFTER TASKS 1-2): L3435 captured variable step

L3435 is the captured variable case (`.getEnv (.var envVar) idx` needs 2 Flat steps vs 1 Core step). Investigate if the multi-step infrastructure from `closureConvert_steps_simulation` can handle this, or if a specialized `getEnv_var_two_step` lemma is needed.

## DO NOT:
- Touch L4549, L4557 (semantic mismatch — compiler needs changing)
- Touch L6437 (functionDef — HeapInj blocked)
- Touch L5195 (unprovable)
- Edit ANFConvertCorrect.lean

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
