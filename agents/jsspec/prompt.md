# jsspec — Close L3408 and L7787. Two easy wins.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 14 real sorries. You eliminated forIn/forOf and tryCatch non-error (GOOD). Now close the 2 supported infrastructure sorries.

## TASK 1 — Close L3408 (Core.step preserves supported) — HIGHEST PRIORITY

L3408 is:
```lean
have hsupp' : sc'.expr.supported = true := sorry /- TODO: prove Core.step preserves supported -/
```

Write a lemma ABOVE this line:
```lean
private theorem Core_step_preserves_supported (sc sc' : Core.State) (ev : Core.TraceEvent)
    (hsupp : sc.expr.supported = true)
    (hstep : Core.step? sc = some (ev, sc')) :
    sc'.expr.supported = true := by
  simp only [Core.step?] at hstep
  cases sc.expr with
  | lit v => simp at hstep
  | var name => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Core.Expr.supported]
  -- etc: each constructor unfolds step?, extracts sc', shows sc'.expr.supported
  | seq a b =>
    simp [Core.Expr.supported] at hsupp
    -- case split on exprValue? a; if value steps to b (supported from hsupp)
    -- if non-value, steps to .seq a' b where a' has same supported
    sorry
  -- ... all other cases
```

Use `lean_hover_info` on `Core.step?` and `Core.Expr.supported` to see exact definitions. Use `lean_multi_attempt` at each case.

Then replace L3408 sorry with:
```lean
have hsupp' : sc'.expr.supported = true := Core_step_preserves_supported sc sc' ev hsupp hcstep
```

## TASK 2 — Close L7787 (h_supp parameter) — QUICK WIN

L7787 is:
```lean
have h_supp : s.body.supported = true := sorry /- TODO: add h_supp param when EndToEnd.lean is updated -/
```

This is in `closureConvert_correct`. Fix:
1. Add `(h_supp : s.body.supported = true)` as a parameter to `closureConvert_correct`
2. Delete the sorry'd `have` line at L7787
3. Check if anything calls `closureConvert_correct` — grep for it: `grep -n "closureConvert_correct" VerifiedJS/Proofs/ClosureConvertCorrect.lean VerifiedJS/*.lean`
4. If EndToEnd.lean calls it, add `h_supported` (which should exist from the top-level theorem) as the argument
5. Build and verify

## TASK 3 (ONLY AFTER 1-2): L3435 captured variable

L3435 is the captured variable multi-step case. Investigate with `lean_goal` at L3435 to see the exact proof state, then determine if a 2-step simulation lemma is needed.

## DO NOT:
- Touch L4549, L4557 (semantic mismatch — compiler bug)
- Touch L6437 (functionDef — HeapInj blocked)
- Touch L5195 (unprovable)
- Touch L3764, L3787 (CCStateAgree architecture issue)
- Edit ANFConvertCorrect.lean

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
