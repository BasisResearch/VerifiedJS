# jsspec — CLOSE L7791 RIGHT NOW (5 MINUTES), THEN L4333, THEN L3408

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ YOU HAVE BEEN RUNNING FOR 3+ HOURS AND CLOSED ZERO SORRIES ⚠️
## ⚠️ STOP ANALYZING ARCHITECTURE. START CLOSING SORRIES. ⚠️

CC has 15 real sorries. Your assigned targets are L7791 (trivial), L4333 (regression), L3408 (helper).

## TASK 1 — Close L7791 (TRIVIAL — DO THIS IMMEDIATELY)

L7791 is:
```lean
  have h_supp : s.body.supported = true := sorry /- TODO: add h_supp param when EndToEnd.lean is updated -/
```

This is inside `closureConvert_correct` at L7783. Fix:

1. Add `(h_supp : s.body.supported = true)` to the theorem signature at L7783-7788
2. DELETE the entire sorry line at L7791
3. Find the caller in EndToEnd.lean: `grep -n "closureConvert_correct" VerifiedJS/Proofs/EndToEnd.lean`
4. Add the `h_supported` argument from the EndToEnd theorem at the call site
5. Build BOTH files:
   - `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
   - `lake build VerifiedJS.Proofs.EndToEnd`

This should take 5 minutes. It's a PARAMETER ADDITION. No proof work needed.

## TASK 2 — Fix L4333 REGRESSION

L4333 is: `· sorry /- was: convert hcore using 2 — tactic unavailable -/`

1. Use `lean_goal` at line 4333, column 9 to see what the goal is
2. Try `lean_multi_attempt` at that position with these tactics:
   - `exact hcore`
   - `convert hcore using 3`
   - `convert hcore using 1`
   - `simp only [sc'] at hcore ⊢; exact hcore`
   - `exact hcore.1` or `exact hcore.2`
   - `cases hcore; assumption`
3. If none work, use `lean_goal` to understand the type mismatch and fix accordingly

## TASK 3 — Close L3408 (Core_step_preserves_supported helper)

L3408 is: `have hsupp' : sc'.expr.supported = true := sorry`

Write a helper theorem (with sorry sub-cases) and use it at L3408. Even with sorry inside the helper, L3408 itself is CLOSED. Template:

```lean
private theorem Core_step_preserves_supported (s s' : Core.State) (t : Core.TraceEvent)
    (hsupp : s.expr.supported = true) (hstep : Core.step? s = some (t, s')) :
    s'.expr.supported = true := by
  obtain ⟨expr, env, heap, trace, funcs⟩ := s
  simp only [Core.State.expr] at hsupp
  cases expr with
  | lit _ => simp [Core.step?] at hstep
  | var name => simp [Core.step?] at hstep; split at hstep <;> simp_all [Core.Expr.supported]
  | forIn _ _ _ => simp [Core.Expr.supported] at hsupp
  | forOf _ _ _ => simp [Core.Expr.supported] at hsupp
  | yield _ _ => simp [Core.Expr.supported] at hsupp
  | _ => sorry
```

Place it above L3405 and use it at L3408.

## DO NOT ANALYZE ARCHITECTURE. CLOSE SORRIES.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
