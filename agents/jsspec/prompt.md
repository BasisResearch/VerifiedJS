# jsspec — FIX L4333 REGRESSION, CLOSE L7791, THEN L3408

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 15 real sorries (UP FROM 14 — YOU INTRODUCED A REGRESSION AT L4333).

## ⚠️ SORRY COUNT WENT UP. FIX IT BEFORE ANYTHING ELSE. ⚠️

## TASK 0 — FIX L4333 REGRESSION (DO THIS FIRST — 5 MINUTES)

L4333 is: `· sorry /- was: convert hcore using 2 — tactic unavailable -/`

This broke during your supported migration. `convert hcore using 2` no longer works because CC_SimRel changed. Fix it:

1. Use `lean_goal` at L4333 to see what the goal is
2. Try these tactics with `lean_multi_attempt` at L4333:
   - `exact hcore`
   - `convert hcore using 3`
   - `convert hcore using 1`
   - `simp only [sc'] at hcore ⊢; exact hcore`
   - `rw [show sc.trace ++ [ev] = sc.trace ++ [ev] from rfl]; exact hcore`
3. If none work, check what field `CC_SimRel` gained and ensure `hcore` matches the new shape
4. This MUST be fixed — you cannot leave regressions.

## TASK 1 — Close L7791 (EASIEST — do this in 5 minutes)

L7791 is: `have h_supp : s.body.supported = true := sorry`

This is just a missing parameter. Fix:
1. Find the theorem signature above L7791. Add `(h_supp : s.body.supported = true)` as a parameter.
2. Delete the sorry line at L7791.
3. Find the caller: `grep -n "closureConvert_correct" VerifiedJS/Proofs/EndToEnd.lean`
4. Add `h_supported` (from the top-level theorem's hypothesis) as the new argument at the call site.
5. Build CC. Fix any errors.

## TASK 2 — Close L3408 (Core_step_preserves_supported)

L3408 is: `have hsupp' : sc'.expr.supported = true := sorry /- TODO: prove Core.step preserves supported -/`

### STEP A: Write the helper WITH sorry sub-cases (this is fine!)

Find Core.step? definition: `grep -n "def step?" VerifiedJS/Core/Semantics.lean`
Then write this helper ABOVE line ~3405:

```lean
private theorem Core_step_preserves_supported (s s' : Core.State) (t : Core.TraceEvent)
    (hsupp : s.expr.supported = true) (hstep : Core.step? s = some (t, s')) :
    s'.expr.supported = true := by
  obtain ⟨expr, env, heap, trace, funcs⟩ := s
  simp only [Core.State.expr] at hsupp
  cases expr with
  | lit _ => simp [Core.step?] at hstep
  | var name =>
    simp [Core.step?] at hstep
    split at hstep <;> simp_all [Core.Expr.supported]
  | forIn _ _ _ => simp [Core.Expr.supported] at hsupp
  | forOf _ _ _ => simp [Core.Expr.supported] at hsupp
  | yield _ _ => simp [Core.Expr.supported] at hsupp
  | _ => sorry -- fill remaining constructors; each follows same pattern
```

### STEP B: Use it at L3408

Replace the sorry at L3408 with:
```lean
    have hsupp' : sc'.expr.supported = true := Core_step_preserves_supported sc sc' ev hsupp (by cases hcstep; assumption)
```

### STEP C: Build and verify

Even with sorry sub-cases in the helper, L3408 itself is CLOSED. That's -1 sorry at the usage site, +1 sorry in the helper = net 0, BUT the helper sorry is more tractable.

**IMPORTANT**: If the `by cases hcstep; assumption` doesn't work at L3408, try:
- `(by exact hcstep.step_eq)` or whatever extracts the step? from Core.Step
- Read the Core.Step definition: `grep -n "inductive Step\|structure Step" VerifiedJS/Core/Semantics.lean`

## DO NOT:
- Touch L4553, L4561 (semantic mismatch — compiler bug)
- Touch L6441 (functionDef — HeapInj blocked)
- Touch L5199 (unprovable)
- Touch L3764, L3787 (CCStateAgree architecture)
- Touch L6598, L6599, L6671 (CCStateAgree blocked)
- Touch L6779 (while_ CCState threading)
- Touch L4345 (FuncsCorr blocked)
- Touch L3435 (captured var multi-step)
- Edit ANFConvertCorrect.lean
- Write analysis instead of code
- Spend more than 10 minutes reading before writing code

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
