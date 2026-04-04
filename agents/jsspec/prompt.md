# jsspec — YOU HAVE NOT CLOSED A SINGLE SORRY IN 4 DAYS. CLOSE L3408 AND L7787 NOW.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 14 real sorries. You can close 2 of them THIS RUN.

## ⚠️ STOP ANALYZING. START WRITING CODE. ⚠️
Your last 4 runs produced ZERO sorry reductions and thousands of lines of analysis.
The analysis is done. The architecturally-blocked sorries are NOT your targets.
L3408 and L7787 ARE provable. Write the code NOW.

## TASK 1 — Close L7787 (EASIEST — do this FIRST, in 5 minutes)

L7787 is: `have h_supp : s.body.supported = true := sorry`

This is just a missing parameter. Fix:
1. Find the theorem signature above L7787. Add `(h_supp : s.body.supported = true)` as a parameter.
2. Delete the sorry line at L7787.
3. Find the caller: `grep -n "closureConvert_correct" VerifiedJS/Proofs/EndToEnd.lean`
4. Add `h_supported` (from the top-level theorem's hypothesis) as the new argument at the call site.
5. Build CC. Fix any errors.

This is a 5-minute task. Do it FIRST.

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

Even with sorry sub-cases in the helper, L3408 itself is CLOSED. That's -1 sorry at the usage site, +1 sorry in the helper = net 0, BUT the helper sorry is more tractable and can be filled in incrementally.

**IMPORTANT**: If the `by cases hcstep; assumption` doesn't work at L3408, try:
- `(by exact hcstep.step_eq)` or whatever extracts the step? from Core.Step
- Read the Core.Step definition: `grep -n "inductive Step\|structure Step" VerifiedJS/Core/Semantics.lean`

### STEP D: Fill in easy constructor cases

After the helper compiles, try filling in `seq`, `let`, `assign`, `if` — they follow the same pattern:
```lean
    | seq a b =>
      simp [Core.Expr.supported] at hsupp
      simp [Core.step?] at hstep
      split at hstep
      · simp_all [Core.Expr.supported]  -- value case: result is b, which is supported
      · split at hstep
        · sorry -- non-value: step a, reconstruct .seq a' b — needs depth induction
        · simp at hstep
```

## DO NOT:
- Touch L4549, L4557 (semantic mismatch — compiler bug)
- Touch L6437 (functionDef — HeapInj blocked)
- Touch L5195 (unprovable)
- Touch L3764, L3787 (CCStateAgree architecture)
- Touch L6594, L6595, L6667 (CCStateAgree blocked)
- Touch L6775 (while_ CCState threading)
- Touch L4341 (FuncsCorr blocked)
- Touch L3435 (captured var multi-step)
- Edit ANFConvertCorrect.lean
- Write analysis instead of code
- Spend more than 10 minutes reading before writing code

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
