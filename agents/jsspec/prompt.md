# jsspec — CLOSE L7791 FIRST (5 min), THEN L4333, THEN L3408

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ AGENTS HAVE BEEN IDLE FOR 4+ DAYS. ZERO SORRIES CLOSED. ⚠️
## ⚠️ STOP ANALYZING. START CLOSING. ⚠️

CC has 15 real sorries. Your 3 targets are below. Do them IN ORDER.

## TASK 1 — Close L7791 (TRIVIAL — 5 MINUTES MAX)

L7791 is:
```lean
  have h_supp : s.body.supported = true := sorry /- TODO: add h_supp param when EndToEnd.lean is updated -/
```

This is inside `closureConvert_correct` (search for it near L7783). Fix:

1. Find the theorem signature: `grep -n "theorem closureConvert_correct" VerifiedJS/Proofs/ClosureConvertCorrect.lean`
2. Add `(h_supp : s.body.supported = true)` as a new parameter
3. DELETE the sorry line at L7791 entirely (the `have h_supp` line)
4. Find caller: `grep -n "closureConvert_correct" VerifiedJS/Proofs/EndToEnd.lean`
5. Pass `h_supported` (from EndToEnd theorem) at the call site
6. Build BOTH:
   - `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
   - `lake build VerifiedJS.Proofs.EndToEnd`

This is a PARAMETER ADDITION. No proof work. 5 minutes.

## TASK 2 — Fix L4333 REGRESSION

L4333: `· sorry /- was: convert hcore using 2 — tactic unavailable -/`

1. Use `lean_goal` at L4333 col 9 to see the goal
2. Try `lean_multi_attempt` with:
   - `exact hcore`
   - `convert hcore using 3`
   - `convert hcore using 1`
   - `simp only [sc'] at hcore ⊢; exact hcore`
   - `exact hcore.1`
   - `cases hcore; assumption`
   - `rw [show sc'.expr = _ from rfl] at hcore; exact hcore`
3. If none work, read the goal and craft the right tactic

## TASK 3 — Close L3408 (Core_step_preserves_supported)

L3408: `have hsupp' : sc'.expr.supported = true := sorry`

Write a helper lemma (even with inner sorries) and use it:

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

Place above L3405 and replace L3408 with:
```lean
    have hsupp' : sc'.expr.supported = true := Core_step_preserves_supported _ _ _ hsupp hstep
```

This converts 1 sorry into 1 sorry inside a helper — same count but better structure.

## DO NOT ANALYZE ARCHITECTURE. CLOSE SORRIES.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
