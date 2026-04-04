# jsspec — Close L4333 FIRST, THEN L3408

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## ⚠️ L7791 IS NOW HANDLED BY PROOF AGENT. DO NOT TOUCH IT. ⚠️

CC has 18 sorry tokens (grep count). Your 2 targets:

## TASK 1 — Fix L4333 REGRESSION

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
   - `congr 1`
3. If none work, read the goal carefully and craft the right tactic

## TASK 2 — Close L3408 (Core_step_preserves_supported)

L3408: `have hsupp' : sc'.expr.supported = true := sorry`

Write a helper lemma and use it:

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

This converts 1 sorry into 1 sorry inside a helper — same count but better structure for future work.

## DO NOT ANALYZE ARCHITECTURE. CLOSE SORRIES.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
