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

## TASK 1 — Fix L4333 REGRESSION (HIGHEST PRIORITY)

L4333: `· sorry /- was: convert hcore using 2 — tactic unavailable -/`

Context: This is inside the consoleLog call case. `hcore` proves `Core.step? sc = some (ev, sc')` for some sc'. The goal at L4333 is likely `Core.Step sc ev sc'` (the inductive step wrapper around step?).

**Strategy**: Look at the `Core.Step` definition. If it's a wrapper around `step?`:
```lean
inductive Core.Step (s : Core.State) (ev : Core.TraceEvent) (s' : Core.State) : Prop where
  | mk : s.step? = some (ev, s') → Core.Step s ev s'
```
Then the proof is simply `exact Core.Step.mk hcore` or `constructor; exact hcore`.

Try these tactics in order:
1. `exact Core.Step.mk hcore`
2. `constructor; exact hcore`
3. `exact ⟨hcore⟩`
4. `exact hcore`
5. Use `lean_goal` at L4333 col 9 to see the actual goal, then match

## TASK 2 — Close L3408 (Core_step_preserves_supported)

L3408: `have hsupp' : sc'.expr.supported = true := sorry`

This needs a helper lemma proving Core.step preserves `supported`. Write it:

```lean
private theorem Core_step_preserves_supported (s s' : Core.State) (ev : Core.TraceEvent)
    (hsupp : s.expr.supported = true) (hstep : Core.step? s = some (ev, s')) :
    s'.expr.supported = true := by
  obtain ⟨expr, env, heap, trace, funcs, callStack⟩ := s
  simp only [Core.State.expr] at hsupp
  cases expr with
  | lit _ => simp [Core.step?] at hstep
  | var name => simp [Core.step?] at hstep; split at hstep <;> simp_all [Core.Expr.supported]
  | forIn _ _ _ => simp [Core.Expr.supported] at hsupp
  | forOf _ _ _ => simp [Core.Expr.supported] at hsupp
  | yield _ _ => simp [Core.Expr.supported] at hsupp
  | _ => sorry  -- remaining cases need case analysis on step?
```

Place above L3405 and replace L3408's sorry:
```lean
    have hsupp' := Core_step_preserves_supported _ _ _ hsupp (by obtain ⟨h⟩ := hcstep; exact h)
```

Wait — `hcstep` is `Core.Step sc ev sc'`. You need to extract `step?` from it. Check if `Core.Step` has a field like `.step_eq` or use `cases hcstep with | mk h => ...`.

This converts 1 deep sorry into 1 sorry inside a helper — same count but better structure.

## DO NOT ANALYZE ARCHITECTURE. CLOSE SORRIES.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
