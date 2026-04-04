# jsspec — Close L3408 THIS RUN. No excuses.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 14 real sorries. L3408 is your #1 target. L7787 is #2.

## ⚠️ YOU HAVE BEEN RUNNING 2+ HOURS WITH NO SORRY REDUCTION. FOCUS. ⚠️

The supported migration was good architectural work, but L3408 still has sorry. Close it NOW.

## TASK 1 — Close L3408 (Core.step preserves supported) — DO THIS FIRST

L3408 is:
```lean
have hsupp' : sc'.expr.supported = true := sorry /- TODO: prove Core.step preserves supported -/
```

### EXACT STEPS:

1. Find Core.step? definition: `lean_local_search "Core.step?"` or `lean_hover_info` on it
2. Find Core.Expr.supported definition: `lean_hover_info` on `supported`
3. Write the lemma ABOVE L3408:

```lean
private theorem Core_step_preserves_supported (sc sc' : Core.State) (ev : Core.TraceEvent)
    (hsupp : sc.expr.supported = true)
    (hstep : Core.step? sc = some (ev, sc')) :
    sc'.expr.supported = true := by
  obtain ⟨expr, env, heap, trace, funcs, cs⟩ := sc
  simp only [Core.State.expr] at hsupp
  -- Strong induction on depth for context-stepping cases
  suffices ∀ n e, e.depth ≤ n → ∀ env heap trace funcs cs ev sc',
    e.supported = true →
    Core.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sc') →
    sc'.expr.supported = true from this _ _ (le_refl _) _ _ _ _ _ hsupp hstep
  intro n
  induction n with
  | zero => intro e hd; cases e <;> simp [Core.Expr.depth] at hd <;> omega
  | succ n ih =>
    intro e hd env heap trace funcs cs ev sc' hsupp hstep
    cases e with
    | lit v => simp [Core.step?] at hstep  -- lit doesn't step
    | var name =>
      -- steps to .lit v → supported = true trivially
      simp [Core.step?] at hstep
      split at hstep <;> simp_all [Core.Expr.supported]
    -- ... each constructor
    | forIn _ _ _ => simp [Core.Expr.supported] at hsupp  -- contradiction
    | forOf _ _ _ => simp [Core.Expr.supported] at hsupp  -- contradiction
    | _ => sorry  -- fill in remaining cases
```

4. Replace L3408: `have hsupp' := Core_step_preserves_supported sc sc' ev hsupp hcstep`

### KEY INSIGHT: `Core.Expr.supported` returns false ONLY for `forIn` and `forOf`. For ALL other constructors it's `true ∧ (recursive on children)`. So:
- forIn/forOf cases: `simp [Core.Expr.supported] at hsupp` gives contradiction
- Value cases (lit): step? returns none → contradiction
- Simple cases (var, this): step? produces .lit → supported = true
- Context cases (seq, let, etc.): IH on sub-expression via depth

Even getting a lemma with 5 sorry sub-cases and using it at L3408 is progress over a standalone sorry.

## TASK 2 — Close L7787 (h_supp parameter)

L7787: `have h_supp : s.body.supported = true := sorry`

Fix:
1. Add `(h_supp : s.body.supported = true)` parameter to `closureConvert_correct` at ~L7779
2. Delete the sorry line
3. Find EndToEnd.lean caller: `grep -n "closureConvert_correct" VerifiedJS/Proofs/EndToEnd.lean`
4. Add `h_supported` (from top-level theorem) as the argument

## DO NOT:
- Touch L4549, L4557 (semantic mismatch — compiler bug)
- Touch L6437 (functionDef — HeapInj blocked)
- Touch L5195 (unprovable)
- Touch L3764, L3787 (CCStateAgree architecture)
- Touch L6594, L6595, L6667 (CCStateAgree blocked)
- Touch L6775 (while_ CCState threading)
- Touch L4341 (FuncsCorr blocked)
- Edit ANFConvertCorrect.lean
- Spend time on architecture analysis — CLOSE SORRIES

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
