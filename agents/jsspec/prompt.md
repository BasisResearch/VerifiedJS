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

## ⚠️ SORRY COUNT HAS BEEN FLAT FOR 4+ DAYS. CLOSE L3408 NOW. ⚠️

## TASK 1 — Close L3408 (Core.step preserves supported)

L3408 is:
```lean
have hsupp' : sc'.expr.supported = true := sorry /- TODO: prove Core.step preserves supported -/
```

Context: `hcstep : Core.Step sc ev sc'` where `Core.Step` wraps `Core.step?` (defined at VerifiedJS/Core/Semantics.lean:6972). Also `hsupp : sc.expr.supported = true` is available (from the suffices at L3405).

### KEY FACTS about Core.Expr.supported (VerifiedJS/Core/Syntax.lean:138-165):
- Returns `false` ONLY for: `.forIn`, `.forOf`, `.yield`
- For all other constructors: returns `true` (terminal) or `&&` of children's supported
- `_ => true` catches: lit, var, break, continue, return none, this

### APPROACH: Write a helper lemma, use it at L3408

Write this ABOVE L3405 (before the `by` block):

```lean
private theorem Core_step_preserves_supported (s s' : Core.State) (t : Core.TraceEvent)
    (hsupp : s.expr.supported = true) (hstep : Core.step? s = some (t, s')) :
    s'.expr.supported = true := by
  -- Core.step? recurses into sub-expressions. When stepping a compound expression,
  -- the result either:
  --   (a) replaces with a child (value case) → child was `supported` by &&
  --   (b) steps a child in context → IH on child
  --   (c) forIn/forOf/yield → hsupp gives false → contradiction
  obtain ⟨expr, env, heap, trace, funcs⟩ := s
  simp only [Core.State.expr] at hsupp
  suffices ∀ n (e : Core.Expr), e.depth ≤ n → ∀ env heap trace funcs t s',
    e.supported = true →
    Core.step? ⟨e, env, heap, trace, funcs⟩ = some (t, s') →
    s'.expr.supported = true from this _ _ (le_refl _) _ _ _ _ _ hsupp hstep
  intro n
  induction n with
  | zero => intro e hd; cases e <;> simp [Core.Expr.depth] at hd <;> omega
  | succ n ih =>
    intro e hd env heap trace funcs t s' hsupp hstep
    cases e with
    | lit _ => simp [Core.step?] at hstep  -- lit doesn't step → contradiction
    | var name =>
      simp [Core.step?] at hstep
      split at hstep <;> simp_all [Core.Expr.supported]
    | forIn _ _ _ => simp [Core.Expr.supported] at hsupp
    | forOf _ _ _ => simp [Core.Expr.supported] at hsupp
    | yield _ _ => simp [Core.Expr.supported] at hsupp
    | seq a b =>
      simp [Core.Expr.supported] at hsupp
      obtain ⟨ha, hb⟩ := Bool.and_eq_true.mp hsupp
      simp [Core.step?] at hstep
      sorry -- split on exprValue? a; value → hb; non-value → IH on a + reconstruct
    | _ => sorry  -- fill remaining constructors one by one
```

Then at L3408 replace:
```lean
    have hsupp' : sc'.expr.supported = true := Core_step_preserves_supported sc sc' ev hsupp (by cases hcstep; assumption)
```

### EVEN 1 SORRY REDUCTION IS PROGRESS. Get the lemma in place (even with sorry sub-cases) and use it at L3408.

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
