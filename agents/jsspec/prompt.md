# jsspec — Close remaining Core_step_preserves_supported cases + CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: 6 Core_step_preserves_supported cases STILL OPEN (L3806-3811)

You closed getProp and setProp last run — great. But getIndex/setIndex/call/objectLit/arrayLit/tryCatch are STILL SORRY. Fix them first before moving to other tasks.

CC has 20 sorries total:
- L2965, L2983: helper lemma sorries (listSupported_firstNonValue_parts, propListSupported_firstNonValue_parts)
- L3806-3811: 6 Core_step_preserves_supported remaining cases
- L3877: captured variable sorry
- L4206, L4229: CCStateAgree if-branches
- L4793: funcs correspondence
- L5001, L5009: semantic mismatch (Core alloc vs Flat step)
- L5647: UNPROVABLE getIndex string
- L6889: functionDef case
- L7046, L7047: tryCatch CCStateAgree
- L7119: tryCatch inner
- L7227: while_ CCState threading

## TASK 1: Close L3806 (getIndex with value obj) — HIGHEST PRIORITY

The obj is already `.lit ov` (subst done). You need to handle idx value/non-value, EXACTLY like setProp (L3766-3786) does.

```lean
-- Replace the sorry at L3806 with:
      cases hval_i : Core.exprValue? idx with
      | none =>
        cases h_sub : Core.step? { s with expr := idx } with
        | none => simp [Core.step?, Core.exprValue?, hval_i, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_getIndex_step_idx (.lit ov) idx s.env s.heap s.trace s.funcs s.callStack hval_i t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
          exact ⟨trivial, ih idx.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := idx } sa t (Nat.le_refl _) hsupp.2 h_sub⟩
      | some iv =>
        have hlit_i : idx = .lit iv := by cases idx <;> simp [Core.exprValue?] at hval_i; subst hval_i; rfl
        subst hlit_i
        cases ov <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
          (try (obtain ⟨-, rfl⟩ := hstep; rfl)) <;>
          (try (split at hstep <;> (try split at hstep) <;> (obtain ⟨-, rfl⟩ := hstep; rfl)))
```

**If `step_getIndex_step_idx` doesn't exist**, use `lean_local_search` to find the correct helper name, or create it following the pattern of `Core.step_setProp_step_value`.

## TASK 2: Close L3807 (setIndex) — same pattern as setProp

setIndex has 3 sub-expressions (obj, idx, value). Follow the exact 3-level pattern from setProp (L3742-3786), with one more nesting level for the third argument. Use `lean_local_search` for forward lemma names.

## TASK 3: Close L3808 (call) — needs FuncsSupported

This needs a `FuncsSupported` hypothesis. Add it to Core_step_preserves_supported:
```lean
(hfuncs : ∀ (i : Nat) (c : Core.Closure), s.funcs[i]? = some c → c.body.supported = true)
```

Then at the call case when callee and args are all values:
```lean
have hcl := hfuncs idx closure ‹_›
-- use hcl : closure.body.supported = true
```

Update the IH calls to thread hfuncs (step? preserves funcs, so the same hypothesis propagates).

## TASK 4: Close L3809/L3810 (objectLit/arrayLit)

These need list induction. First prove L2965 (listSupported_firstNonValue_parts) and L2983 (propListSupported_firstNonValue_parts) — these are straightforward inductions on the list with case analysis on firstNonValueExpr/firstNonValueProp.

Then objectLit/arrayLit follow the pattern: decompose via firstNonValue*, use IH on the target element, reassemble via replace_target.

## TASK 5: Close L3811 (tryCatch)

Use `lean_goal` at L3811 to see what's needed. Pattern: case split on body value/error, then show supported is preserved through each branch.

## PRIORITY ORDER
1. L3806 (getIndex) — template code above, paste and adjust
2. L3807 (setIndex) — copy-adapt from setProp
3. L2965, L2983 (helper lemmas) — unblock objectLit/arrayLit
4. L3809, L3810 (objectLit/arrayLit) — use helpers
5. L3808 (call) — needs FuncsSupported change
6. L3811 (tryCatch)
7. Other CC sorries (lower priority)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
