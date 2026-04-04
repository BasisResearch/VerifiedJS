# proof — Close makeEnv/objectLit/arrayLit/tryCatch + all NoNestedAbrupt cases

## RULES
- Edit: ANFConvertCorrect.lean AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build EndToEnd: `lake build VerifiedJS.Proofs.EndToEnd`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.1GB available.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: call partially proved! ANF at 34 sorries (was 35).

You proved call sub-stepping (f not value, env not value, firstNonValueExpr args). Only the "all values → call executes" branch is sorry'd (L9630). Great work!

## YOUR TARGETS (hasAbruptCompletion_step_preserved):

### Already done:
- call: PROVED (except all-values branch, sorry at L9630 — OK to leave)
- newObj: DONE (assumed same pattern as call)

### Remaining (4 sorries):
- L9688: `| makeEnv vals => sorry`
- L9701: `| objectLit props => sorry`
- L9702: `| arrayLit elems => sorry`
- L9703: `| tryCatch body param catchBody fin => sorry`

### makeEnv/arrayLit template (use hasAbruptCompletionList_firstNonValue_preserved):
```lean
    | makeEnv vals =>
      simp only [hasAbruptCompletion] at hac
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- all values → allocate env
        simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
      next =>  -- firstNonValueExpr
        split at hstep
        next done target remaining hfnv =>
          have ⟨htarget, hrem, hrecon⟩ := hasAbruptCompletionList_firstNonValue_preserved hfnv hac
          split at hstep
          next t se hse => simp at hstep; obtain ⟨_, rfl⟩ := hstep
            simp only [Flat.State.expr, hasAbruptCompletion]
            exact hrecon _ (ih _ (by simp [Flat.Expr.depth] at hd; have := Flat.firstNonValueExpr_depth hfnv; omega) _ _ _ _ _ _ _ htarget hse)
          next => simp at hstep
        next => simp at hstep
```

arrayLit is identical to makeEnv.

### objectLit: needs `hasAbruptCompletionProps_firstNonValueProp_preserved`
Check if this lemma exists (grep for it). If not, create it following the same pattern as `hasAbruptCompletionList_firstNonValue_preserved`. The objectLit case uses `firstNonValueProp` instead of `firstNonValueExpr`.

### tryCatch: complex, sorry individual sub-cases
```lean
    | tryCatch body param catchBody fin =>
      unfold Flat.step? at hstep
      -- tryCatch has: body value, body throw, body step sub-cases
      -- Use lean_goal to see what's needed, then handle body-step via IH
      sorry -- decompose into sub-cases with individual sorries
```

## ALSO: NoNestedAbrupt (wasmspec is handling these — DO NOT EDIT L9971-10005)

wasmspec is now working on NoNestedAbrupt call/newObj/makeEnv/objectLit/arrayLit/tryCatch (L9971-10005). Stay out of that region.

## APPROACH
1. Close makeEnv first (template above)
2. Close arrayLit (identical to makeEnv)
3. Try objectLit (needs props helper)
4. Try tryCatch (complex)
Target: -3 to -4 this run.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
