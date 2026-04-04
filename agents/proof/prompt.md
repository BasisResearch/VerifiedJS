# proof — Close call/newObj sub-stepping + makeEnv/arrayLit list cases

## RULES
- Edit: ANFConvertCorrect.lean AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build EndToEnd: `lake build VerifiedJS.Proofs.EndToEnd`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: 6 easy hasAbruptCompletion cases CLOSED ✓ — Great work!

You closed getProp, setProp, getIndex, setIndex, deleteProp, getEnv. ANF down from 41→35 sorry.

## Remaining 12 sorry targets in hasAbruptCompletion + NoNestedAbrupt

### hasAbruptCompletion_step_preserved (6 remaining):
- L9541: `| call f fenv args => sorry`
- L9542: `| newObj f fenv args => sorry`
- L9560: `| makeEnv vals => sorry`
- L9573: `| objectLit props => sorry`
- L9574: `| arrayLit elems => sorry`
- L9575: `| tryCatch body param catchBody fin => sorry`

### NoNestedAbrupt_step_preserved (6 remaining):
- L9843: `| call f fenv args => sorry`
- L9844: `| newObj f fenv args => sorry`
- L9862: `| makeEnv vals => sorry`
- L9875: `| objectLit props => sorry`
- L9876: `| arrayLit elems => sorry`
- L9877: `| tryCatch body param catchBody fin => sorry`

## TASK 1 (HIGHEST PRIORITY): call sub-stepping cases

### CRITICAL INSIGHT about call/newObj:
The "all values resolved" case (where call actually executes) is HARD because `hasAbruptCompletion (funcDef.body)` is unknown. Focus ONLY on the sub-expression stepping branches.

For `hasAbruptCompletion_step_preserved` call case, `Flat.step?` on `.call f env args` has these branches:
1. `exprValue? f = none` → step f → result `.call sf.expr env args` → PROVABLE via IH
2. `exprValue? f = some _`, `exprValue? env = none` → step env → PROVABLE via IH
3. `exprValue? f = some _`, `exprValue? env = some _`, `valuesFromExprList? args = some _` → all values → call executes → HARD (sorry this)
4. `firstNonValueExpr args = some (done, target, remaining)` → step target in list → PROVABLE using `hasAbruptCompletionList_firstNonValue_preserved` (already proved at L2980)

### Proof template for call (hasAbruptCompletion):
```lean
    | call f fenv args =>
      simp only [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
      obtain ⟨⟨hf, henv⟩, hargs⟩ := hac
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- f not value → step f
        split at hstep
        next ev' sf hsf => simp at hstep; obtain ⟨_, rfl⟩ := hstep
          simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]
          exact ⟨⟨ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hf hsf, henv⟩, hargs⟩
        next => simp at hstep
      next =>  -- f value, env not value → step env
        split at hstep
        next ev' se hse => simp at hstep; obtain ⟨_, rfl⟩ := hstep
          simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]
          exact ⟨⟨hf, ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ henv hse⟩, hargs⟩
        next => simp at hstep
      next =>  -- all values → call executes
        split at hstep
        · sorry -- all values: call body has unknown hasAbruptCompletion
        · -- firstNonValueExpr args
          split at hstep
          next done target remaining hfnv =>
            have ⟨htarget, hrem, hrecon⟩ := hasAbruptCompletionList_firstNonValue_preserved hfnv hargs
            split at hstep
            next t sa hsa => simp at hstep; obtain ⟨_, rfl⟩ := hstep
              simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]
              exact ⟨⟨hf, henv⟩, hrecon _ (ih _ (by simp [Flat.Expr.depth] at hd; have := Flat.firstNonValueExpr_depth hfnv; omega) _ _ _ _ _ _ _ htarget hsa)⟩
            next => simp at hstep
          next => simp at hstep
```

Use the SAME pattern for newObj (identical structure).

### For NoNestedAbrupt call case:
```lean
    | call f fenv args =>
      cases hna with | call hf henv hargs =>
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- f not value → step f
        split at hstep
        next ev' sf hsf => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
          exact NoNestedAbrupt.call (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hf hsf) henv hargs
        next => simp at hstep
      next =>  -- f value, env not value → step env
        split at hstep
        next ev' se hse => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
          exact NoNestedAbrupt.call hf (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ henv hse) hargs
        next => simp at hstep
      next =>  -- all values → call executes
        split at hstep
        · sorry -- all values: function body NoNestedAbrupt unknown
        · split at hstep
          next done target remaining hfnv =>
            have ⟨htarget, hrem, hrecon⟩ := firstNonValueExpr_noNestedAbrupt_preserved hfnv hargs
            split at hstep
            next t sa hsa => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
              exact NoNestedAbrupt.call hf henv (hrecon _ (ih _ (by simp [Flat.Expr.depth] at hd; have := Flat.firstNonValueExpr_depth hfnv; omega) _ _ _ _ _ _ htarget hsa))
            next => simp at hstep
          next => simp at hstep
```

## TASK 2: makeEnv/arrayLit list cases

These use `firstNonValueExpr` on a list. Pattern for hasAbruptCompletion makeEnv:
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

arrayLit is identical to makeEnv. objectLit uses `firstNonValueProp` instead (may need `hasAbruptCompletionProps_firstNonValueProp_preserved` — check if it exists, or create it following `hasAbruptCompletionList_firstNonValue_preserved`).

## TASK 3: tryCatch cases

tryCatch in Flat.step? is complex (body value, body throw, body step). Use `lean_goal` at L9575 and L9877 to see what's needed. Handle the body-stepping case first (PROVABLE via IH), sorry the body-value and body-throw cases.

## APPROACH: Partial progress is great
Replace each `sorry` with the proved sub-cases + smaller `sorry`s. Going from 12 sorry → 12 sorry but with each one targeting a SPECIFIC hard case (all-values execution) is excellent progress.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
