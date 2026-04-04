# wasmspec — Close NoNestedAbrupt call/newObj/makeEnv/arrayLit/objectLit/tryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~1.1GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## REDIRECT: if-compound (L9257/9258/9330/9331) is HARD — deprioritized

Your analysis confirmed these need trivialChain infrastructure. Switch to NoNestedAbrupt cases instead.

## NEW TARGET: NoNestedAbrupt_step_preserved (6 sorries at L9971-10005)

These are symmetric to hasAbruptCompletion_step_preserved which proof agent just proved for call/newObj. Use the SAME patterns.

### Current sorry lines:
- L9971: `| call f fenv args => sorry`
- L9972: `| newObj f fenv args => sorry`
- L9990: `| makeEnv vals => sorry`
- L10003: `| objectLit props => sorry`
- L10004: `| arrayLit elems => sorry`
- L10005: `| tryCatch body param catchBody fin => sorry`

### IMPORTANT: proof agent is editing L9600-9703 (hasAbruptCompletion). You edit L9971-10005 (NoNestedAbrupt). DO NOT overlap.

### Template for call (NoNestedAbrupt):
The proof agent already wrote this template in the previous prompt. Adapt from hasAbruptCompletion call proof (now at ~L9600-9630). Key differences:
- `hna` is `NoNestedAbrupt` not `hasAbruptCompletion`
- Use `cases hna with | call hf henv hargs =>` to destructure
- Sub-stepping branches use IH on NoNestedAbrupt
- All-values branch: sorry (same as hasAbruptCompletion)

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

newObj: identical structure (just `NoNestedAbrupt.newObj` constructor).

### makeEnv/arrayLit template:
```lean
    | makeEnv vals =>
      cases hna with | makeEnv hvals =>
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- all values → done
        simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
        exact NoNestedAbrupt.lit
      next =>  -- firstNonValueExpr
        split at hstep
        next done target remaining hfnv =>
          have ⟨htarget, hrem, hrecon⟩ := firstNonValueExpr_noNestedAbrupt_preserved hfnv hvals
          split at hstep
          next t se hse => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
            exact NoNestedAbrupt.makeEnv (hrecon _ (ih _ (by simp [Flat.Expr.depth] at hd; have := Flat.firstNonValueExpr_depth hfnv; omega) _ _ _ _ _ _ htarget hse))
          next => simp at hstep
        next => simp at hstep
```

### APPROACH
1. Start with call + newObj (template above, very similar)
2. Then makeEnv + arrayLit
3. objectLit if `firstNonValueProp_noNestedAbrupt_preserved` exists
4. tryCatch last (complex)

Target: -4 to -6 sorries.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
