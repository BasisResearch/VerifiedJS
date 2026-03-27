# jsspec — Help proof agent with CC CCState lemma

## BUILD STATUS: Core/Semantics PASSES ✓. All stepping lemmas DONE ✓.

## NEW TASK: Create CCState independence lemma for proof agent

The proof agent is blocked on 6 identical CC sorries that all need to show:
when `convertExpr` is called on the same expression with two different CCStates,
the result Flat expressions are equivalent (α-equivalent / identical up to fresh names).

### What to do:
1. Read `VerifiedJS/Proofs/ClosureConvertCorrect.lean` around L530-640
2. Find `convertExpr_state_determined` — it exists but the `functionDef` case (L642) is sorry
3. Close the L642 sorry in `convertExpr_state_determined` for `functionDef`
   - The case uses `freshVar` (consumes nextId) and `addFunc` (uses funcs.size)
   - Two CCStates with same `nextId` and `funcs.size` produce the same output
   - Use `lean_goal` at L642 to see what's needed
   - Try structural induction or `simp [CCState.freshVar, CCState.addFunc]`

4. If `convertExpr_state_determined` is complete, verify it has the signature the proof agent needs:
   ```
   theorem convertExpr_state_determined (e : Core.Expr) (scope envVar envMap) (st1 st2 : CCState)
       (hid : st1.nextId = st2.nextId) (hsz : st1.funcs.size = st2.funcs.size) :
       (Flat.convertExpr e scope envVar envMap st1).fst = (Flat.convertExpr e scope envVar envMap st2).fst
   ```
   This would let the proof agent use it to close all 6 CCState sorries.

5. Also check: does a `convertExpr_state_output` lemma exist that shows the *output state*
   is also determined? That might be needed too.

### ALTERNATIVE: If L642 is too hard
Write a standalone helper lemma in ClosureConvertCorrect.lean:
```lean
theorem cc_conversion_preserved (e : Core.Expr) (scope envVar envMap st st')
    (hconv : Flat.convertExpr e scope envVar envMap st = (fe, st'))
    (hconv2 : Flat.convertExpr e scope envVar envMap st2 = (fe2, st2')) :
    fe = fe2 -- if st.nextId = st2.nextId ∧ st.funcs.size = st2.funcs.size
```

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log progress to agents/jsspec/log.md.
