# jsspec — CC HELPER INTEGRATION + forIn/forOf CHECK

## STATUS: Staging proofs written for objectLit/arrayLit, setProp/setIndex. CC file is OWNED BY PROOF USER (rw-r-----). You CANNOT edit it directly.

## PRIORITY 0: Write `normalizeExpr_not_labeled_family` infrastructure

The proof agent is restructuring `normalizeExpr_labeled_step_sim` to use induction on depth. To close the 7 sorry cases (L1582, L1586, L1597, L1648, L1652, L1663, L1680), it needs a lemma showing compound expressions can't produce `.labeled` through normalizeExpr.

Write in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_not_labeled.lean`:

```lean
/-- bindComplex never produces .labeled -/
private theorem bindComplex_not_labeled (rhs : ANF.ComplexExpr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (label : String) (body : ANF.Expr) :
    (ANF.bindComplex rhs k).run n ≠ .ok (.labeled label body, m) := by
  -- Copy proof from bindComplex_not_trivial (L117-126), replacing .trivial with .labeled
  show ANF.bindComplex rhs k n ≠ .ok (.labeled label body, m)
  simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
             get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
             StateT.set, pure, Pure.pure, StateT.pure, Except.pure, getThe, MonadStateOf.get]
  cases hk : k (.var (toString "_anf" ++ toString (Nat.repr n))) (n + 1) with
  | error => simp [hk]
  | ok v => intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
```

Then write `normalizeExpr_not_labeled_family` following the EXACT same structure as `normalizeExpr_not_trivial_family` (L130-417), replacing `.trivial t` with `.labeled label body` and `bindComplex_not_trivial` with `bindComplex_not_labeled`.

**KEY DIFFERENCE from _not_trivial**: The `.labeled label' body_flat` case DOES produce `.labeled`:
```
normalizeExpr (.labeled label' body_flat) k = do { bodyExpr ← normalizeExpr body_flat k; pure (.labeled label' bodyExpr) }
```
So the family version CANNOT handle `.labeled` without excluding it. Add hypothesis `(h_not_labeled : ∀ l b, e ≠ .labeled l b)`.

For `.return none`, `.yield none`, `.break`, `.continue`, `.throw`, `.await`: continuations produce non-labeled constructors → noConfusion ✓
For `.return (some v)`, `.yield (some v)`: recursion with continuation `fun t => pure (.return (some t))`. This continuation doesn't produce .labeled (noConfusion). Apply IH ✓.
For compound expressions: `bindComplex_not_labeled` ✓.
For `.let`, `.if`: continuations produce `.let`/`.if` → noConfusion ✓.
For `.seq a b`: recurse on `a` then `b` → IH ✓.

Verify with `lake env lean .lake/_tmp_fix/VerifiedJS/Proofs/anf_not_labeled.lean`.

## PRIORITY 1: CC objectLit/arrayLit — polish staging proof

Your `cc_objectLit_arrayLit_proof.lean` is written. Clean it up:
- Ensure all import paths are correct
- Document which sorries remain (heap alloc, ncfr, CCState)
- Write a summary comment at the top showing exactly which lines of ClosureConvertCorrect.lean each block replaces

## PRIORITY 2: Check forIn/forOf (L1132-1133)

Read L1125-1140 of ClosureConvertCorrect.lean. Check if there's a `supported` hypothesis reachable. If `Flat.Expr.supported` excludes forIn/forOf, we can close these with `exfalso; simp [Flat.Expr.supported] at h_supported`. Write the proof in staging.

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`
- `VerifiedJS/Core/*.lean`
- `VerifiedJS/ANF/Convert.lean` (for helper lemmas only)

## DO NOT EDIT
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (owned by proof)
- `VerifiedJS/Proofs/LowerCorrect.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)

## Log to agents/jsspec/log.md
