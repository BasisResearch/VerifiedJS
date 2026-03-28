# jsspec — NORMALIZEEXPR INVERSION LEMMAS + SUPPORTED PROPAGATION

## STATUS: proof agent needs normalizeExpr inversion lemmas to close let/seq/if sorries. YOU provide the infrastructure.

## PRIORITY 0: normalizeExpr inversion for `.let`

The proof agent needs: if `(normalizeExpr sf.expr k).run n = ok (.let name rhs body, m)`, what can `sf.expr` be?

Write in `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean` (append):

```lean
/-- If normalizeExpr produces .let, characterize possible source expressions.
    The key insight: normalizeExpr only produces .let via:
    1. bindComplex (which wraps any complex rhs in a let)
    2. Direct .let case: normalizeExpr (.let name rhs body) k
    So .let output means sf.expr was compound with a non-trivial sub-expression. -/
theorem normalizeExpr_let_output_characterization (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (name : String) (rhs : ANF.ComplexExpr) (body : ANF.Expr)
    (h : (ANF.normalizeExpr e k).run n = Except.ok (ANF.Expr.let name rhs body, m)) :
    -- Either e is a Flat.let, or e is a compound expression that bindComplex wrapped
    -- For now, just establish that e is NOT a value/trivial form
    ¬ (∃ v, e = .lit v) := by
  intro ⟨v, hv⟩; subst hv
  simp [ANF.normalizeExpr] at h
  -- k produces .trivial not .let, contradiction
  sorry -- needs: k produces .trivial (from hk_triv hypothesis)
```

Actually, this needs the `hk_triv` hypothesis. The inversion depends on k being trivial-preserving.

**Better approach**: Write case-by-case lemmas:

```lean
/-- normalizeExpr of a value/var applies k, never produces .let directly -/
theorem normalizeExpr_lit_not_let (v : Flat.Value) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ arg n', ∃ m', (k arg).run n' = Except.ok (ANF.Expr.trivial arg, m'))
    (n m : Nat) (name : String) (rhs : ANF.ComplexExpr) (body : ANF.Expr) :
    (ANF.normalizeExpr (.lit v) k).run n ≠ Except.ok (ANF.Expr.let name rhs body, m) := by
  simp [ANF.normalizeExpr, StateT.run, StateT.pure, pure, Pure.pure, Except.pure]
  intro h
  obtain ⟨m', hm'⟩ := hk (ANF.trivialOfFlatValue v) n  -- need trivialOfFlatValue
  sorry -- show k output is .trivial, not .let
```

Hmm, this is getting complex. Let me simplify.

**The REAL priority**: Write `normalizeExpr_produces_let_iff_bindComplex` which shows that `.let` in the output always comes from `bindComplex`. This is structural from the definition.

Check the `normalizeExpr` definition in `VerifiedJS/ANF/Convert.lean` to see which cases call `bindComplex` and which call `k` directly. Then enumerate.

## PRIORITY 1: normalizeExpr_supported_no_yield_await

Write a lemma showing that if the input expression is supported, normalizeExpr can't produce yield/await:

```lean
theorem normalizeExpr_supported_no_yield (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hsupp : e.supported = true)
    (hk_no_yield : ∀ arg n' m' res, (k arg).run n' = Except.ok (res, m') → ¬ res.isYield)
    (n m : Nat) (result : ANF.Expr)
    (h : (ANF.normalizeExpr e k).run n = Except.ok (result, m)) :
    ¬ result.isYield := by
  induction e generalizing k n m result with
  | yield arg delegate => simp [Core.Expr.supported] at hsupp
  | await arg => simp [Core.Expr.supported] at hsupp
  | ... => sorry -- each case: recurse or use hk_no_yield
```

This requires `ANF.Expr.isYield` to exist. Check if it does:
```
grep -n "isYield\|is_yield" VerifiedJS/ANF/Syntax.lean
```

If not, define it. Or just prove the negation directly without a predicate.

## PRIORITY 2: Continue staging lemmas from last prompt
- `propListNoCallFrameReturn_append`
- `listNoCallFrameReturn_append`
- `convertPropList_append`
(Only if Priority 0/1 complete)

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`

## DO NOT EDIT
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (owned by proof)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)
- `VerifiedJS/ANF/Semantics.lean` (owned by wasmspec)
- `VerifiedJS/ANF/Convert.lean` (owned by proof)

## LOG to agents/jsspec/log.md with exact results
