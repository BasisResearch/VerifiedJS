# jsspec — CC STAGING PROOFS + HELPERS FOR PROOF AGENT

## STATUS: CC file is OWNED BY PROOF USER (rw-r-----). You CANNOT edit it directly.

**Your job**: Write proofs into staging files in `.lake/_tmp_fix/VerifiedJS/Proofs/`. The proof agent will integrate them.

## CURRENT CC SORRY MAP (ClosureConvertCorrect.lean, 20 grep / ~18 actual):
- L1132, L1133: forIn/forOf (unsupported stubs)
- L1828: HeapInj staging sorry
- L2147, L2169 (×2): CCState threading
- L2588, L2589: call, newObj
- L2595, L2654, L2724: value sub-cases (heap reasoning)
- L2648: setProp stepping
- L2718: setIndex stepping
- L2866, L2867: objectLit, arrayLit
- L2868: functionDef
- L2958: tryCatch
- L2989: while_ CCState threading

## PRIORITY 0: ANF HELPER — `normalizeExpr_compound_not_await`

The proof agent needs a lemma showing compound expressions (let, if, call, getProp, etc.) cannot produce `.await` through `normalizeExpr` when `k` produces trivials. Write this in `.lake/_tmp_fix/VerifiedJS/ANF/compound_not_await.lean`:

```lean
/-- When k maps trivials to trivials, compound expressions cannot produce .await through normalizeExpr. -/
theorem normalizeExpr_compound_not_await (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk_lit : ∀ v n, (k (ANF.trivialOfValue v)).run n ≠ .ok (.await _, _))
    (hk_var : ∀ name n, (k (.var name)).run n ≠ .ok (.await _, _))
    (hk_this : ∀ n, (k (.var "this")).run n ≠ .ok (.await _, _))
    (hk_seq : ∀ a b n, (k _).run n ≠ .ok (.await _, _))  -- probably needs different form
    (n m : Nat) (arg : ANF.Trivial) :
    -- For compound expressions (not var, lit, this, seq, await, yield, return, throw, break, continue, labeled):
    e.isCompound → (ANF.normalizeExpr e k).run n ≠ .ok (.await arg, m)
```

Study `normalizeExpr_compound_not_trivial` (grep for it in ANFConvertCorrect.lean) — adapt its structure. The key: compound expressions use `bindComplex`, and `bindComplex` followed by `k` cannot produce `.await` when `k` produces trivials.

## PRIORITY 1: CC objectLit/arrayLit staging proofs

Read L2850-2870 of ClosureConvertCorrect.lean. Write complete proof terms for objectLit and arrayLit in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit.lean`. Include all imports and the exact sorry location so proof agent can copy-paste.

## PRIORITY 2: CC forIn/forOf exfalso check

Read L1130-1135 of ClosureConvertCorrect.lean. Check if there's a `supported` hypothesis in scope. If yes, write `exfalso; simp [Flat.Expr.supported] at h_supported` proofs in staging.

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
