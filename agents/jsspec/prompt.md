# jsspec — CLOSE 5 REMAINING BREAK INVERSION CASES

## STATUS: 59 grep sorries. Break inversion 27/32 cases done. GREAT PROGRESS.

## PRIORITY 0: Close remaining 5 list-based break inversion cases

File: `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`

The 5 remaining sorry cases in `normalizeExpr_break_or_k` are: **call, newObj, makeEnv, objectLit, arrayLit**.

All use `normalizeExprList` or `normalizeProps` internally. You need TWO helper lemmas:

### Helper 1: `normalizeExprList_break_or_k`
```lean
theorem normalizeExprList_break_or_k (es : List Flat.Expr) (k : Flat.Expr → Flat.NormalizeM ANF.Expr)
    (label : String) (n : Nat) (hn : (∀ e ∈ es, e.depth ≤ n)) :
    (normalizeExprList es k).run m = .break label →
    (∃ e ∈ es, ∃ m', (normalizeExpr e (fun t => ... )).run m' = .break label) ∨
    (∃ ts m', (k ts).run m' = .break label)
```

Key insight: `normalizeExprList` processes elements left-to-right using `bindComplex`. You already proved `bindComplex_never_break_general` — bindComplex NEVER produces .break. So break must come from either:
- A recursive `normalizeExpr` call on an element (→ use IH via strong induction on depth)
- The final continuation `k` applied to the normalized list

Proof strategy: Induction on `es`.
- `[] case`: normalizeExprList [] k = k [] — break comes from k.
- `e :: rest case`: normalizeExprList unfolds to `do let t ← normalizeExpr e ...; let ts ← normalizeExprList rest ...; k (t :: ts)`. The break comes from normalizeExpr e, or normalizeExprList rest, or k. Use the general characterization IH for normalizeExpr e, and list IH for rest.

### Helper 2: `normalizeProps_break_or_k`
Same pattern for property lists. `normalizeProps` processes `(name, expr)` pairs.

### Then close the 5 cases:
For each of call, newObj, makeEnv, objectLit, arrayLit:
1. Unfold `normalizeExpr` for that constructor
2. It calls `normalizeExprList` (or `normalizeProps`) then a continuation
3. Apply `normalizeExprList_break_or_k` to get the disjunction
4. Left case: extract the element, show `HasBreakInHead` via `HasBreakInHead` constructors
5. Right case: show continuation produces break → either HasBreakInHead from another sub-expr or k produces break

**Once all 32 cases are proved, `normalizeExpr_break_implies_hasBreakInHead` is COMPLETE.** This directly enables -2 ANF sorries.

## PRIORITY 1: Stage Flat objectLit/arrayLit step helpers

The proof agent needs these for CC objectLit. Check if they exist; if not, stage in `.lake/_tmp_fix/`:

1. `Flat.step?_objectLit_prop_step`: When first prop is non-value, Flat steps inner expression
2. `convertPropList_cons`: How convertPropList relates to stepping through prop list
3. `convertPropList_firstNonValueProp_some`: Flat version preserves firstNonValueProp structure

## FILES: `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging), `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md
