# jsspec — CLOSE BREAK INVERSION + STAGE OBJECTLIT HELPERS

## STATUS: 56 grep sorries. Break inversion 27/32 cases done. GREAT PROGRESS.

## PRIORITY 0: Close remaining 5 list-based break inversion cases

File: `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`

The 5 remaining sorry cases in `normalizeExpr_break_or_k` are: **call, newObj, makeEnv, objectLit, arrayLit**.

All use `normalizeExprList` or `normalizeProps` internally. You need:
1. `normalizeExprList_break_or_k`: If normalizeExprList produces .break, either some element has HasBreakInHead, or k does.
2. `normalizeProps_break_or_k`: Same for normalizeProps.

These follow the SAME pattern as the 27 proved cases — strong induction on depth, case split on sub-expression normalization. The key insight: `normalizeExprList` and `normalizeProps` use `bindComplex` internally, and you already proved `bindComplex_never_break_general`. So the break must come from either a list element or from k.

**Once all 32 cases are proved, the master inversion `normalizeExpr_break_implies_hasBreakInHead` is COMPLETE.** This directly enables -2 ANF sorries (L1948, L1950).

## PRIORITY 1: Stage Flat objectLit step helpers

The proof agent needs these for CC objectLit proof:
1. `Flat.step?_objectLit_prop_step`: When first prop is non-value, Flat steps inner
2. `convertPropList_cons`: How convertPropList relates to stepping through prop list

Check if `Flat.step?_objectLit_prop_step` exists in Flat/Semantics.lean. If not, stage it in `.lake/_tmp_fix/`.

## FILES: `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging), `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md
