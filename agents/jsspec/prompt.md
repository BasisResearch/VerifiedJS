# jsspec — BREAK INVERSION + STAGING HELPERS

## STATUS: 55 sorries, ZERO change in 4.5 hours. BUILD BROKEN (CC and Wasm). Your break inversion work is the KEY enabler for -2 ANF sorries.

## PRIORITY 0: normalizeExpr break source characterization (CONTINUE)

Keep working on `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`.

The lemma needed:
```
Given normalizeExpr e k = .ok (.break label, m) with k trivial-preserving,
Flat can step from {expr := e} to {expr := .break label} in zero or more steps.
```

Key cases:
1. `e = .break l` directly → zero steps
2. `e = .seq a b` where `exprValue? a ≠ none` → one step (drop value), recurse on b
3. `e = .seq a b` where a normalizes to value → multi-step a, then recurse on b

Even a partial version (just cases 1+2) is valuable. Stage it in `.lake/_tmp_fix/`.

## PRIORITY 1: objectLit/arrayLit step helpers

The proof agent will need these for CC objectLit (L3129). Check if these exist, if not stage them:
1. `Flat.step?_objectLit_prop_step`: When first prop is non-value, Flat steps inner
2. `Core.step?_objectLit_prop_step`: Same for Core
3. `convertPropList_cons`: How convertExpr relates to stepping through prop list

Stage in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`.

## PRIORITY 2: Complete leaf not-break lemmas

For the master break inversion. Complete for:
- `.getProp`, `.setProp`, `.binary`, `.unary`, `.typeof`, `.deleteProp`
- `.assign`, `.if`, `.while_`, `.call`, `.newObj`

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`

## DO NOT EDIT
- `VerifiedJS/Proofs/*.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)
- `VerifiedJS/ANF/Semantics.lean` (owned by wasmspec)

## LOG to agents/jsspec/log.md
