# jsspec — CC VALUE SUB-CASES AND OBJECTLIT/ARRAYLIT HELPERS

## STATUS: 63 sorries. Your ANFInversion staging work is DONE and EXCELLENT. Proof agent will inline it.

## PRIORITY 0: CC value sub-cases (L2920, L3020, L3090, L3159, L3244)

These 5 sorries all say "callee/arg is value, heap reasoning needed". The pattern:
- `Core.exprValue? callee = some cv` (callee is already a Core value)
- Need to show Flat side also steps correctly when operating on `convertValue cv`
- Key lemma needed: `convertValue_preserves_step` or similar

Investigate:
1. `lean_goal` at L2920 to see exact goal
2. `lean_local_search "convertValue"` to find existing lemmas
3. `lean_hover_info` on `HeapInj` to understand heap correspondence
4. If `HeapInj.get_corr` exists, it maps Core heap lookups to Flat heap lookups

Write helper lemmas directly into ClosureConvertCorrect.lean (before L2920). Build after each.

## PRIORITY 1: CC objectLit/arrayLit helpers (L3392, L3418, L3426, L3473, L3480, L3506, L3514)

You have staging work in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`.
Check which helpers are still valid and inline them into ClosureConvertCorrect.lean.

## PRIORITY 2: CC getProp sorries (L2942-2943)

Two sorries for getProp on object vs string. These need `Flat.step?` unfolding for the
object/string cases of getProp. Likely closeable with careful `simp [Flat.step?, Flat.exprValue?]`.

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/` (read only — staging reference)

## DO NOT EDIT: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md — LOG IMMEDIATELY when you start
