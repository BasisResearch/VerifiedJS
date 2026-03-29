# jsspec — FILE CREATION IS IMPOSSIBLE. PIVOT TO INLINING + SUPPORTED PREDICATE.

## STATUS: 61 sorries. ANFInversion.lean STILL not in main tree — BUT IT'S NOT YOUR FAULT.

**The directory `VerifiedJS/Proofs/` is root:pipeline 750. NO agent can create new files there.**
The proof agent has been told to INLINE the ANFInversion content into ANFConvertCorrect.lean.
You are no longer responsible for file creation. Stop trying.

## PRIORITY 0: Fix `convertExpr_not_value` for forIn/forOf (CC L1148-1149)

These 2 sorries are FALSE THEOREMS:
- `Core.exprValue? (.forIn ...) = none` — TRUE (forIn is not a value)
- `Flat.convertExpr (.forIn ...) = (.lit .undefined, st)` — this IS a value
- So `Flat.exprValue? (.lit .undefined) = some .undefined ≠ none`

The theorem `convertExpr_not_value` needs a `supported` guard. Two options:

**Option A** (preferred): Add `(h_supp : e.supported = true)` hypothesis to `convertExpr_not_value`.
Then the forIn/forOf cases become `simp [supported] at h_supp` (they're not supported).
This requires that `Core.Expr.supported` exists and returns false for forIn/forOf.

**Option B**: If `supported` doesn't exist on `Core.Expr`, create a predicate inline:
```lean
private def Core.Expr.isStub : Core.Expr → Bool
  | .forIn .. => true
  | .forOf .. => true
  | _ => false
```
Add `(h_nostub : e.isStub = false)` to `convertExpr_not_value`.

Check: does `Core.Expr.supported` or similar exist? Use `lean_local_search` for "supported".
Then: does the caller of `convertExpr_not_value` have access to a supported hypothesis?

The callers are at L2408 (if-cond none case) and L1980 area. Check if they have `h_supported`.

## PRIORITY 1: Complete remaining break/continue characterization lemmas

The 5 missing constructor cases (call, newObj, makeEnv, objectLit, arrayLit) need
normalizeExprList/normalizeProps characterization. These are already staged in
`.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`.

Since you can't create new files, write them into `ANFConvertCorrect.lean` directly
(coordinate with proof agent — they're also editing that file).

Actually — **let the proof agent handle ANFConvertCorrect.lean**. Focus on CC.

## PRIORITY 2: Explore CC objectLit/arrayLit helpers

The sorries at CC L3461, L3487, L3495, L3542, L3549, L3575, L3583 are related to
objectLit/arrayLit. You have staging work in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`.
Check if any of those helpers can be inlined into ClosureConvertCorrect.lean.

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw — for P0 and P2)
- `.lake/_tmp_fix/` (read only — source material)

## DO NOT EDIT: `VerifiedJS/Proofs/ANFConvertCorrect.lean` (proof agent owns this), `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md — LOG IMMEDIATELY when you start
