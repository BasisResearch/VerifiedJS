# jsspec — CLOSE CC SORRIES: objectLit, arrayLit, value sub-cases

## STATUS: ANF staging done. CC is your domain. CC=18 actual sorries.

## CURRENT CC SORRY MAP (ClosureConvertCorrect.lean):
- L1132, L1133: forIn/forOf (unsupported stubs — check if exfalso via supported hyp)
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

## PRIORITY 0: objectLit (L2866), arrayLit (L2867) — EASIEST

Read 30 lines of context around L2866. These are typically:
- `closureConvert (objectLit props)` just produces `objectLit (props.map convertExpr)`
- Simulation: source steps → target steps with same structure
- If props are values: direct. If stepping: induction hypothesis on sub-expression.

Pattern: `simp [Flat.closureConvert, Flat.convertExpr]` then match the stepping relation.

Use `lean_goal` — if it timeouts, read the code directly and write the proof, then build.

## PRIORITY 1: forIn/forOf (L1132, L1133) — maybe exfalso

Check if there's a `supported` hypothesis in scope:
```lean
  | forIn => exfalso; simp [Flat.Expr.supported] at h_supported
  | forOf => exfalso; simp [Flat.Expr.supported] at h_supported
```
If no such hypothesis exists at this proof point, these are permanent sorries — SKIP.

## PRIORITY 2: setProp stepping (L2648), setIndex stepping (L2718)

These are the "sub-expression steps" cases (obj is not a value, it steps). The closure convert preserves the step. Find the nearest proved case (e.g., getProp stepping) above and adapt.

## PRIORITY 3: call (L2588), newObj (L2589)

## DO NOT edit: ANFConvertCorrect.lean, LowerCorrect.lean, Wasm/Semantics.lean
## YOU CAN edit: ClosureConvertCorrect.lean, VerifiedJS/Flat/*, VerifiedJS/Core/*
## BUILD: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log to agents/jsspec/log.md
