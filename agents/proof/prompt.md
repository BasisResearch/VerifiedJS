# proof — PIVOT: CCState threading is BLOCKED. Close MECHANICAL sorries instead.

## STATUS: 62 sorries (17 ANF + 27 CC + 18 Wasm). CC down 1 from last run. P3 DONE — good work.

Your analysis of CCState threading (P0/P1) is CORRECT — it's a theorem statement issue, not a witness problem. STOP working on it. Same for forIn/forOf (P2) — needs `supported` invariant. These are DEFERRED.

## NEW PRIORITIES — ALL CLOSEABLE RIGHT NOW

### P0: L2072 — captured variable case (CC)

This sorry is for `lookupEnv envMap name = some idx`. The converted expression is `.getEnv (.var envVar) idx`. You need to:
1. `lean_goal` at L2072 to see the exact state
2. The non-captured case (L2073-2108) is ALREADY PROVED and is your template
3. For captured vars: `step?` on `.getEnv (.var envVar) idx` looks up `envVar` in `sf.env`, gets the closure environment array, then indexes at `idx`
4. You need `HeapInj` to map from the Core env lookup to the Flat closure env lookup
5. Construct `sc'` analogous to the non-captured case at L2088

### P1: L2929 — getProp on object (CC)

The string case is proved (L2930-2975). For object case:
1. `lean_goal` at L2929
2. `Flat.step?` on `.getProp (.lit (.object addr)) prop` does a heap lookup
3. Use `HeapInj` to map Core heap addr to Flat heap addr
4. Template: follow the string case pattern but with heap lookup instead of length

### P2: L3655 — functionDef (CC)

```lean
| functionDef fname params body isAsync isGen => sorry
```
1. `lean_goal` at L3655
2. `Flat.convertExpr (.functionDef ...)` creates a closure, allocates it on the heap
3. This is likely the most complex of these targets. If >1 hour, move to P3.

### P3: L1878 + L1988 — "proved in staging" sorries

These need `convertExpr_not_lit` for stub constructors (forIn, forOf, classDecl). Write this lemma:
```lean
theorem convertExpr_not_lit_stub (e : Core.Expr)
    (h : e = .forIn .. ∨ e = .forOf .. ∨ e = .classDecl ..) :
    ∀ v, Flat.convertExpr e scope envVar envMap st ≠ (.lit v, _) := by
  rcases h with rfl | rfl | rfl <;> simp [Flat.convertExpr]
```
Check if this pattern works with `lean_multi_attempt`. Then use it to close L1878 and L1988.

## WORKFLOW — MANDATORY
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: SORRY IT BACK within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
