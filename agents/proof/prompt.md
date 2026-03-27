# proof — FIX BUILD FIRST, then close CC CCState sorries.

## ⚠️ BUILD IS BROKEN — FIX THIS FIRST ⚠️
Line 684 in ClosureConvertCorrect.lean has invalid `maxHeartbeats` in simp config:
```
decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_all (config := { maxHeartbeats := 200000 }) <;> omega
```
`maxHeartbeats` is NOT a field of `Lean.Meta.Simp.ConfigCtx`. Fix by removing the config:
```
decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_all <;> omega
```

## BUILD: `lake build VerifiedJS.Proofs.ClosureConvertCorrect` — must pass before any sorry work.

## CURRENT SORRY COUNT: ~71 total
- ANFConvertCorrect: 13 sorries (LEAVE ALONE — architecturally blocked)
- ClosureConvertCorrect: 23 sorries (YOUR TARGET)
- LowerCorrect: 1 sorry (blocked on lowerExpr partial)
- Wasm/Semantics: 34 sorries (wasmspec owns)

## ANF IS OFF LIMITS. DO NOT TOUCH IT.

## PRIORITY 1: CC CCState sorries — 6 with IDENTICAL pattern
These are the highest-value targets because they ALL have the same fix:
- L1932: `sorry -- conversion relation for let stepping — same CCState issue`
- L2139: `sorry -- conversion relation for if stepping — needs CCState preservation lemma`
- L2228: `sorry -- conversion relation for seq stepping — same CCState issue`
- L2467: `sorry -- conversion relation for binary lhs stepping — same CCState issue`
- L2590: `sorry -- conversion relation for getIndex stepping — same CCState issue`
- L2862: `sorry -- CCState threading: while_ lowering duplicates sub-expressions with different CCState`

### How to close these:
1. `lean_goal` at L1932 to see what the goal actually is
2. The goal involves showing that after stepping, the Flat expression in the new state
   matches the closure-converted Core expression under a (potentially different) CCState.
3. The key insight: `convertExpr` is deterministic given `scope`, `envVar`, `envMap`.
   The CCState only affects fresh variable names. Two runs of `convertExpr` on the same
   expression with different CCStates produce α-equivalent output.
4. Look for `convertExpr_state_determined` — it should exist around L530-640.
   Use `lean_local_search "state_determined"` to find it.
5. `lean_multi_attempt` at L1932 with:
   ```
   ["exact hconv'",
    "exact ⟨hfexpr', hst'⟩",
    "constructor <;> [exact (convertExpr_state_determined ..).1 ▸ hfexpr'; exact (convertExpr_state_determined ..).2]",
    "simp [Flat.convertExpr] at *; exact hconv'"]
   ```
6. Once you close L1932, apply the SAME proof to the other 5 (L2139, L2228, L2467, L2590, L2862).

## PRIORITY 2: forIn/forOf at L1113, L1114 — VACUOUSLY TRUE
These stub cases (`forIn => sorry`, `forOf => sorry`) should be vacuously true because
forIn/forOf are not in the supported subset. Try:
```lean
simp [Core.Expr.supported] at *
```
Or look at how the `supported` predicate excludes them.

## PRIORITY 3: var captured case (L1741)
This is the `| some idx =>` branch of variable lookup — the variable IS captured.
The Flat expression should be `.getEnv (.var envVar) idx`. Need to show the Flat step
matches the Core step for looking up a captured variable.

## PRIORITY 4: Expression cases with jsspec lemmas (call, newObj, setProp, setIndex, objectLit, arrayLit, functionDef)
- L2468 (call): use `step?_call_function_val`
- L2469 (newObj): similar pattern
- L2528 (setProp): use `step?_setProp_object_val`
- L2591 (setIndex): use `step?_setIndex_object_val`
- L2739 (objectLit): use `step?_objectLit_val`
- L2740 (arrayLit): use `step?_arrayLit_val`
- L2741 (functionDef): use `step_functionDef_exact`

## PRIORITY 5: value sub-cases (L2475, L2534, L2597) — skip if stuck

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Use lean_goal + lean_multi_attempt BEFORE every edit.
## Log progress to agents/proof/log.md.
