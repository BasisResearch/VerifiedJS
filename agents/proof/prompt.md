# proof — ANF IS NOW YOUR #1 PRIORITY

## STATUS: 59 total sorries. CC at 18, ANF STILL at 13 — UNTOUCHED FOR 6 DAYS.

The end-to-end `compiler_correct` theorem CANNOT compose without `anfConvert_step_star`. CC is at diminishing returns. **PIVOT TO ANF NOW.**

## STEP 1: ANF break/continue (L172, L174) — EASIEST, DO FIRST

These are terminal control flow — no sub-expressions to evaluate.

```lean
-- At L172 (break):
lean_goal at L172
-- Expected: ANF.step? (.break label) and normalizeExpr (.break label) k produce same trace
-- Try: simp_all [ANF.step?, Source.step?, normalizeExpr]
-- Or: unfold ANF.step? Source.step?; simp_all

-- At L174 (continue):
-- Same pattern as break
```

Use `lean_goal` at each line, then `lean_multi_attempt` with:
```
["simp_all [ANF.step?, Source.step?, normalizeExpr]",
 "unfold ANF.step? Source.step?; simp_all",
 "simp [ANF.step?]; rfl",
 "cases h_step <;> simp_all"]
```

## STEP 2: ANF throw/return/yield/await (L155, L159, L161, L163)

These evaluate a trivial arg then produce an event. Pattern:
1. `evalTrivial` resolves the arg
2. Event is produced
3. Match to source semantics

```lean
lean_goal at L155  -- throw
lean_goal at L159  -- return
lean_goal at L161  -- yield
lean_goal at L163  -- await
```

## STEP 3: ANF var lookup (L138)

Variable resolution in ANF env should match source env.

## STEP 4: ANF seq (L149), if (L151), let (L147)

These need sub-expression stepping. Harder but follow the same pattern as CC proofs.

## STEP 5: CC remaining (ONLY after making ANF progress)

- L2138: jsspec confirmed 2nd sorry closes with `⟨rfl, rfl⟩`. Replace `sorry, sorry⟩` with `sorry, ⟨rfl, rfl⟩⟩`.
- CCStateAgree helpers staged at `.lake/_tmp_fix/VerifiedJS/Proofs/cc_agree_helpers.lean` — install them.
- L3068 (while_ CCState): chain `convertExpr_state_determined` calls.

## DO NOT TOUCH: Wasm/Semantics.lean, LowerCorrect.lean

## Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
## Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log progress to agents/proof/log.md.
