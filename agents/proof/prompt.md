# proof — FIX CC BUILD, THEN PIVOT TO ANF

## URGENT P0: CC BUILD IS BROKEN

Errors cascade from L2577 → L2563 → L1778:
```
L2577:6: Alternative `string` has not been provided
L2577:6: Alternative `function` has not been provided
L2563:4: Alternative `none` has not been provided
L1778:2: Alternative `setProp/getIndex/setIndex/...` has not been provided
```

All match arms ARE present (verified). The errors cascade from inside the `getProp | some cv =>` arm (L2564-2661). Something in the `.object addr =>` sub-case (L2614-2661) likely has a type error that prevents the whole match from elaborating.

**Likely causes:**
1. `hheapvwf addr haddr props hobj kv (List.find?_mem hfind)` at L2659 — check if `List.find?_mem` exists with the right signature
2. `coreToFlatValue_eq_convertValue` usage — check signature matches

**Quick fix if stuck**: temporarily sorry the `.object addr =>` case body (L2615-2661) and rebuild. This narrows the error.

**Run:** `lake build VerifiedJS.Proofs.ClosureConvertCorrect` to verify fix.

## P1: ANF IS YOUR #1 PRIORITY (after build fix)

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean` — 13 sorries, UNTOUCHED FOR 6 DAYS.

### Easiest cases first:

1. **break (L172), continue (L174)**: Terminal control flow, no sub-expressions.
```lean
lean_goal at L172
lean_multi_attempt at L172: ["simp_all [ANF.step?, Source.step?, normalizeExpr]",
 "unfold ANF.step? Source.step?; simp_all",
 "simp [ANF.step?]; rfl",
 "cases h_step <;> simp_all"]
```

2. **throw (L155), return (L159), yield (L161), await (L163)**: Evaluate trivial arg, produce event.

3. **var lookup (L138)**: Variable resolution.

4. **seq (L149), if (L151), let (L147)**: Sub-expression stepping.

5. **while (L153), tryCatch (L157)**: Hardest.

### Use `lean_goal` at each sorry, then `lean_multi_attempt` aggressively.

## P2: CC remaining (ONLY after ANF progress)

- L2138: jsspec confirmed 2nd sorry closes with `⟨rfl, rfl⟩`
- CCStateAgree helpers staged at `.lake/_tmp_fix/VerifiedJS/Proofs/cc_agree_helpers.lean`
- L3068 (while_ CCState): chain `convertExpr_state_determined`

## DO NOT TOUCH: Wasm/Semantics.lean, LowerCorrect.lean

## Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
## Log progress to agents/proof/log.md.
