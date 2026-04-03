# jsspec — CLOSE arrayLit all-values (L6038). DO NOT TOUCH tryCatch OR functionDef.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 actual sorries.

## ⚠️⚠️⚠️ ABSOLUTE BLOCKLIST — DO NOT TOUCH ⚠️⚠️⚠️
- ALL tryCatch sorries — BLOCKED CCStateAgree
- ALL if-then/else sorries — BLOCKED CCStateAgree
- L6507 while_ — BLOCKED CCStateAgree
- L4227 call — BLOCKED no FuncsCorr
- L5015 getIndex string — semantic mismatch
- L1507, L1508 forIn/forOf — UNPROVABLE stubs
- L3334 captured var — multi-step simulation gap
- L6172 functionDef — NOT a leaf case! Flat produces `.makeClosure funcIdx (.makeEnv capturedExprs)` requiring MULTI-STEP evaluation of captured variables. DO NOT ATTEMPT.
- L4423 newObj — wasmspec owns this

## YOUR ONE TARGET: arrayLit all-values (LINE 6038)

```lean
| none =>
  sorry -- all elements are values: heap allocation (same class as other value sub-cases)
```

Context: `Core.firstNonValueExpr elems = none` means ALL elements are values.

### THIS IS PROVED FOR objectLit — COPY THE PATTERN

The objectLit all-values case is PROVED at lines 5825-5898. Your proof should be a near-copy.

### Step-by-step template (from objectLit L5825-5898):

1. Get flat's `firstNonValueExpr` is none:
```lean
have hffnv := convertExprList_firstNonValueExpr_none elems scope envVar envMap st hcfnv
```
NOTE: `convertExprList_firstNonValueExpr_none` may not exist yet. Check with `grep -n`. If it doesn't exist, you need to prove it (analogous to `convertPropList_firstNonValueProp_none` at ~L3109).

2. Get values list:
```lean
have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values _ hffnv
```
This helper EXISTS at line 75.

3. Set up sf eta and rewrite flat step:
```lean
have hsf_eta : sf = { sf with expr := .arrayLit (Flat.convertExprList elems scope envVar envMap st).fst } := by
  cases sf; simp_all
rw [hsf_eta] at hstep
rw [Flat.step?_arrayLit_allValues _ _ _ hvs] at hstep  -- EXISTS in Flat/Semantics.lean
```

4. Build Core step using `Core.step?_arrayLit_val` (EXISTS in Core/Semantics.lean)

5. HeapInj: use `HeapInj_alloc_both` (same as objectLit).
   NOTE: You may need `convertExprList_filterMap_eq` (analogous to `convertPropList_filterMap_eq` at L3178). If it doesn't exist, prove it — same induction pattern.

6. State none: `convertExprList_state_none` EXISTS at L3138.

7. Fill remaining goals (trace, EnvCorr, EnvAddrWF, HeapValuesWF, etc.) following objectLit pattern lines 5887-5898.

### CRITICAL: Check what helpers exist first
```bash
grep -n "convertExprList_firstNonValueExpr_none\|convertExprList_filterMap\|convertExprList_state_none\|firstNonValueExpr_none_implies_values\|step?_arrayLit_allValues\|step?_arrayLit_val\|HeapInj_alloc_both" VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
Build any missing helpers by copying the PropList versions.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. Check which helpers exist (grep above)
3. Build any missing helpers first
4. Write the proof following objectLit template
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
