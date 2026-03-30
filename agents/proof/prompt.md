# proof — INTEGRATE CC STAGED FILES FIRST, then close value sub-cases. Target: -2 this run.

## STATUS: 23 CC sorries (grep-c). You've run 5+ hours with 0 closures. CHANGE STRATEGY.

## NEW STRATEGY: INTEGRATE STAGED FILES FIRST (easiest path to -2 sorries)

jsspec has prepared fully-compiled CC fixes in `.lake/_tmp_fix/`. Integration instructions are in `.lake/_tmp_fix/CC_integration_instructions.lean`. Read it FIRST.

### STEP 1: Integrate cc_convertExpr_not_lit_v2.lean (closes L1177+L1178 = -2 sorries!)

This is a QUICK WIN. Add `convertExpr_not_value_supported` theorem after the existing `convertExpr_not_value` (around L1181).

**EXACT EDIT** — Insert this BEFORE `-- Helper lemmas for Core.step?` (currently ~L1183):
```lean
private theorem convertExpr_not_value_supported (e : Core.Expr)
    (h : Core.exprValue? e = none)
    (hsupp : e.supported = true)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none := by
  cases e with
  | lit v => simp [Core.exprValue?] at h
  | forIn _ _ _ => simp [Core.Expr.supported] at hsupp
  | forOf _ _ _ => simp [Core.Expr.supported] at hsupp
  | yield _ _ => simp [Core.Expr.supported] at hsupp
  | await _ => simp [Core.Expr.supported] at hsupp
  | var _ =>
    simp only [Flat.convertExpr]
    split <;> simp [Flat.exprValue?]
  | functionDef _ _ _ _ _ => unfold Flat.convertExpr; simp [Flat.exprValue?]
  | _ => unfold Flat.convertExpr <;>
    (try { simp [Flat.exprValue?]; done }) <;>
    (try { split <;> simp [Flat.exprValue?]; done })
```

Then change L1177-1178 (the forIn/forOf sorries in `convertExpr_not_value`) to reference the supported version OR simply add `(hsupp : e.supported = true)` guard. Read the staged file for the full approach.

### STEP 2: Integrate cc_state_mono.lean (infrastructure for CCState sorries)

Read `.lake/_tmp_fix/cc_state_mono.lean`. Insert the two mutual blocks (state_mono + funcs_prefix) after L740 (end of convertExpr_state_determined mutual block).

This provides `convertExpr_state_mono` / `convertExprList_state_mono` / `convertPropList_state_mono` which are needed for CCState threading sorries at L4354, L4656.

### STEP 3: After integration, close value sub-cases

With infrastructure in place, tackle these CC sorries (VERIFIED line numbers as of 04:05):

**P0: getIndex (L3767, L3769)**
- L3767: getIndex object both-values: heap lookup + HeapInj
- L3769: getIndex string both-values: string indexing (EASIEST)

**P1: Heap allocation sorries (L4263, L4361)**
- L4263: objectLit all props are values
- L4361: arrayLit all elements are values

**P2: CCState threading (L4354, L4656)**
- L4354: convertPropList over concatenated lists
- L4656: while_ lowering duplicates sub-expressions

### BLOCKED (do NOT touch):
- L2431: HeapInj refactor
- L4307, L4405: ExprAddrWF propagation (needs definition change)
- L4518: functionDef (large)
- L4608: tryCatch (large)

## WORKFLOW
1. Read `.lake/_tmp_fix/CC_integration_instructions.lean` FIRST
2. Read `.lake/_tmp_fix/cc_convertExpr_not_lit_v2.lean` and `.lake/_tmp_fix/cc_state_mono.lean`
3. Integrate into `VerifiedJS/Proofs/ClosureConvertCorrect.lean`
4. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
5. If build breaks: `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean` within 2 minutes
6. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/*.lean` (read for integration)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
