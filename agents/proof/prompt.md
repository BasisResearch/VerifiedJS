# proof — CC sorry count STUCK at 25. We need CLOSES this run.

## STATUS: 60 sorries (17 ANF + 25 CC + 18 Wasm). CC UNCHANGED from last run. We need -2 minimum.

## CURRENT CC SORRY MAP (25 sorries) — LINE NUMBERS VERIFIED 2026-03-29T11:05

### BLOCKED (do NOT touch):
- L1148, L1149: false theorems (forIn/forOf stubs)
- L1878, L1988: need convertExpr_not_lit for stubs
- L2391, L2413(×2): CCState threading if-branches
- L3484: CCState threading objectLit
- L3776: CCState threading while_

### YOUR TARGETS (highest-ROI first):

### P0: L2929 — getProp on object (CONTINUE FROM LAST SESSION)
- String+primitive cases already proved. Object case remains.
- `Flat.step?` on `.getProp (.lit (.object addr)) prop` does heap lookup
- Use `HeapInj` to map Core heap addr → Flat heap addr
- `HeapValuesWF` gives ExprAddrWF for heap-stored values
- **jsspec staged a proof in `.lake/_tmp_fix/cc_getProp_object_proof.lean` — READ IT**

### P1: L2908 — newObj
- `lean_goal` first. Object allocation + HeapInj extension.
- Check the Core and Flat step? for newObj — both allocate on heap.

### P2: L3403, L3491 — objectLit/arrayLit "all values" cases
- When all props/elems are values, heap allocation
- Similar to newObj pattern

### P3: L3429, L3517 — objectLit/arrayLit step extraction
- Need to unfold `step?` for the non-value case
- `firstNonValueProp`/`firstNonValueExpr` gives the sub-expr to step

### P4: L3437, L3525 — ExprAddrWF propagation for objectLit/arrayLit
- Need `ExprAddrPropListWF` / `ExprAddrListWF` helpers
- ExprAddrWF (.objectLit ps) should propagate to each element

### P5: L3655 — functionDef (complex but well-defined)
### P6: L3745 — tryCatch (hardest, save for last)

## jsspec IS HANDLING: L2907, L3031, L3101, L3170, L3255 (value sub-cases)
DO NOT work on these.

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
