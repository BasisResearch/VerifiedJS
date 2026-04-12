# jsspec — REFACTOR SIMULATION INVARIANT (CCExprEquiv offset is DONE!)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T00:05
- CC: 12 real sorries. Total: **42** (ANF 30 + CC 12).
- **convertExpr_CCExprEquiv_shifted is FULLY PROVED** (L1627-1901). Great work!
- All 4 variants proved: Expr, ExprList, PropList, OptExpr.
- **The infrastructure is READY.** Now apply it to close CCStateAgree sorries.

## P0: REFACTOR CCStateAgree SORRIES USING CCExprEquiv (HIGHEST PRIORITY — 5 sorries)

The 5 CCStateAgree sorries are at: L6899, L6925, L9654 (area), L9888, L10004.

### The Pattern
Each sorry has this shape:
```
-- Need: CCStateAgree st' st_a'
-- Have: st' = (convertExpr branch2 (convertExpr branch1 st).snd).snd
--       st_a' = (convertExpr branch1 st).snd  (only took branch1)
-- Problem: st' has extra state from branch2, so st'.nextId ≠ st_a'.nextId
```

### The Fix
Replace `sf.expr = (convertExpr e scope envVar envMap st).fst` equality in the simulation invariant with:
```lean
CCExprEquiv δ sf.expr (convertExpr e scope envVar envMap st_a).fst
```

where `δ = st.funcs.size - st_a.funcs.size` and `st_a` is the actual conversion state.

### Concrete Steps:

**Step 1: Start with ONE sorry (L6899 — if-true branch)**
1. `lean_goal` at L6899 to see exact goal
2. The goal needs `CCStateAgree st' st_a'`. Instead of proving equality, use:
   - `convertExpr_CCExprEquiv_shifted` to show the then-branch expression from `st'` is `CCExprEquiv δ` with the then-branch expression from `st_a'`
   - `convertExpr_state_delta` to compute δ = `exprFuncCount else_`
3. Change the `suffices` or `have` that introduces the witness to use CCExprEquiv instead

**Step 2: If Step 1 works, check if you can refactor the invariant**
The simulation invariant (likely in a `structure` or `suffices`) uses `sf.expr = converted_expr`. If you can weaken this to `CCExprEquiv δ sf.expr converted_expr`, the proof flows through.

**Step 3: Apply to remaining 4 CCStateAgree sorries**

### Key Theorems Available:
- `convertExpr_CCExprEquiv_shifted` (L1627): Different funcs.size → CCExprEquiv δ
- `convertExpr_state_delta` (L1232): Computes exact state delta
- `convertExpr_state_determined` (L570): Same state → same expression
- `CCExprEquiv_refl` (L1513): Reflexivity at δ=0

### Expected: -3 to -5 sorries

## P1: MULTI-STEP SIMULATION (L6451, L7756, L7767) — SECOND PRIORITY
These 3 sorries are "multi-step simulation gap (architectural)." Separate blocker from CCStateAgree. Only attempt after P0.

## DO NOT ATTEMPT:
- L8407 (getIndex semantic mismatch — unprovable)
- L7548, L9811, L9814 — different blockers

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgree invariant refactor using CCExprEquiv" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
