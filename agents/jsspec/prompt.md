# jsspec — APPLY CCExprEquiv TO CLOSE CCStateAgree SORRIES (5 sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T01:05
- CC: 12 real sorries. Total: **42** (ANF 30 + CC 12).
- **convertExpr_CCExprEquiv_shifted is FULLY PROVED** (L1627-1901). All 4 variants.
- **convertExpr_state_delta is PROVED**. Infrastructure is DONE.
- **You've been running since 23:30. The infrastructure is ready. CLOSE SORRIES NOW.**

## P0: CLOSE CCStateAgree SORRIES (5 sorries — L6899, L6925, L9654, L9888, L10004)

### DO NOT build more infrastructure. USE what you have.

**For each sorry, the fix is the same pattern:**

1. `lean_goal` at the sorry line to see the exact goal
2. The goal asks for something like `CCStateAgree st' st_a'` or needs an expression match
3. Instead of exact equality, use `convertExpr_CCExprEquiv_shifted` to show the expressions are CCExprEquiv with offset δ
4. Use `convertExpr_state_delta` to compute δ = `exprFuncCount` of the skipped branch

### Start with L6899 (if-true branch):
```lean
-- Goal shape: ... sorry⟩ -- BLOCKED: CCStateAgree
-- Fix: replace CCStateAgree requirement with CCExprEquiv δ
-- δ = exprFuncCount else_branch
```

1. Read lines around L6899 to understand the exact proof structure
2. The `sorry` is embedded in a tuple. Replace the equality witness with a CCExprEquiv witness
3. You may need to change a `have` or `suffices` upstream to weaken from exact equality to CCExprEquiv

### If refactoring the invariant is needed:
Find where the simulation relation requires `sf.expr = converted_expr` and weaken to `CCExprEquiv δ sf.expr converted_expr`. This is a broader change but fixes ALL 5 sorries at once.

### IMPORTANT: Test after EACH sorry fix
After fixing L6899, verify with `lean_diagnostic_messages` before moving to L6925.

**Expected: -3 to -5 sorries**

## P1: MULTI-STEP SIMULATION (L6451, L7756, L7767) — SECOND PRIORITY
3 sorries marked "multi-step simulation gap (architectural)." Different blocker. Only after P0.

## DO NOT ATTEMPT:
- L8407 (getIndex semantic mismatch — unprovable axiom issue)
- L7548, L9811, L9814 — different blockers
- Building more infrastructure — USE what exists

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — closing CCStateAgree sorries with CCExprEquiv" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
