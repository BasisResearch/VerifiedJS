# jsspec — noFunctionDef BRANCH-SPLIT FOR CCStateAgree

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T22:05
- CC: 12 real sorries. Total: **44** (ANF 32 + CC 12). Down from 50 (-6).
- `exprFuncCount` + `convertExpr_state_delta` infrastructure done last run.
- `noFunctionDef` + `convertExpr_state_id_no_functionDef` done.
- You confirmed: `supported` does NOT imply `noFunctionDef`.

## PRIORITY: Try noFunctionDef branch-split on CCStateAgree sorries

### Strategy:
For each CCStateAgree sorry (L6439, L6465, L9194, L9351, L9428, L9544):
1. `lean_goal` at the sorry line to see what expression is being converted
2. Check: does that specific sub-expression contain `functionDef`?
3. If `noFunctionDef` can be established for that sub-expression → use `convertExpr_state_id_no_functionDef` → CCStateAgree becomes trivial (states are equal)
4. If it CAN contain `functionDef` → use `convertExpr_state_delta` to show the delta is exactly `exprFuncCount e`, then build CCStateAgree from that

### Specific targets:
- **L9544 (while)**: `while_ cond body` — check if cond/body in this context must be noFunctionDef
- **L9428 (generic)**: what expression? Check with lean_goal
- **L6439, L6465 (if branches)**: then_/else_ — check with lean_goal

### FALLBACK: If noFunctionDef doesn't apply, try CCExprEquiv:
1. Define `CCExprEquiv` mutual inductive on Flat.Expr
2. Prove `convertExpr_CCExprEquiv` for simple cases
3. This is multi-run infrastructure — 0 sorries this run is OK

## DO NOT ATTEMPT:
- Multi-step simulation sorries (L5991, L7088, L7296, L7307)
- L7947 (getIndex semantic mismatch — unprovable)
- Editing ClosureConvert.lean (no write permission)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — noFunctionDef branch-split" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
