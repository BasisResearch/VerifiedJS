# jsspec — CCExprEquiv OR noFunctionDef branch-split

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T21:05
- CC: 12 real sorries. Total: ~50 (ANF ~38 + CC 12).
- ALL 12 CC sorries are architecturally blocked by CCStateAgree or multi-step.
- Path A (position-based naming): REJECTED.
- `noFunctionDef` + `convertExpr_state_id_no_functionDef` theorem: done.
- ClosureConvert.lean is owned by `proof` with 640 permissions — YOU CANNOT WRITE TO IT.

## PRIORITY: noFunctionDef BRANCH-SPLIT (faster path to -1 to -4 sorries)

### Why this before CCExprEquiv:
CCExprEquiv is a multi-run effort with uncertain payoff. But some CCStateAgree sorries might be closable NOW if the specific expressions at those sorry sites are `noFunctionDef`.

### Strategy:
1. For each CCStateAgree sorry (L6439, L6465, L9194, L9351, L9428, L9544):
   - Read the proof context with `lean_goal` at that line
   - Check what expression is being converted
   - If the expression is in a branch of `if`, `while`, `tryCatch` — check if that sub-expression could contain `functionDef`
   - If `noFunctionDef` holds for that sub-expression, apply `convertExpr_state_id_no_functionDef` to get state equality

2. Specifically check:
   - L9544 (while): `while_ cond body` — does `cond` or `body` contain functionDef?
   - L9428 (generic CCStateAgree): what expression?
   - L6439, L6465 (if branch): does `then_`/`else_` contain functionDef?

3. If `supported` implies `noFunctionDef` for some sub-expressions, prove it and close the sorry.

### FALLBACK: If all sorry sites CAN contain functionDef, continue CCExprEquiv:
1. Define `CCExprEquiv` mutual inductive on Flat.Expr
2. Prove `convertExpr_CCExprEquiv` for simple cases
3. This is infrastructure — 0 sorries this run is OK

## DO NOT ATTEMPT:
- Multi-step simulation sorries (L5991, L7088, L7296, L7307)
- L7947 (getIndex semantic mismatch — unprovable)
- Editing ClosureConvert.lean (no write permission)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — noFunctionDef branch-split for CCStateAgree" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
