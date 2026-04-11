# wasmspec — COMPOUND ERROR PROP: HasReturnInHead/Await/Yield (3-6 sorries)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 6 COMPOUND INNER DEPTH CLOSED LAST RUN!
- You closed 6 compound inner depth sorries. Pattern: normalizeExpr_labeled_or_k + normalizeExpr_labeled_branch_step + Steps_ctx_lift.
- ANF: 31 sorries remaining. CC: 17. Total: 48.
- ALL trivialChain sorries (L10183-L10554, ~12 sorries) remain BLOCKED. DO NOT WORK ON THOSE.

## P0: COMPOUND HasReturnInHead (L13285)

This sorry says "compound HasReturnInHead: needs error propagation through compound wrappers". Error propagation IS done now. The pattern is the same as what you used for inner depth:

1. Run `lean_goal` at L13285
2. The compound case means the inner expression of `.return (some inner)` steps — lift through return context
3. Apply normalizeExpr_labeled_or_k on the inner expression
4. Use normalizeExpr_labeled_branch_step for the step
5. Lift with `Steps_return_some_ctx_b` (or similar)

## P1: COMPOUND HasAwaitInHead + HasYieldInHead (L13458, L13631)

Same pattern but for await/yield wrappers. Use `Steps_await_ctx_b` and `Steps_yield_some_ctx_b`. Search with `lean_local_search "Steps_await"` and `lean_local_search "Steps_yield"`.

## P2: RETURN/YIELD COMPOUND .let (L13687, L13691, L13692)

These say "compound, can produce .let" and "compound expressions: needs structural induction". The inner expression normalizes to a `.let`, requiring multi-step. Try IH + Steps_ctx_lift pattern.

## P3: COMPOUND CATCH-ALL (L12969, L15421)

These are broad catch-alls. Run `lean_goal` to see if they're closable now or still blocked.

## SKIP: trivialChain (blocked), if_branch, while, NoNestedAbrupt (proof agent), CC (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound error prop L13285" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
