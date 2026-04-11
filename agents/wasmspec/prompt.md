# wasmspec — COMPOUND HasReturn/Await/Yield + CATCH-ALL

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- Total: 46 sorries (ANF 30, CC 16). Down from 54 last commit.
- Your compound error prop work was excellent.
- Remaining ANF compound sorries are YOUR territory.

## P0: COMPOUND HasReturnInHead (L13361)

Same pattern as your previous compound error prop work:

1. Run `lean_goal` at L13361
2. The compound case: inner expression of `.return (some inner)` steps. Lift through return context.
3. Key helpers to search for: `lean_local_search "Steps_return"`, `lean_local_search "normalizeExpr_return"`
4. Pattern: get IH for inner step, then use Steps context lifting (Steps_return_some_ctx or similar)

## P1: COMPOUND HasAwaitInHead + HasYieldInHead (L13534, L13707)

Same pattern as P0 but for await/yield:
- `lean_local_search "Steps_await"` and `lean_local_search "Steps_yield"`
- The inner expression steps, lift through await/yield wrapper

## P2: RETURN/YIELD .let COMPOUND (L13763, L13767, L13768)

These produce `.let` from normalizeExpr. The inner expression normalizes to a `.let`, requiring multi-step.
- Run `lean_goal` on each
- Try IH + Steps_ctx_lift pattern

## P3: COMPOUND CATCH-ALL (L12969, L15497, L17036, L17107)

These are broad catch-all `| _ => sorry`. Run `lean_goal` on each to see if they're now closable or still blocked. Some may need the same compound lifting pattern.

## P4: WHILE (L13858, L13870) and TRYCATCH (L15476, L15494)

Lower priority. Check with `lean_goal` after P0-P3.

## SKIP: trivialChain (proof agent), if_branch (K-mismatch blocked), CC (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound HasReturnInHead L13361" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
