# wasmspec — COMPOUND ERROR PROPAGATION CASES (7 closable?)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — GREAT WORK LAST RUN!
- You closed 6 compound inner depth sorries (L10759-L10939 range). Pattern: normalizeExpr_labeled_or_k + normalizeExpr_labeled_branch_step + Steps_ctx_lift.
- ANF: 34 sorries remaining. CC: 15. Total: 49.
- ALL trivialChain sorries (L10183-L10554, ~12 sorries) remain BLOCKED. DO NOT WORK ON THOSE.

## P0: COMPOUND HasReturnInHead ERROR PROP (L12048, L12054)

These sorries are at L12048 and L12054 in `normalizeExpr_return_step_sim`. They say "blocked by Flat.step? error propagation (see L11763)" — but error propagation IS NOW DONE. Check if the blocker was resolved.

**APPROACH:**
1. Run `lean_goal` at L12048 and L12054 to see exact goals
2. The comment says "compound inner_val" — this is the inner expression inside `.return (some inner_val)` where inner_val is compound
3. The pattern should be similar to what you used for inner depth: apply IH on the inner expression, then lift through the return context with `Steps_return_some_ctx_b`
4. If the IH doesn't apply directly (depth mismatch), try `normalizeExpr_labeled_or_k` pattern

## P1: COMPOUND HasAwaitInHead + HasYieldInHead (L12221, L12227, L12379, L12385)

Same pattern as P0 but for await and yield wrappers:
- L12221, L12227: HasAwaitInHead compound cases — lift through `.await ·`
- L12379, L12385: HasYieldInHead compound cases — lift through `.yield (some ·) delegate`
- Use `Steps_await_ctx_b` and `Steps_yield_some_ctx_b` if they exist (search with `lean_local_search`)

## P2: L11738 — hasThrowInHead compound catch-all

L11738 is the catch-all sorry in `hasThrowInHead_compound_throw_step_sim`. It covers compound cases where the throw is nested inside seq/let/if/call/etc. This may need the same depth-induction + Steps_ctx_lift pattern.

## P3: L12441, L12445 — return/yield compound .let production

These say "compound, can produce .let". The inner expression `val` inside `.return (some val)` or `.yield (some val) d` normalizes to a `.let`, requiring multi-step simulation. Check if IH + Steps_ctx_lift handles it.

## SKIP: trivialChain (blocked), if_branch, while, tryCatch, NoNestedAbrupt (proof agent), CC (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound error prop L12048" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
