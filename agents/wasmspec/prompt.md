# wasmspec — Close compound throw/return/await/yield sorries using NoNestedAbrupt

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.9GB available right now.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: You closed 12 vacuous sub-cases last run. Good. But sorry LINE count didn't change.

The 12 sub-cases you closed were INSIDE existing sorry lines. We need the actual sorry LINES to go away.

## YOUR TARGETS: The "inner compound" sorries

These are wildcards inside the `_some_direct` cases:
- **L8677**: `| _ => sorry` in normalizeExpr_return_step_sim (inner_val compound)
- **L8854**: `| _ => sorry` in normalizeExpr_await_step_sim (inner_arg compound)
- **L9012**: `| _ => sorry` in normalizeExpr_yield_step_sim (inner_val compound)

You already added `hna : NoNestedAbrupt sf.expr` to these 3 theorems. Now USE it:

### Strategy for L8677 (return inner compound):
The wildcard covers compound inner_val that's not lit/var/this/break/continue/return/yield/await/throw. With `hna`, `hasAbruptCompletion inner_val = false`. The approach:

1. Use `lean_goal` at L8677 to see the exact goal
2. The inner_val is compound but NOT abrupt (by hna). So it must be: seq, let, assign, if, binary, unary, while_, call, newObj, getProp, setProp, getIndex, setIndex, deleteProp, typeof, getEnv, makeEnv, objectLit, makeClosure
3. For each of these, the return wrapper around them should step via `trivialChain_return_steps` or similar

Actually, the simpler approach: if inner_val has no abrupt completion AND isn't a value, it must step. And when it steps, the return wrapper steps with it. You need:

```lean
-- The inner expression steps (it's not a value, not abrupt)
have h_steps : ∃ t s', Flat.step? { sf with expr := inner_val } = some (t, s') := by
  sorry -- need: non-value, non-abrupt expressions always step
-- The return wrapping steps through
sorry
```

This decomposes the sorry into smaller pieces. Even 2 sub-sorries per case is progress.

### Alternative: Close L9045 (let step sim) or L9093 (while step sim)

These may be more tractable:
- L9045: `sorry -- Need characterization of what produces .let, flat simulation`
- L9093: similar

Use `lean_goal` to assess. If they're simpler than the compound cases, do those instead.

## DO NOT just analyze. WRITE CODE. Close at least 1 sorry line.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
