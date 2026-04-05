# wasmspec — Close 4 remaining sorries: trivialChain preservation + exotic

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.5GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8573-10476, L13397-14785
- **YOU** own L11800-12600 ONLY (trivialChain/exotic zone)
- DO NOT touch lines outside your range

## YOUR 4 SORRIES (verified 20:30 — LINE NUMBERS UPDATED):

| Line | Category | Description |
|------|----------|-------------|
| L11833 | preservation for combined steps (true) | trivialChain seq: needs preservation proof for appended steps |
| L11940 | exotic remaining (true) | binary, unary, getProp, etc. |
| L12449 | preservation for combined steps (false) | Same as L11833, false branch |
| L12556 | exotic remaining (false) | Same as L11940, false branch |

## APPROACH FOR L11833 / L12449 (preservation for combined steps)

These are `sorry -- preservation for combined steps` inside the seq sub-case of normalizeExpr_if_branch_step. Look at the context around L11825-11833:
- You have `hwsteps` (steps for a), `hsteps_b` (steps for b), appended together
- Need to prove `Steps_ctx_lift_pres` or similar preservation across the combined steps
- Pattern: the `hpres_a` and `hpres_b` from the IH should compose

Use `lean_goal` at L11833 to see the exact goal. Then check if `Steps_ctx_lift_pres` applied to the seq context with both `hpres_a` and `hpres_b` closes it.

## APPROACH FOR L11940 / L12556 (exotic remaining)

These are catch-all `| _ =>` cases for HasIfInHead constructors not explicitly matched (binary, unary, getProp, etc.). For each:
- Use `lean_goal` to see what constructors remain
- Try: `exfalso; cases hif` to show all constructors are covered
- If some remain, they should be handleable by `trivialChain_eval_value` or direct stepping

## PRIORITY ORDER
1. L11833 + L12449 (preservation) — likely mechanical once you see the goal
2. L11940 + L12556 (exotic) — likely contradictions or trivialChain

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
