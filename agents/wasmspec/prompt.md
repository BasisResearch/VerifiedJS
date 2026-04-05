# wasmspec — 4 sorries remain. Line numbers UPDATED 21:05. Close preservation + exotic cases.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~1.6GB available. VERY TIGHT.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8754-10657
- **YOU** own L12000-12750 ONLY (trivialChain/exotic zone)
- DO NOT touch lines outside your range

## YOUR 4 SORRIES (verified 21:05 — LINE NUMBERS CORRECTED):

| Line | Category | Description |
|------|----------|-------------|
| L12014 | preservation for combined steps (true) | seq_right: needs preservation proof for appended steps |
| L12121 | exotic remaining (true) | binary, unary, getProp, etc. |
| L12630 | preservation for combined steps (false) | Same as L12014, false branch |
| L12737 | exotic remaining (false) | Same as L12121, false branch |

## APPROACH FOR L12014 / L12630 (preservation for combined steps)

Your log says you closed the trivialChain seq sorry and partially closed seq_right, with preservation remaining. Use `lean_goal` at L12014 to see the exact goal.

The pattern: you have steps from IH (hsteps_a, hsteps_b) composed together. Preservation should compose from `hpres_a` and `hpres_b` from the IH. Try:
- `exact Steps_pres_trans hpres_a hpres_b` or similar composition
- Look for how other preservation proofs compose in the file

## APPROACH FOR L12121 / L12737 (exotic remaining)

These are catch-all `| _ =>` cases. Use `lean_goal` to see what constructors remain. Try:
- `exfalso; cases hif <;> simp_all` to show all constructors are already covered
- If some remain, handle them individually

## PRIORITY ORDER
1. L12014 + L12630 (preservation) — likely mechanical once you see the goal
2. L12121 + L12737 (exotic) — likely contradictions or trivialChain

## YOU HAVE BEEN IDLE SINCE 20:15. GET MOVING.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
