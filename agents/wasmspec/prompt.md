# wasmspec — 4 sorries remain. Line numbers UPDATED 21:30. Close preservation + exotic cases.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything — memory is 64MB available. USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. **64MB available — CRITICAL.**
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY WARNING — DO NOT BUILD
Memory is at 64MB available. Your lean worker is using 3.6GB. If you start a build it will OOM and crash everything. **USE LSP TOOLS ONLY** (lean_goal, lean_multi_attempt, lean_hover_info).

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8963-10865
- **YOU** own L12200-12950 ONLY (trivialChain/exotic zone)
- DO NOT touch lines outside your range

## YOUR 4 SORRIES (verified 21:30 — LINE NUMBERS CORRECTED):

| Line | Category | Description |
|------|----------|-------------|
| L12222 | preservation for combined steps (true) | seq_right: needs preservation proof for appended steps |
| L12329 | exotic remaining (true) | binary, unary, getProp, etc. |
| L12838 | preservation for combined steps (false) | Same as L12222, false branch |
| L12945 | exotic remaining (false) | Same as L12329, false branch |

## APPROACH FOR L12222 / L12838 (preservation for combined steps)

Your log says you closed the trivialChain seq sorry and partially closed seq_right, with preservation remaining. Use `lean_goal` at L12222 to see the exact goal.

The pattern: you have steps from IH (hsteps_a, hsteps_b) composed together. Preservation should compose from `hpres_a` and `hpres_b` from the IH. Try:
- `exact Steps_pres_trans hpres_a hpres_b` or similar composition
- Look for how other preservation proofs compose in the file

## APPROACH FOR L12329 / L12945 (exotic remaining)

These are catch-all `| _ =>` cases. Use `lean_goal` to see what constructors remain. Try:
- `exfalso; cases hif <;> simp_all` to show all constructors are already covered
- If some remain, handle them individually

## PRIORITY ORDER
1. L12222 + L12838 (preservation) — likely mechanical once you see the goal
2. L12329 + L12945 (exotic) — likely contradictions or trivialChain

## GOOD: You started at 21:15. Keep going. Close these 4.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
