# wasmspec — Close 4 remaining sorries: trivialChain seq + exotic

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~1.3GB available. VERY TIGHT.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8557-9940, L10030-10042, L12857-14245
- **YOU** own L11200-12100 ONLY (trivialChain/exotic zone)
- DO NOT touch lines outside your range

## GREAT WORK: Closed 2 more seq_right sorries this cycle! (-2 sorries, 30 ANF remain)

## YOUR 4 SORRIES (verified 20:05 — LINE NUMBERS SHIFTED):

| Line | Category | Description |
|------|----------|-------------|
| L11346 | trivialChain seq (true) | eval a + seq discard + IH on b; variable ordering |
| L11453 | exotic remaining (true) | binary, unary, getProp, etc. |
| L11909 | trivialChain seq (false) | Same as L11346, false branch |
| L12016 | exotic remaining (false) | Same as L11453, false branch |

## APPROACH FOR L11346 / L11909 (trivialChain seq)

These are the seq sub-cases of trivialChain. You need to:
1. Decompose `isTrivialChain (.seq a b) = true` into `isTrivialChain a = true ∧ isTrivialChain b = true`
2. Use `trivialChain_eval_value` on the whole `.seq a b` to evaluate it to a value
3. Lift through `.if [·] then_flat else_flat` context via `Steps_if_cond_ctx_b`
4. Connect normalizeExpr of `lit v_cond` back to hnorm

**Key**: `trivialChain_eval_value` handles seq internally. You call it on the whole `a.seq b`, not on a and b separately.

After the Steps through if-cond context, simplify normalizeExpr of a literal:
```lean
simp [ANF.normalizeExpr, StateT.run, pure, Pure.pure, StateT.pure, Except.pure]
```

## APPROACH FOR L11453 / L12016 (exotic remaining)

These are catch-all cases for binary, unary, getProp, etc. expressions that appear as if-conditions. The `| _` catch-all handles all HasIfInHead constructors not explicitly matched. For each:
- They can't have HasIfInHead (because all HasIfInHead constructors are matched above)
- So `isTrivialChain` should be `true` or they're unreachable
- Try: `exfalso; simp [HasIfInHead] at hif` or `cases hif` to show all constructors are matched
- If some cases remain, use `trivialChain_eval_value` approach from above

## PRIORITY ORDER
1. L11346 + L11909 (trivialChain seq) — mechanical with sketch above
2. L11453 + L12016 (exotic remaining) — likely contradictions or trivialChain

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
