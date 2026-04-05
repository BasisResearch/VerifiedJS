# wasmspec — Close 4 remaining sorries: trivialChain seq + seq_right

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~5GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8557-9940, L10030-10042, L12373-13761
- **YOU** own L10944-11425 ONLY (trivialChain/exotic zone)
- DO NOT touch lines outside your range

## GREAT WORK: Exotic catch-alls CLOSED! (-2 sorries)
You closed L11211 and L11532 (exotic catch-all cases for true/false). Only 4 sorries remain in your zone.

## YOUR 4 SORRIES (verified 19:00):

| Line | Category | Description |
|------|----------|-------------|
| L11053 | trivialChain seq (true) | Combine steps from helper + if branch step |
| L11104 | seq_right (true) | eval a + seq discard + IH on b |
| L11376 | trivialChain seq (false) | Same as L11053, false branch |
| L11425 | seq_right (false) | Same as L11104, false branch |

### 1. trivialChain seq (L11053, L11376) — HIGHEST PRIORITY

You already proved lit, var, this. The seq case:
- `trivialChain (.seq a b)` where `a` is a trivialChain sub-expression
- Evaluate `a` (via trivialChain_eval_value), discard result, evaluate `b`
- Combine into Steps for the overall `.seq a b`

Use `lean_goal` at L11053 to see exact goal. Then combine:
1. trivialChain_eval_value on `a` → Steps evaluating a to a value
2. One step for seq-discard (`.seq (lit v) b` → `b`)
3. trivialChain_eval_value on `b` (the condition)
4. Combine all Steps via Steps.trans

### 2. seq_right (L11104, L11425)

`.seq a b` where `HasIfInHead b` (not `a`). Evaluate `a` first:
- If value: `.seq (lit v) b` → `b` in one step, then IH on b
- If not value: `a` must step (trivialChain), lift through `.seq [·] b`

## PRIORITY ORDER
1. L11053 + L11376 (trivialChain seq) — should be mechanical
2. L11104 + L11425 (seq_right)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
