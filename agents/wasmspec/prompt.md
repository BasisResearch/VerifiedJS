# wasmspec — Close 6 remaining sorries in normalizeExpr_if_branch_step zone

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.6GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8557-9940 (compound HasXInHead) and L12375+ (tryCatch, break/continue)
- **YOU** own L1767-1950 (Steps_ctx_lift infrastructure) AND L10944-11532 (normalizeExpr_if_branch_step zone)
- DO NOT touch lines outside your range

## PROGRESS SNAPSHOT: lit/var/this DONE, hpres DONE, 6 sorries remain
Your bounded Steps_ctx_lift infrastructure was KEY. ANF is at 32 total.

## YOUR 6 SORRIES (verified 18:30):

| Line | Category | Description |
|------|----------|-------------|
| L11053 | trivialChain seq (true) | Combine steps from helper + if branch step |
| L11104 | seq_right (true) | eval a + seq discard + IH on b |
| L11211 | exotic catch-all (true) | binary, unary, getProp, etc. |
| L11376 | trivialChain seq (false) | Same as L11053, false branch |
| L11425 | seq_right (false) | Same as L11104, false branch |
| L11532 | exotic catch-all (false) | Same as L11211, false branch |

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

### 2. exotic catch-all (L11211, L11532) — INVESTIGATE CONTRADICTIONS

Many exotic constructors may be IMPOSSIBLE (normalizeExpr can't produce `.if` from them):
```
lean_multi_attempt at line 11211 column 4
["cases hif <;> simp_all [ANF.normalizeExpr] <;> sorry"]
```
If some cases are contradictions, close with `exfalso`. For real cases, follow the IH + Steps_*_ctx_b pattern.

### 3. seq_right (L11104, L11425)

`.seq a b` where `HasIfInHead b` (not `a`). Evaluate `a` first:
- If value: `.seq (lit v) b` → `b` in one step, then IH on b
- If not value: `a` must step (trivialChain), lift through `.seq [·] b`

## PRIORITY ORDER
1. L11053 + L11376 (trivialChain seq) — should be mechanical
2. L11211 + L11532 (exotic — investigate contradictions first)
3. L11104 + L11425 (seq_right)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
