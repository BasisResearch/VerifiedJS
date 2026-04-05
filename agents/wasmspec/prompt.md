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

## GREAT PROGRESS: hpres + lit/var/this DONE. ANF down to 32 sorries.
Your bounded Steps_ctx_lift infrastructure was KEY. Proof agent used it to close all 8 UNLOCK sorries. ANF went 40→32. You have 6 sorries left in your zone.

## REMAINING 6 SORRIES (verified 18:00):

| Line | Category | Description |
|------|----------|-------------|
| L11053 | trivialChain seq (true) | Combine steps from helper + if branch step |
| L11104 | seq_right (true) | eval a + seq discard + IH on b |
| L11211 | exotic catch-all (true) | binary, unary, getProp, etc. |
| L11376 | trivialChain seq (false) | Same as L11053, false branch |
| L11425 | seq_right (false) | Same as L11104, false branch |
| L11532 | exotic catch-all (false) | Same as L11211, false branch |

### 1. trivialChain seq (L11053, L11376) — HIGHEST PRIORITY

You already proved lit, var, this. The seq case for trivialChain means:
- `trivialChain (.seq a b)` where `a` is a trivialChain sub-expression
- Need to evaluate `a` (via trivialChain_eval_value or similar), discard result, then evaluate `b`
- Combine into Steps for the overall `.seq a b` expression

Use `lean_goal` at L11053 to see exact goal. Then try to combine:
1. trivialChain_eval_value on `a` to get Steps evaluating a to a value
2. One step for seq-discard (`.seq (lit v) b` → `b`)
3. trivialChain_eval_value on `b` (the condition)
4. Combine all Steps

### 2. seq_right (L11104, L11425) — MEDIUM

`.seq a b` where `HasIfInHead b` (not `a`). So `a` must evaluate first:
1. If `a` is a value: `.seq (lit v) b` → `b` in one step, then IH on b
2. If not value: `a` must step (trivialChain since ¬HasIfInHead a), lift through `.seq [·] b`

Variable ordering may be complex — use `lean_multi_attempt` to test partial tactics.

### 3. exotic catch-all (L11211, L11532) — INVESTIGATE FIRST

Many exotic constructors may be IMPOSSIBLE (normalizeExpr can't produce `.if` from them):
```
lean_multi_attempt at L11211 column 4
["cases hif <;> simp_all [ANF.normalizeExpr] <;> sorry"]
```
If some cases are contradictions, close with `exfalso`. For real cases, follow the IH + Steps_*_ctx_b pattern.

## PRIORITY ORDER
1. L11053 + L11376 (trivialChain seq)
2. L11211 + L11532 (exotic — investigate which are contradictions)
3. L11104 + L11425 (seq_right)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
