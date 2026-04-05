# wasmspec — Prove compound if cases (L9813/9814/9911/9912) in ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~600MB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead. Wait 60s then check again.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L10127 (tryCatch_direct) and L10131+
- **YOU** own L9800-9912 (if compound infrastructure)
- DO NOT touch lines outside your range

## STATUS: GOOD PROGRESS — lit/var/this subcases proved, 5 contradiction cases proved. 4 sorries remain.

Remaining sorries:
- L9813: compound c_flat with HasIfInHead — eval context lifting / strong induction
- L9814: non-if_direct HasIfInHead — structural induction on depth
- L9911: same as L9813 but false branch
- L9912: same as L9814 but false branch

## YOUR TASK: Close L9813/9911 first, then L9814/9912

### L9813/L9911 — compound c_flat in if_direct
sf.expr = `.if c_flat then_flat else_flat`, c_flat is compound (not lit/var/this, not break/continue/labeled/while_/tryCatch — those are contradictions you already proved).

**Key infrastructure you found**:
- `Steps_if_cond_ctx` (L1828): lifts multi-step evaluation through `.if [·] then_ else_` context
- `normalizeExpr_if_or_k_aux` (L7219): pattern for strong induction on expression depth

**Approach**:
1. `lean_goal` at L9813 to see exact state
2. The compound c_flat must be one of: seq, let, assign, if, call, unary, binary, var, this, etc.
3. Flat.step? on `.if compound_c t e` steps compound_c (evaluation context)
4. After the step, the result is still `.if c' t e` with simpler c'
5. Use `Steps_if_cond_ctx` to lift the inner stepping
6. Apply strong induction on depth — the stepped c' has smaller depth

### L9814/L9912 — non-if_direct HasIfInHead
These need eval context stepping through seq/let/etc. where the `.if` is nested inside.

**Check first**: Can these be proved by contradiction? If HasIfInHead requires `.if` in head position of a normalized expression, maybe some wrappers (seq/let) can't have `.if` in head?
Try: `lean_multi_attempt` with `exact absurd hewf sorry` or `simp [HasIfInHead] at *`

## PRIORITY ORDER
1. L9813 (compound c_flat, true) — strong induction approach
2. L9911 (compound c_flat, false) — structurally identical
3. L9814 (non-if_direct, true) — eval context through wrappers
4. L9912 (non-if_direct, false) — structurally identical

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
