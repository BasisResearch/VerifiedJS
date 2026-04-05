# wasmspec — Prove compound if cases (L9811/9812/9907/9908) in ANF

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
- proof agent works on L10122 (tryCatch_direct) and L11425/11478
- **YOU** own L9800-9910 (if compound infrastructure)
- DO NOT touch lines outside your range

## STATUS: GOOD PROGRESS LAST RUN — proved lit/var/this subcases for both if_compound lemmas.

You proved 6 subcases (3 per lemma: lit/var/this). 4 narrower sorries remain:
- L9811: compound c_flat with HasIfInHead — eval context lifting / strong induction needed
- L9812: non-if_direct HasIfInHead — structural induction on depth needed
- L9907: same as L9811 but false branch
- L9908: same as L9812 but false branch

## YOUR TASK: Close L9811/9812 (true branch), then L9907/9908 (false branch)

### L9811 — compound c_flat in if_direct, true branch
sf.expr = `.if c_flat then_flat else_flat`, but c_flat is compound (not lit/var/this).
normalizeExpr (.if compound_c ...) k wraps c_flat in .let via normalization.

**Key insight**: If c_flat is compound, normalizeExpr normalizes c_flat FIRST into a trivial + continuation. The .if in the result comes from the continuation. So:
- Flat.step? steps the innermost sub-expression of c_flat
- This is an evaluation context reduction
- Need: "Flat steps on .if compound_c ... reduce to Flat steps on compound_c, then branch"

**Approach**:
1. `lean_goal` at L9811 to see exact state
2. Case analyze c_flat — it's NOT lit/var/this (those are proved), so it's a compound expression
3. Flat.step? on `.if compound_c t e` steps the condition: `Flat.step? (.if c t e)` where c steps
4. Use `Flat_step?_if_cond_step` (should exist) to lift inner steps
5. After c_flat fully evaluates, the if branches — use existing true/false branch lemmas

### L9812 — non-if_direct HasIfInHead
sf.expr is NOT `.if ...` but HasIfInHead sf.expr (e.g., `.seq (.if ...) b` or `.let x (.if ...) body`).
normalizeExpr propagates the .if through the outer expression's normalization.

**This is the hardest case**. Needs eval context stepping through seq/let/etc.

**Approach**: Try `lean_multi_attempt` with:
- `exact absurd hewf (HasIfInHead_not_wellformed ...)` — maybe these are unreachable?
- `simp [HasIfInHead] at *` — see if can derive contradiction
If not contradiction, this needs the general eval context lifting lemma (shared with break/continue/throw/return/await/yield compound cases).

### Strategy: Focus on L9811/9907 FIRST (compound c_flat)
These are more tractable than L9812/9908. Even proving just these two would be progress.

## PRIORITY ORDER
1. L9811 (compound c_flat, true) — try eval context approach
2. L9907 (compound c_flat, false) — structurally identical
3. L9812 (non-if_direct, true) — only if 1-2 done
4. L9908 (non-if_direct, false) — only if 1-3 done

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
