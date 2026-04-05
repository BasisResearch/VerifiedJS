# wasmspec — Build general eval context stepping lemma to unlock ~17 ANF sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~1.5GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead. Wait 60s then check again.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11023-11165 (tryCatch) and L12240-12522 (break/continue/return)
- **YOU** own L7700-10720 (normalizeExpr step sim infrastructure)
- DO NOT touch lines outside your range

## STATUS: 10 contradiction subcases proved. 8 if-compound sorries at L10599/10607/10609/10610 and L10711/10718/10720/10721. ~17 other sorries share same blocker.

## THE SYSTEMIC BLOCKER: Eval Context Stepping Through Compound Expressions

~20 of 34 ANF sorries say "needs eval context lifting" or "needs strong induction on depth". The pattern is:
1. sf.expr is compound (seq, let, if, call, etc.)
2. It has some construct (throw/return/if/tryCatch) in HEAD position
3. Flat.step? steps the inner expression one step
4. Need to show ANF also steps, preserving SimRel
5. Requires lifting the inner step through the eval context wrapper

**Existing infrastructure (L1820-1894)**:
- `Steps_seq_ctx` (L1820): lifts through `.seq · b`
- `Steps_throw_ctx` (L1829): lifts through `.throw`
- `Steps_let_init_ctx` (L1838): lifts through `.let name · body`
- `Steps_if_cond_ctx` (L1848): lifts through `.if · then_ else_`
- `Steps_return_some_ctx` (L1858), `Steps_yield_some_ctx` (L1868), `Steps_await_ctx` (L1878)
- `Steps_tryCatch_body_ctx` (L1887): lifts through `.tryCatch [·] cp cb fin`

## YOUR TASK: Build the general compound_head_step_sim lemma

### CRITICAL: Don't prove each sorry individually. Build ONE general lemma.

**THIS IS THE #1 HIGHEST LEVERAGE WORK IN THE ENTIRE PROJECT.** If you land this lemma, ~20 sorries become closeable.

### Suggested approach — start SMALL, then generalize:

**Step 1**: Pick ONE concrete sorry (L10609) and prove it directly:
```
lean_goal at L10609 column 7
```
Then understand what the proof needs:
- c_flat is compound, has HasIfInHead
- By strong induction on depth: case split on c_flat constructor
- For `.seq inner rest`: inner has HasIfInHead, Flat steps inner → use `Steps_seq_ctx`
- For `.let name init body`: init has HasIfInHead → `Steps_let_init_ctx`
- Etc.

**Step 2**: Once L10609 works, extract the pattern into a general lemma.

**Step 3**: Apply to ALL compound sorries:
- L10599/10607/10609/10610 (if compound true)
- L10711/10718/10720/10721 (if compound false)
- L9003 (compound HasThrowInHead)
- L9154/9160 (compound HasReturnInHead)
- L9331/9337 (compound HasAwaitInHead)
- L9489/9495 (compound HasYieldInHead)
- L8173/8206/8217/8298/8331/8342/8359 (normalizeExpr_labeled inner value / compound)
- L9551/9555/9556 (return/yield compound)

### USE lean_multi_attempt AGGRESSIVELY
Before editing the file, test tactics via `lean_multi_attempt` at each sorry location. Try:
```
["simp", "exact absurd _ _", "cases htc_head with | seq_cond => sorry | let_init => sorry | if_cond => sorry"]
```
This lets you explore without rebuilding.

## PRIORITY ORDER
1. Prove L10609 directly (concrete case to build understanding)
2. Extract general lemma
3. Apply to if compound sorries (L10599-10721)
4. Apply to other compound sorries (~15 more)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
