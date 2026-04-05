# wasmspec — Build general eval context stepping lemma to unlock ~20 ANF sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~485MB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead. Wait 60s then check again.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L10127-10128 (tryCatch)
- **YOU** own L7700-9912 (normalizeExpr step sim infrastructure)
- DO NOT touch lines outside your range

## STATUS: 10 contradiction subcases proved (great!). 4 if-compound sorries remain. But MORE IMPORTANTLY: ~20 of 27 ANF sorries share the SAME blocker.

## THE SYSTEMIC BLOCKER: Eval Context Stepping Through Compound Expressions

Almost every sorry in ANF says "needs eval context lifting" or "needs strong induction on depth". The pattern is:
1. sf.expr is compound (seq, let, if, call, etc.)
2. It has some construct (throw/return/if/tryCatch) in HEAD position
3. Flat.step? steps the inner expression one step
4. Need to show ANF also steps, preserving SimRel
5. Requires lifting the inner step through the eval context wrapper

**Existing infrastructure (L1800-1863)**:
- `Steps_seq_ctx` (L1800): lifts through `.seq · b`
- `Steps_throw_ctx` (L1809): lifts through `.throw`
- `Steps_let_init_ctx` (L1818): lifts through `.let name · body`
- `Steps_if_cond_ctx` (L1828): lifts through `.if · then_ else_`
- `Steps_return_some_ctx` (L1838), `Steps_yield_some_ctx` (L1848), `Steps_await_ctx` (L1858)

## YOUR TASK: Build the general compound stepping approach

### Step 1: Prove L9813/L9911 (your 4 remaining if-compound sorries) using strong induction
These are the concrete test case for the approach. Use:
1. `lean_goal` at L9813 to see exact state
2. Strong induction on `sf_expr.depth` (pattern from `normalizeExpr_if_or_k_aux` at L7219)
3. Show: Flat.step? on compound c_flat steps the inner expression (eval context)
4. Use `Steps_if_cond_ctx` to lift inner steps through `.if [·] then_ else_`
5. IH applies because stepped expression has smaller depth

### Step 2: Extract a reusable `compound_head_step_sim` lemma
Once L9813/L9911 work, factor out the pattern into a general lemma that:
- Takes a "HasXInHead" hypothesis
- Shows the compound expression steps through its eval context
- Produces a state where SimRel still holds

### Step 3: Apply to other compound sorries
The same approach should close:
- L8973 (compound HasThrowInHead)
- L9130 (compound HasReturnInHead)
- L9307 (compound HasAwaitInHead)
- L9465 (compound HasYieldInHead)
- L8143/8176/8268/8301 (normalizeExpr_labeled inner value)
- L8187/8312/8329 (compound/bindComplex)

That's potentially **17 sorries** unlocked by one general approach!

### Step 4: Also try L9814/L9912 (non-if_direct HasIfInHead)
These are the eval context through seq/let wrappers. Same strong induction.

## PRIORITY ORDER
1. L9813 (if compound true, strong induction) — PROVE THE PATTERN
2. L9911 (if compound false) — mirror of L9813
3. L9814/L9912 (non-if_direct) — eval context through wrappers
4. Extract general lemma + apply to L8973/9130/9307/9465

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
