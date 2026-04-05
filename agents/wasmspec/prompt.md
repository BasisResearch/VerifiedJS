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

## STATUS: 10 contradiction subcases proved. 4 if-compound sorries remain at L10597/10605/10610/10611 and L10710/10717/10719/10720. ~17 other sorries share same blocker.

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

### CRITICAL INSIGHT: Don't prove each sorry individually. Build ONE general lemma.

The pattern for EVERY compound sorry is:
```
sf.expr = E[inner] where E is an eval context (seq/let/if/etc.)
inner has HasXInHead (for some X: If, Throw, Return, etc.)
Flat.step? steps inner one step → inner'
normalizeExpr inner k produces X construct
Need: Flat can step E[inner] and ANF preserves SimRel
```

### Step 1: Define compound_eval_ctx_step_sim (NEW LEMMA)
```lean
private theorem compound_eval_ctx_step_sim
    (sf : Flat.State) (s : ANF.State) (t : Core.TraceEvent) (sa : ANF.State)
    (k : ANF.Trivial → ANF.NormM ANF.Expr)
    (n m : Nat) ...
    -- When sf.expr is compound with some HasXInHead in head position,
    -- and ANF steps to sa producing event t,
    -- then Flat also produces corresponding steps preserving SimRel
```
This should work by strong induction on `sf.expr.depth`:
1. sf.expr is compound: case split on outermost constructor
2. For `.seq inner rest`: Flat steps inner via IH (smaller depth), lift through `Steps_seq_ctx`
3. For `.let name init body`: Flat steps init via IH, lift through `Steps_let_init_ctx`
4. For `.if cond then_ else_`: Flat steps cond via IH, lift through `Steps_if_cond_ctx`
5. Base case: sf.expr IS the HasXInHead construct directly → use the direct case proof

### Step 2: Apply to L10597/10605/10610/10611 (if compound true)
Replace all 4 sorries with calls to the general lemma.

### Step 3: Apply to L10710/10717/10719/10720 (if compound false)
Same application.

### Step 4: Apply to ALL other compound sorries
- L9003 (compound HasThrowInHead)
- L9154/9160 (compound HasReturnInHead)
- L9331/9337 (compound HasAwaitInHead)
- L9489/9495 (compound HasYieldInHead)
- L8173/8206/8217/8298/8331/8342/8359 (normalizeExpr_labeled inner value / compound)
- L9551/9555/9556 (return/yield compound)

That's **~20 sorries** unlockable by one general lemma!

### Step 5: If general lemma is too hard, at least prove one concrete case
If the general approach stalls, prove L10610 directly:
1. `lean_goal` at L10610
2. c_flat is compound, has HasIfInHead
3. By strong induction on depth: case split on c_flat constructor
4. For each compound constructor, use corresponding Steps_X_ctx to lift
5. Once one case works, the pattern is clear for all others

## PRIORITY ORDER
1. Build general compound_eval_ctx_step_sim lemma
2. Apply to if compound sorries (L10597-10720)
3. Apply to other compound sorries (~15 more)
4. If general lemma blocked, prove L10610 directly

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
