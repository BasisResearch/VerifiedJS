# wasmspec — Build general eval context stepping lemma to unlock ~17 ANF sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.6GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead. Wait 60s then check again.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L10400-10555 (tryCatch) and L11840-11910 (break/continue)
- **YOU** own L7700-10135 (normalizeExpr step sim infrastructure)
- DO NOT touch lines outside your range

## STATUS: 10 contradiction subcases proved (great!). 4 if-compound sorries remain. ~17 other sorries share same blocker.

You proved break/continue/labeled/while_/tryCatch contradiction cases in both normalizeExpr_if_compound_true_sim and normalizeExpr_if_compound_false_sim. 4 remaining sorries at L10033/10034/10131/10132 need strong induction + eval context lifting.

## THE SYSTEMIC BLOCKER: Eval Context Stepping Through Compound Expressions

~17 of 30 ANF sorries say "needs eval context lifting" or "needs strong induction on depth". The pattern is:
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

## YOUR TASK: Prove eval context stepping for L9813 then generalize

### Step 1: Prove L10033 (if compound true, strong induction on depth)
1. `lean_goal` at L10033 to see exact state
2. c_flat is compound with HasIfInHead. Flat.step? steps c_flat one step.
3. By strong induction on `c_flat.depth`:
   - c_flat must be some compound expr (seq, let, etc.) with .if in head
   - Flat.step? steps the head subexpression
   - Inner step produces c_flat' with smaller depth
   - Use `Steps_if_cond_ctx` to lift through `.if [·] then_ else_`
   - Apply IH (smaller depth)
4. Pattern: follow `normalizeExpr_if_or_k_aux` (L7219) for strong induction setup

### Step 2: Prove L10131 (mirror of L10033 for false branch)
Identical structure, just different branch.

### Step 3: Prove L10034/L10132 (non-if_direct HasIfInHead through wrappers)
These need eval context through seq/let wrappers. Same strong induction.

### Step 4: Extract general `compound_head_step_sim` lemma
Once L9813 works, factor out the approach. The same pattern applies to:
- L8973 (compound HasThrowInHead)
- L9130 (compound HasReturnInHead)
- L9307 (compound HasAwaitInHead)
- L9465 (compound HasYieldInHead)
- L8143/8176/8268/8301 (normalizeExpr_labeled inner value)
- L8187/8312/8329 (compound/bindComplex)

That's **17 sorries** unlocked by one general approach!

## PRIORITY ORDER
1. L10033 (if compound true) — PROVE THE PATTERN
2. L10131 (if compound false) — mirror
3. L10034/L10132 (non-if_direct) — wrappers
4. Extract general lemma + apply to other compound sorries

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
