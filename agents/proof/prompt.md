# proof — Close if_step_sim (L6864/6867/6883), then tryCatch_step_sim (L6910)

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 24 sorry occurrences. UNCHANGED since last run.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` (L6785) entirely.

## ⚠️⚠️⚠️ CRITICAL CORRECTION: normalizeExpr_if_source IS WRONG ⚠️⚠️⚠️
Your LAST RUN discovered that the characterization approach (`normalizeExpr_if_source`: "e must be .if") is INCORRECT:
- `.seq a b` CAN produce `.if` when `b` contains `.if`
- `.let name (.if ...) body` CAN produce `.if` (bubbles up through CPS)
- Most constructors with a 'head' sub-expression can propagate `.if`

DO NOT build `normalizeExpr_if_source`. It is FALSE for general `e`.

## YOUR IMMEDIATE TASK: Close if_step_sim via strong induction

### Correct approach (from your own analysis):
**Strong induction on `sf.expr.depth`** with case analysis:

1. **`.if fc ft fe` (fc is trivial chain)**: Direct — use `steps_if_var_branch`/`steps_if_lit_branch`
2. **`.seq a b`**: Peel off seq prefix with `trivialChain_consume_ctx`, recurse on `b` (depth decreases)
3. **`.var`, `.lit`, `.this`**: Contradiction — `k` produces `.trivial`, not `.if`
4. **`.break`, `.continue`, `.return none`, `.yield none`, `.labeled`, `.while_`, `.tryCatch`**: Contradiction — these don't produce `.if`
5. **Other (`.let`, `.assign`, etc.)**: Use `bindComplex` structure — the `.if` is inside the continuation, recurse

### Existing helpers you already found:
- `steps_if_var_branch`, `steps_if_lit_branch`, `steps_if_this_branch`
- `trivialChain_consume_ctx`
- `bindComplex_not_if` (line ~469)

### For L6864/L6867 (true/false branches):
Instead of characterizing what `e` must be, prove that Flat can simulate the if-step
by inducting on how normalizeExpr produced `.if`:
```lean
-- Strong induction: sf.expr.depth
-- Base case: sf.expr = .if fc ft fe → direct flat steps
-- Inductive case: sf.expr = .seq a b, .let x init body, etc.
--   normalizeExpr wraps with prefix steps, the .if comes from inner expr
--   Flat steps = prefix steps + .if step
```

### For L6883 (.var not bound error case):
Your last run closed all literal trivial cases. Only `.var name_cond` remains.
Need: if normalizeExpr produces `.if (.var name) ...`, then `name` is either:
- Free in `sf.expr` (so `hewf` gives it's bound → contradiction with `hnone`)
- Or a freshName (which IS bound in the wrapping .let → also contradiction)

Key insight: `normalizeExpr_var_implies_free` already exists (used at L6946). Check if a similar lemma works for the .if condition variable.

### After if_step_sim: tryCatch_step_sim (L6910)
Same strong-induction approach. Use `bindComplex_not_tryCatch` (line ~480).

## SKIP THESE:
- `let_step_sim` (L6785) — bindComplex PRODUCES .let, characterization WRONG
- `seq_step_sim` — blocked on SimRel while-loop generalization
- ClosureConvertCorrect.lean — other agents own it
- LowerCorrect.lean — DONE (0 sorries)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
