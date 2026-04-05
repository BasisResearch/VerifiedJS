# proof — Close compound HasXInHead sorries (7 targets) + tryCatch

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L11053-11532 (trivialChain/exotic sorries)
- **YOU** own L8557-9940 (labeled/compound HasXInHead) AND L12375-13763 (tryCatch/call/break)
- DO NOT touch lines outside your range

## CONGRATULATIONS: ALL 8 UNLOCK SORRIES CLOSED!
Your work on Steps_ctx_lift_pres enabled wasmspec to close hpres, and you closed all 8 UNLOCK compound_true/false_sim sorries. ANF dropped from 40 to 32. Excellent.

## YOUR NEW PRIMARY TARGET: 7 compound HasXInHead sorries

These follow a UNIFORM PATTERN. Each sorry is at a `| _ =>` catch-all in a compound case where the expression has HasXInHead but the inner sub-expression isn't one of the simple cases (lit, var, this, break, continue):

| Line | Theorem | X |
|------|---------|---|
| L9387 | normalizeExpr_throw_step_sim | HasThrowInHead |
| L9538 | normalizeExpr_return_step_sim | compound inner_val |
| L9544 | normalizeExpr_return_step_sim | HasReturnInHead |
| L9715 | normalizeExpr_return_step_sim | compound inner_arg |
| L9721 | normalizeExpr_await_step_sim | HasAwaitInHead |
| L9873 | normalizeExpr_yield_step_sim | compound inner_val |
| L9879 | normalizeExpr_yield_step_sim | HasYieldInHead |

### STRATEGY: Eval context stepping

These compounds are expressions like `.seq a b`, `.let x e b`, `.call f args`, `.assign x e`, `.if c t e` where the HEAD contains throw/return/await/yield buried inside.

The pattern for each:
1. `sf_expr` has `HasXInHead sf_expr` but isn't a direct X (it's compound)
2. `sf_expr` must step — one sub-expression evaluation step
3. After stepping, the head STILL has `HasXInHead`
4. Use `normalizeExpr` on the stepped state to get the same ANF output
5. Bridge to SimRel

**Key insight**: These are EXACTLY the same kind of eval-context-based stepping that normalizeExpr_if_branch_step handles. Look at how normalizeExpr_if_branch_step decomposes compound HasIfInHead cases — the same infrastructure (Steps_*_ctx lifting, trivialChain evaluation) applies here.

**Start with L9387** (HasThrowInHead, simplest):
```
lean_goal at L9387 column 4
```
Then try:
```
lean_multi_attempt at L9387 column 4
["cases sf_expr <;> simp_all [ANF.normalizeExpr] <;> sorry"]
```
This will show which sub-cases of `sf_expr` actually have HasThrowInHead. Many should be impossible (exfalso). For the real cases (`.seq`, `.let`, etc.), follow the eval context pattern.

## SECONDARY: L9935-9940 (return/yield/compound, 3 sorries)
Same family. After compound HasXInHead is done, these should follow.

## TERTIARY: tryCatch/call frame/break/continue (7 sorries at L12375-13763)
These are architecturally harder. Only attempt if HasXInHead is done.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
