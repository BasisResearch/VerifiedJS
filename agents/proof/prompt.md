# proof — Close UNLOCK sorries (8) in compound_true/false_sim

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
- wasmspec works on L1767-1950 (Steps_ctx_lift) AND L8000-11461 (normalizeExpr_if_branch_step)
- **YOU** own L11468-11691 (compound_true/false_sim, UNLOCK sorries) AND L12100-13600 (tryCatch, break/continue, call site)
- DO NOT touch lines outside your range

## YOUR PRIMARY TARGET: 8 UNLOCK sorries

These are in `normalizeExpr_if_compound_true_sim` (L11468) and `normalizeExpr_if_compound_false_sim` (L11583).

### UNLOCK sorries (true branch — L11566, 11574, 11576, 11578):

**L11566** — `.seq a_c b_c` case with `HasIfInHead`:
```lean
-- You have: hif_seq : HasIfInHead (Flat.Expr.seq a_c b_c)
-- You need: normalizeExpr_if_branch_step applied to (.seq a_c b_c), then lifted through if_cond_ctx
```

The proof pattern for ALL 4 true-branch UNLOCK sorries is:
```lean
-- Step 1: Get depth bound
have hdepth : sf_expr_sub.depth ≤ sf_expr_sub.depth := Nat.le_refl _
-- Step 2: Apply normalizeExpr_if_branch_step (it exists, even if it has sorries)
obtain ⟨sf', evs', hsteps', hsil', henv', hheap', hfuncs', hcs', htrace', hpres', hnorm', hewf'⟩ :=
  normalizeExpr_if_branch_step sf_expr_sub.depth sf_expr_sub hdepth hif
    env heap trace funcs cs k n m cond then_ else_ v
    hnorm hewf heval hbool
-- Step 3: If the expression is in an eval context (like if_cond), lift steps
obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
  Steps_if_cond_ctx_b then_flat else_flat hsteps' hsil_bound hpres'
-- Step 4: Wire into the goal
```

**Check with lean_goal first!** Use:
```
lean_goal at L11566 column 8
lean_goal at L11574 column 6
lean_goal at L11576 column 6
lean_goal at L11578 column 14
```

**L11574** — `.if c' t' e'` case: Same pattern, IH on (.if c' t' e')
**L11576** — `_` catch-all: Same pattern, IH on the matched expression
**L11578** — `all_goals sorry`: Non-if_direct HasIfInHead cases. normalizeExpr_if_branch_step applies DIRECTLY to sf_expr (no eval context lift needed). This should be:
```lean
exact normalizeExpr_if_branch_step sf_expr.depth sf_expr (Nat.le_refl _) hif
  env heap trace funcs cs k n m cond then_ else_ v hnorm hewf heval hbool
```

### UNLOCK sorries (false branch — L11680, 11687, 11689, 11691):
Symmetric to true branch. Replace `normalizeExpr_if_branch_step` with `normalizeExpr_if_branch_step_false`, and `trivialChain_if_true_sim` with `trivialChain_if_false_sim`.

### HOW TO APPROACH:

1. Start with L11578 (`all_goals sorry`) — this is the EASIEST. It's the non-if_direct case where normalizeExpr_if_branch_step applies directly. Try:
```
lean_multi_attempt at L11578 column 14
["exact normalizeExpr_if_branch_step _ _ (Nat.le_refl _) ‹_› _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›"]
```

2. Then L11691 (false version of same).

3. Then L11574/L11576 and L11687/L11689 — need IH + eval context lift.

4. Then L11566/L11680 — `.seq` case, needs IH + Steps_if_cond_ctx_b lift through `.seq` inside `.if`.

### USE lean_goal AND lean_multi_attempt AGGRESSIVELY
Before editing, check goals. Try multiple tactics. Don't waste time editing blind.

## SECONDARY: tryCatch/call site/break/continue (7 sorries)
These are architecturally blocked. DO NOT work on them unless UNLOCK is done.
- L12153, 12171, 12174: tryCatch
- L13257, 13268: call site
- L13488, 13541: break/continue

## PRIORITY ORDER
1. L11578 + L11691 (all_goals sorry — direct application of normalizeExpr_if_branch_step/false)
2. L11574, L11576, L11687, L11689 (eval context lift cases)
3. L11566, L11680 (seq case)
4. DO NOT attempt tryCatch/break/continue — they're blocked

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
