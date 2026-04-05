# wasmspec — Close exotic, trivialChain, and seq_right sorries

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
- proof agent works on L11500-11700 (UNLOCK/compound_sim) and L12100-13600 (tryCatch, break/continue, call site)
- **YOU** own L1767-1950 (Steps_ctx_lift infrastructure) AND L8000-11461 (normalizeExpr step sim)
- DO NOT touch lines outside your range

## GREAT WORK: 16 hpres sorries closed!

You built Steps_ctx_lift_pres, Steps_*_ctx_b wrappers, and closed all 16 hpres sorries. ANF dropped from 56 to 40.

## REMAINING SORRIES IN YOUR ZONE (6):

### 1. trivialChain (2 sorries) — L11082, L11305
- L11082: `if_direct` case, `¬HasIfInHead c_flat` → c_flat is trivialChain. Use `trivialChain_if_true_sim`.
- L11305: Same for false branch. Use `trivialChain_if_false_sim`.

**Pattern (L11082)**: You already proved this pattern for the `¬HasIfInHead` in the `.seq` case at L11568-11572. Follow the EXACT same approach:
```lean
have htc := no_if_head_implies_trivial_chain c_flat.depth c_flat (Nat.le_refl _)
  _ cond then_ else_ n m hnorm hif_cond
exact trivialChain_if_true_sim (trivialChainCost c_flat) c_flat
  then_flat else_flat s t env heap trace sa_trace funcs cs k n m cond then_ else_ v
  htc (Nat.le_refl _) hnorm_if hewf heval htrace hbool
```

Where `hif_cond` is the `¬HasIfInHead c_flat` hypothesis and `hnorm_if` is the original normalizeExpr hypothesis for `.if c_flat then_flat else_flat`.

Check with `lean_goal` at L11082 to get exact names. The `no_if_head_implies_trivial_chain` lemma exists and was used at L11568.

### 2. seq_right (2 sorries) — L11133, L11354
- L11133: `.seq a b` where `HasIfInHead b` (true branch)
- L11354: Same for false branch

**Strategy**: Use `Classical.em (HasIfInHead a)`:
- `HasIfInHead a`: IH on a (handled like seq_left)
- `¬HasIfInHead a`: a is trivialChain. Evaluate a to value (trivialChain_eval_value), then lift through .seq, getting `.seq (lit v_a) b`. The next step evaluates to `b`. Then IH on b.

Actually, since HasIfInHead b is given, you don't need Classical.em. Just:
1. Check if a is a value (exprValue?)
2. If value: `.seq` steps to b, then IH on b
3. If not value: a must step (via trivialChain), lift through .seq, recurse

This mirrors the `trivialChain_if_true_sim` pattern. Check the existing trivialChain_if_true_sim code structure for how it handles the non-value case in seq.

### 3. exotic cases (2 sorries) — L11240, L11461
- L11240: `| _ => sorry` catch-all in normalizeExpr_if_branch_step (true)
- L11461: Same in normalizeExpr_if_branch_step_false

These catch HasIfInHead constructors not handled by explicit match arms:
- getProp_obj, setProp_obj, setProp_val
- binary_lhs, binary_rhs, unary_arg, typeof_arg
- deleteProp_obj, assign_val
- call_func, call_env, call_args
- newObj_func, newObj_env, newObj_args

**Strategy**: Expand `| _ =>` into explicit cases. For each case, follow the SAME pattern as seq_left (L11107-11129):
1. Extract the sub-expression with HasIfInHead
2. IH on that sub-expression
3. Lift through Steps_*_ctx_b (you already have Steps_unary_ctx and Steps_binary_lhs_ctx)
4. Wire normalizeExpr continuity + ExprWellFormed

You'll need to add Steps_*_ctx_b wrappers for each new eval context. Use the same pattern as Steps_seq_ctx_b.

**PRIORITY**: Start with cases you already have infrastructure for:
- binary_lhs (Steps_binary_lhs_ctx exists → make _b version)
- unary_arg (Steps_unary_ctx exists → make _b version)
Then add more ctx wrappers for the remaining cases.

**ALTERNATIVE simpler approach**: Many of these exotic constructors might be impossible. For example, `normalizeExpr (.call f env args) k` might not be able to produce `.if`. Try `cases hif` at L11240 and for each constructor that reaches this branch, check if it's actually reachable via normalizeExpr producing .if. Some might be `exfalso` cases.

Use `lean_multi_attempt` to test:
```
lean_multi_attempt at L11240
["cases hif <;> simp_all [ANF.normalizeExpr] <;> sorry"]
```

## PRIORITY ORDER
1. trivialChain (L11082, L11305) — 2 easy wins, follow existing pattern at L11568-11572
2. seq_right (L11133, L11354) — 2 medium, needs case split on exprValue? of a
3. exotic (L11240, L11461) — investigate which are contradictions vs real cases

**Expected: 4-6 sorries closed this run.**

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
