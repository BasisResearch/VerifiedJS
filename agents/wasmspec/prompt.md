# wasmspec — Prove compound if infrastructure lemmas in ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent is INSERTING new definitions around L7100 (HasTryCatchInHead) and working on L9536
- **YOU** own L9273-9322 (infrastructure lemmas) and L9326+ (normalizeExpr_if_step_sim usage)
- DO NOT touch lines 7046-7500 or 9508-9540
- **NOTE**: proof agent's insertions will SHIFT your line numbers. Use `grep -n "normalizeExpr_if_compound_true_sim"` to find current lines.

## STATUS: CRASHED at 06:31 (EXIT code 1). Restarting.

You previously consolidated 4 inline sorries → 2 infrastructure lemmas (net -2). L9298 and L9322 still sorry.

## YOUR TASK: Prove these 2 infrastructure lemmas

`normalizeExpr_if_compound_true_sim` and `normalizeExpr_if_compound_false_sim`.

### Proof strategy: case analysis on sf_expr

1. **Find your lemmas**: `grep -n "normalizeExpr_if_compound_true_sim" VerifiedJS/Proofs/ANFConvertCorrect.lean`

2. **Use `lean_goal` at the sorry line** to see exact proof state.

3. **Key insight**: Only `.if` in sf_expr can produce `.if` through normalizeExpr.
   Use `ANF.normalizeExpr_if_implies_hasIfInHead` (already exists!) to get `HasIfInHead sf_expr`.

4. **Case split on HasIfInHead**:
```lean
  have hif := ANF.normalizeExpr_if_implies_hasIfInHead sf_expr k hk cond then_ else_ n m hnorm
  cases hif with
  | if_direct =>
    -- sf_expr = .if c_flat then_flat else_flat
    -- This is the main case: prove simulation directly
    sorry
  | _ =>
    -- Compound cases (seq, let, etc.)
    -- These are harder — sorry for now
    sorry
```

5. **For if_direct case**: sf_expr = `.if c_flat then_flat else_flat`.
   - normalizeExpr (.if c t e) k normalizes c to a trivial condTriv
   - The `cond` in the ANF .if IS condTriv
   - For the true branch: Flat.step? (.if c_flat ...) evaluates c_flat
   - If c_flat is value (lit): single step, trivial
   - If c_flat is var: two steps (lookup + branch)
   - If c_flat is this: two steps (lookup + branch)
   - Model on the existing normalizeExpr_if_step_sim proof (L9343+) which handles exactly this

6. **Even if you can only prove if_direct**: That's still progress — narrows the sorry to compound cases only.

### IMPORTANT: Use existing decomp lemmas
- `normalizeExpr_if_lit_decomp`, `normalizeExpr_if_var_decomp`, `normalizeExpr_if_this_decomp` — these extract cond/then_/else_ info from the normalizeExpr result
- `Flat_step?_if_cond_step` — Flat step for if-condition
- `Flat.step?_if_true`, `Flat.step?_if_false` — Flat step for branch selection

## PRIORITY ORDER
1. L9298 (true branch infrastructure) — prove if_direct case, sorry compounds
2. L9322 (false branch) — structurally identical

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
