# wasmspec — COMPOUND INNER DEPTH SORRIES (6 closable)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- ANF: 42 sorries. CC: 17. Total: 59.
- **NO PROGRESS SINCE LAST RUN.** You must close at least 1 sorry this run.
- ALL trivialChain sorries confirmed blocked. DO NOT WORK ON THOSE.

## P0: L10759 — COMPOUND INNER DEPTH (do this FIRST)

This sorry is at line 10759 in ANFConvertCorrect.lean. Context: `inner_val` is compound (not `.labeled`), inside `.return (some (.return (some inner_val)))` in `normalizeExpr_labeled_branch_step`.

**You have** (from the surrounding proof context):
- `hlh : HasLabeledInHead (.return (some (.return (some inner_val)))) label`
- `hd : (.return (some (.return (some inner_val)))).depth ≤ d + 1`
- IH on depth: `ih : ∀ e, e.depth ≤ d → HasLabeledInHead e label → ... → ∃ sf' evs, Steps ...`
- `hnorm` giving normalizeExpr result
- `hewf` giving well-formedness

**Write this proof:**
```lean
-- Step 1: Extract inner HasLabeledInHead
have hlh_inner : HasLabeledInHead inner_val label := by
  cases hlh with | return_some_arg h => cases h with | return_some_arg h => exact h
-- Step 2: Depth bound
have hdepth_inner : inner_val.depth ≤ d := by
  simp [Flat.Expr.depth] at hd; omega
-- Step 3: Well-formedness
have hewf_inner : ExprWellFormed inner_val env := by
  intro x hfx; exact hewf x (VarFreeIn.return_some_arg _ _ (VarFreeIn.return_some_arg _ _ hfx))
-- Step 4: Apply IH (check lean_goal at L10759 for exact parameter order)
-- Step 5: Lift steps through two return layers using Steps_return_some_ctx_b twice
```

**CRITICAL**: Before writing the proof, run `lean_goal` at line 10759 to see the exact goal and available hypotheses. The parameter names/order above are approximate — use the ACTUAL names from the goal.

After L10759 works, adapt for L10795, L10808, L10891, L10926, L10939 (same pattern with yield variants).

## Infrastructure that EXISTS:
- `Steps_return_some_ctx_b` (search with `lean_local_search "Steps_return_some_ctx_b"`)
- `Steps_yield_some_ctx_b` (search for it)
- `HasLabeledInHead.return_some_arg`, `HasLabeledInHead.yield_some_arg`

## SKIP: trivialChain (blocked), if_branch, while, tryCatch, error prop cases (proof agent owns those)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound inner depth L10759" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
