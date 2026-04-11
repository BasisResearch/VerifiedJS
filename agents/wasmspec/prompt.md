# wasmspec — COMPOUND INNER DEPTH SORRIES (6 closable)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- ANF: 42 sorries. CC: 17. Total: 59.
- Error propagation done in Flat/Semantics.lean.
- ALL trivialChain sorries confirmed blocked. DO NOT WORK ON THOSE.
- Trivial reconciliation infrastructure is needed but NOT YET TRACTABLE.

## P0: 6 COMPOUND INNER DEPTH SORRIES (L10759, L10795, L10808, L10891, L10926, L10939)

These are ALL the same pattern in `normalizeExpr_labeled_branch_step`. They handle compound (non-labeled) `inner_val` inside nested return/yield wrappers. The IH on depth APPLIES. Here is the exact proof approach:

### Pattern (L10759 example):
Context: `inner_val` is compound (not `.labeled`), inside `.return (some (.return (some inner_val)))`.

**What you have:**
- `hlh : HasLabeledInHead (.return (some (.return (some inner_val)))) label`
- `hd : (.return (some (.return (some inner_val)))).depth ≤ d + 1`
- `hnorm : (normalizeExpr inner_val (fun t => pure (.return (some t)))).run n = .ok (.labeled label body, m)`
  (after `simp only [ANF.normalizeExpr]` simplified through two returns)
- `hewf : ExprWellFormed (.return (some (.return (some inner_val)))) env`
- `ih : ∀ e, e.depth ≤ d → HasLabeledInHead e label → ... → ∃ sf' evs, Steps ...`

**Step 1: Extract HasLabeledInHead for inner_val**
```lean
have hlh_inner : HasLabeledInHead inner_val label := by
  cases hlh with | return_some_arg h => cases h with | return_some_arg h => exact h
```

**Step 2: Depth bound**
```lean
have hdepth_inner : inner_val.depth ≤ d := by
  simp [Flat.Expr.depth] at hd; omega
```

**Step 3: Well-formedness for inner_val**
```lean
have hewf_inner : ExprWellFormed inner_val env := by
  intro x hfx; exact hewf x (VarFreeIn.return_some_arg _ _ (VarFreeIn.return_some_arg _ _ hfx))
```

**Step 4: Apply IH**
```lean
obtain ⟨sf_inner, evs_inner, hsteps, hsilent, henv_eq, hheap_eq, ...⟩ :=
  ih d inner_val hdepth_inner label hlh_inner env heap trace funcs cs
    (fun t => pure (.return (some t))) n m body hnorm hewf_inner
```

**Step 5: Lift steps through `.return (some (.return (some ·)))` using Steps_return_some_ctx_b TWICE**
The first lift goes from `inner_val` to `.return (some inner_val)`.
The second lift wraps with `.return (some ·)` again.

```lean
have hsteps_inner_ret := Steps_return_some_ctx_b hsteps ...
have hsteps_outer_ret := Steps_return_some_ctx_b hsteps_inner_ret ...
```

**Step 6: The normalizeExpr result for sf_inner matches because:**
`normalizeExpr (.return (some (.return (some sf_inner.expr)))) K`
= `normalizeExpr sf_inner.expr (fun t => pure (.return (some t)))` (K discarded by return)
The IH already gives this.

### Variations for L10795, L10808, L10891, L10926, L10939:
- L10795: `.return (some (.yield (some inner_val) delegate))` — use `yield_some_arg` + `Steps_yield_some_ctx_b` inner, `Steps_return_some_ctx_b` outer
- L10808: `.return (some inner_val)` where inner_val is compound from tryCatch/while — single return layer
- L10891, L10926: Same as L10759/L10795 but nested under `.yield` instead of outer `.return`
- L10939: `.yield (some inner_val)` — single yield layer

### EXECUTION ORDER:
1. Do L10759 FIRST (double return, clearest case)
2. Verify with LSP (may time out — check `lean_diagnostic_messages` at that line)
3. If L10759 works, adapt for L10795, L10808, L10891, L10926, L10939 (same pattern)

### INFRASTRUCTURE ALREADY EXISTS:
- `Steps_return_some_ctx_b` (L2668): lifts Steps through `.return (some ·)` context
- `Steps_yield_some_ctx_b`: lifts through `.yield (some ·) delegate` (search for it)
- `HasLabeledInHead.return_some_arg` (L4947): `HasLabeledInHead v → HasLabeledInHead (.return (some v))`
- `HasLabeledInHead.yield_some_arg` (L4948): same for yield

## SKIP: trivialChain (blocked), if_branch, while, tryCatch, error prop cases (proof agent)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound inner depth L10759-L10939" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
