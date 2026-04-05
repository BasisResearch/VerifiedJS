# wasmspec — Close normalizeExpr_if_branch_step sorries (L10559-10629)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~1.4GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11200-11360 (tryCatch) and L12400-12717 (break/continue/return)
- **YOU** own L8000-10912 (normalizeExpr step sim infrastructure)
- DO NOT touch lines outside your range

## YOUR ZONE: 36 sorries. You built great infrastructure — now close the sorries!

### Proved infrastructure (USE THESE):
- `trivialChain_eval_value` — eval trivial chain to value, preserves state
- `no_if_head_implies_trivial_chain` — ¬HasIfInHead → trivial chain
- `trivialChain_if_true_sim` — true branch simulation
- `trivialChain_if_false_sim` — false branch simulation
- `step?_tryCatch_body_ctx` — tryCatch body context stepping
- `Steps_tryCatch_body_ctx` — multi-step tryCatch body context
- `Steps_if_cond_ctx` (L1828) — multi-step if condition context

## IMMEDIATE TARGETS — normalizeExpr_if_branch_step (12 sorries, L10559-10629)

### GROUP A: hpres sorries (L10559, L10583, L10605) — 3 sorries
State preservation after lifted steps. Should follow from `trivialChain_eval_value` which proves env/heap/funcs/cs preservation. Try:
```
lean_multi_attempt at L10559
["exact ⟨rfl, rfl, rfl, rfl⟩", "exact trivialChain_eval_value ... |>.2.2"]
```

### GROUP B: L10567 — trivialChain → value → branch .if → then_flat (1 sorry)
This IS what `trivialChain_if_true_sim` proves. Wire it in:
```
lean_multi_attempt at L10567
["exact trivialChain_if_true_sim ...", "apply trivialChain_if_true_sim"]
```

### GROUP C: L10607 — ExprWellFormed (1 sorry)
ExprWellFormed for `ws.expr = .seq sf_a.expr b`. Should follow from ExprWellFormed composition.

### GROUP D: L10611 — core recursion (1 sorry)
¬HasIfInHead a → trivialChain eval → IH on b; or HasIfInHead a → IH on a.
Use `Classical.em (HasIfInHead a)` then apply IH in each branch.

### GROUP E: L10615-10628 — IH through eval contexts (5 sorries)
All follow the SAME pattern: apply IH + lift through `Steps_*_ctx`.
```lean
-- L10615: IH on init + Steps_let_init_ctx
-- L10619: IH on arg + Steps_throw_ctx
-- L10622: IH on v + Steps_return_some_ctx
-- L10625: IH on arg + Steps_await_ctx
-- L10628: IH on v + Steps_yield_some_ctx
```

### GROUP F: L10629 — exotic cases (1 sorry)
Binary, unary, getProp, etc. Most should be contradictions (no HasIfInHead for these).
```
lean_multi_attempt at L10629
["next => cases hif", "next => simp [HasIfInHead] at hif"]
```

### AFTER branch_step: L10668 (false version) — copy with true→false substitutions

### AFTER both: UNLOCK sorries (L10773-10898, 8 sorries) cascade automatically

## USE lean_multi_attempt AGGRESSIVELY
Before editing, test tactics at each sorry. This avoids rebuilds.

## PRIORITY: Groups A→B→E→F→D→C, then false version, then UNLOCKs

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
