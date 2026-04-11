# wasmspec — TRIVIALCHAIN PASSTHROUGH SORRIES (10183, 10233, 10281, 10331, 10358, 10408)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- ANF: 42 sorries. CC: 23. Total: 65.
- Last wasmspec run: 2026-03-30. 12 DAYS AGO.
- Build passes. Error propagation done in Flat/Semantics.lean.

## SORRY LOCATIONS (current, verified by grep)

**Block 1 — trivialChain passthrough (6 sorries):**
- L10183 — binary_rhs: `¬HasLabeledInHead lhs`, lhs is trivialChain but stepping changes trivial
- L10233 — setProp_val: `¬HasLabeledInHead obj`, obj is trivialChain
- L10281 — getIndex_obj: proved (has labeled in head), but getIndex_idx at L10281 has sorry
- L10331 — setIndex_idx: `¬HasLabeledInHead obj`
- L10358 — setIndex_val: `¬HasLabeledInHead obj`
- L10408 — call_env: `¬HasLabeledInHead funcE`

**Block 2 — list decomposition (2 sorries):**
- L10410 — call_args: labeled in args list, needs list stepping
- L10462 — newObj_args: labeled in args list, needs list stepping

**Block 3 — first-element-has-no-labeled (3 sorries):**
- L10493 — objectLit first prop value
- L10525 — objectLit first prop value
- L10556 — arrayLit first element

**Block 4 — compound inner (6 sorries):**
- L10761, L10797, L10810, L10893, L10928, L10941 — depth induction cases

## P0: CLOSE BLOCK 1 — TRIVIALCHAIN PASSTHROUGH (6 sorries)

These sorries all share the same pattern: `¬HasLabeledInHead sub_expr` means `sub_expr` is a trivialChain. The issue is that `normalizeExpr_trivialChain_apply` gives an ANF trivial `t`, but we need to show the flat evaluation matches.

**Investigate approach:**
1. `lean_goal` at L10183 to see exact goal
2. `lean_local_search "trivialChain"` to find existing infrastructure
3. `lean_local_search "normalizeExpr_trivialChain"` to find the apply lemma
4. Check if there's a `trivialChain_eval_matches` lemma or equivalent

The core problem: when `¬HasLabeledInHead lhs` in binary_rhs case, `lhs` is already a value (trivialChain), so the labeled is in `rhs`. But `normalizeExpr (.binary op lhs rhs) k` first normalizes `lhs` (giving trivial t_lhs), then normalizes `rhs` (which has the labeled). The existing proof handles the `HasLabeledInHead lhs` case fine but not `¬HasLabeledInHead lhs`.

For the ¬HasLabeledInHead case:
- `lhs` must be trivialChain → normalizeExpr gives trivial t
- Need: Steps from {expr = .binary op lhs rhs, ...} that step rhs (keeping lhs)
- This requires showing lhs evaluates to a value first, then stepping rhs

**Check**: Is there a `step?_binary_rhs_ctx` or `Flat.step?` case for when lhs IS a value?
```
lean_local_search "step?_binary_rhs"
lean_local_search "Steps_binary_rhs"
```

## P1: IF BLOCK 1 DONE, assess Block 2 (list decomposition)
- `lean_local_search "Steps_" "list"` for list-related stepping
- These likely need new infrastructure (ExprList stepping lemmas)

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — trivialChain passthrough" >> agents/wasmspec/log.md`
2. `lean_goal` at L10183, L10233, L10331, L10358, L10408
3. Try to close each using trivialChain infrastructure
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
