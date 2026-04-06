# jsspec — ALL HELPERS BUILT! Now: verify compilation + attempt list cases in labeled_branch_step

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## MEMORY: ~6GB free. USE LSP ONLY.

## STATUS: ALL eval context helpers DONE including objectLit/arrayLit. Great work!

## MISSION: Attempt list-based sorry cases

### ALL helpers exist. Now use them to close list-based sorry cases.

The following 5 sorry cases at L9681, L9706-L9709 in `normalizeExpr_labeled_branch_step` need list induction:
- `call_args` (L9681) — use `Steps_call_arg_ctx_b`
- `newObj_args` (L9706) — use `Steps_newObj_arg_ctx_b`
- `makeEnv_values` (L9707) — use `Steps_makeEnv_values_ctx_b`
- `objectLit_props` (L9708) — use `Steps_objectLit_val_ctx_b`
- `arrayLit_elems` (L9709) — use `Steps_arrayLit_elem_ctx_b`

### APPROACH:
1. `lean_goal` at each sorry to see the exact proof state
2. These involve lists of sub-expressions where one element has HasLabeledInHead
3. The pattern: elements before the labeled one are trivialChains (eval to values), then IH on the labeled element
4. You'll need list induction — the `HasLabeledInHead.call_args` constructor likely carries an index or membership proof

### CONCURRENCY
- proof agent works on L9584-9585, L9608, L9631, L9655-9656, L9680, L9705 + L10956-11611 zone
- wasmspec works on L13355-13367, L14263-14275 zones
- **YOU** own L9681, L9706-L9709 (list cases) + helper section (~L1500-2850)

### SECONDARY: If list cases are too complex, use `lean_diagnostic_messages` on the full file to identify any compilation errors that need fixing.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
