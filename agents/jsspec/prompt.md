# jsspec — List-based sorry cases in labeled_branch_step

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## MEMORY: ~2.5GB free. USE LSP ONLY.

## YOUR 5 SORRIES (all list-based in labeled_branch_step):

```
    | call_args h_args => sorry       -- L9919
    | newObj_args h_args => sorry      -- L9944
    | makeEnv_values h_vals => sorry   -- L9945
    | objectLit_props h_props => sorry -- L9946
    | arrayLit_elems h_elems => sorry  -- L9947
```

## CONCURRENCY
- proof agent owns L9822-9918, L9943 (second-position cases)
- wasmspec owns L13593-13627, L14523-14557 (if_branch)
- **YOU** own L9919, L9944-L9947 ONLY

## APPROACH

These cases have `HasLabeledInHead` somewhere in a list of sub-expressions. The pattern:
1. Elements before the labeled one are trivialChains (eval to values)
2. Apply IH on the labeled element
3. Use the list-based context helpers

### Available helpers:
- `Steps_call_arg_ctx_b funcExpr envExpr done remaining` — for call_args
- `Steps_newObj_arg_ctx_b funcExpr envExpr done remaining` — for newObj_args
- `Steps_makeEnv_values_ctx_b done remaining` — for makeEnv_values
- `Steps_objectLit_val_ctx_b` — for objectLit_props
- `Steps_arrayLit_elem_ctx_b` — for arrayLit_elems

### Steps:
1. `lean_goal` at each sorry to see the exact proof state
2. The `HasLabeledInHead` constructor for lists likely carries an index/membership proof
3. You'll need to show all preceding elements are trivialChains
4. Then IH on the labeled element, lift through list context, wire up

### IF LIST CASES ARE TOO COMPLEX:
Fall back to running `lean_diagnostic_messages` on the file and reporting compilation status. Also check if any of the existing helpers need bug fixes.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
