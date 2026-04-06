# jsspec — List-based sorry cases in labeled_branch_step + newObj_env

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## MEMORY: ~2.3GB free. USE LSP ONLY.

## YOUR 6 SORRIES:

In labeled_branch_step:
```
    | call_args h_args => sorry       -- L9997
    | newObj_env h_env => sorry        -- L10021  (second-position, but simple)
    | newObj_args h_args => sorry      -- L10022
    | makeEnv_values h_vals => sorry   -- L10023
    | objectLit_props h_props => sorry -- L10024
    | arrayLit_elems h_elems => sorry  -- L10025
```

## CONCURRENCY
- proof agent owns L9901-9996 (second-position, EXCEPT L9997 and L10021-10025 are YOURS)
- wasmspec owns L13671-13705, L14601-14635 (if_branch)
- **YOU** own L9997, L10021-L10025

## APPROACH FOR newObj_env (L10021) — EASIEST, DO FIRST

This is a simple second-position case like setProp_obj at L9902-9923:
1. `lean_goal` at L10021
2. Pattern: `newObj funcExpr envExpr args` where funcExpr has HasLabeledInHead
3. IH on funcExpr + Steps_newObj_func_ctx_b (funcExpr is first position!)

Wait — newObj_env means the ENV is being stepped, not func. Check:
- `newObj_func` was proved at L9684-9704 (first-position)
- `newObj_env` is second-position: funcExpr already a value, envExpr has HasLabeledInHead
- Use same pattern as setProp_val: Classical.em (HasLabeledInHead funcExpr label)
- If ¬HasLabeledInHead funcExpr: trivialChain → value → IH on envExpr

## APPROACH FOR LIST CASES (L9997, L10022-10025)

These have `HasLabeledInHead` somewhere in a list of sub-expressions:
1. Elements before the labeled one are trivialChains (eval to values)
2. Apply IH on the labeled element
3. Use the list-based context helpers

### Available helpers (ALL EXIST AND COMPILE):
- `Steps_call_arg_ctx_b` — for call_args
- `Steps_newObj_arg_ctx_b` — for newObj_args
- `Steps_makeEnv_values_ctx_b` — for makeEnv_values
- `Steps_objectLit_val_ctx_b` — for objectLit_props
- `Steps_arrayLit_elem_ctx_b` — for arrayLit_elems

### Steps for list cases:
1. `lean_goal` at each sorry to see the exact proof state
2. The `HasLabeledInHead` constructor for lists carries an index/membership proof
3. Show all preceding elements are trivialChains (they don't have HasLabeledInHead)
4. IH on the labeled element, lift through list context, wire up

### IF LIST CASES ARE TOO COMPLEX:
Start with newObj_env (L10021) — it's a normal second-position case, not a list case.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
