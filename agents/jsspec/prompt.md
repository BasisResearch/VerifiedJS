# jsspec — Attempt list-based sorry cases in labeled_branch_step

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## MEMORY: ~2.3GB free. USE LSP ONLY.

## YOUR 5 SORRIES (all list-based):

In labeled_branch_step (~L10159-10187):
```
    | call_args h_args => sorry       -- L10159
    | newObj_args h_args => sorry      -- L10184
    | makeEnv_values h_vals => sorry   -- L10185
    | objectLit_props h_props => sorry -- L10186
    | arrayLit_elems h_elems => sorry  -- L10187
```

Note: newObj_env (L10183) is a second-position case owned by proof agent.

## CONCURRENCY
- proof agent owns L10063-10158 (second-position cases)
- wasmspec owns L13697+, L14792+ (if_branch)
- **YOU** own L10159, L10184-L10187

## ===== K-MISMATCH WARNING =====

The second-position cases (binary_rhs, setProp_val, etc.) are blocked by a K-mismatch issue: when the first sub-expression evaluates from .var x to .lit v, `trivialOfFlat(.var x) ≠ trivialOfFlatValue v`, causing the ANF body to change.

**List cases MAY have the same issue.** Before spending time on proofs, CHECK:

For call_args: `normalizeExpr (.call f env args) K` processes f, then env, then args in sequence. The continuation for the labeled arg wraps previous args' trivials. After stepping previous args to values, the trivials change → K changes → body changes.

**Quick test**: Use `lean_goal` at each sorry to see the exact proof state. Then check if the HasLabeledInHeadList hypothesis constrains which list element has the labeled. If it's the FIRST element (no preceding elements to evaluate), there's no K-mismatch.

## APPROACH

### Step 1: Investigate K-mismatch for list cases
1. `lean_goal` at L10159 (call_args)
2. Check what `h_args : HasLabeledInHeadList args label` looks like
3. If the proof requires evaluating preceding elements → K-mismatch → blocked
4. If first element has labeled → no K-mismatch → provable

### Step 2: If first-element case is provable
For HasLabeledInHeadList.head (labeled element is first in list):
- No preceding elements to evaluate
- K for the first element matches between original and stepped states
- IH on the first element, lift through list context
- Remaining elements unchanged

### Step 3: If K-mismatch confirmed
Report findings in log. Consider whether HasLabeledInHeadList constructors are used downstream or if they're dead code (check call sites of normalizeExpr_labeled_branch_step).

### Available helpers:
- `Steps_call_arg_ctx_b`, `Steps_newObj_arg_ctx_b`, `Steps_makeEnv_values_ctx_b`
- `Steps_objectLit_val_ctx_b`, `Steps_arrayLit_elem_ctx_b`
- `normalizeExprList_labeled_or_k`, `normalizeProps_labeled_or_k`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
