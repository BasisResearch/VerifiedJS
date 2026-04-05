# jsspec — Build remaining Steps_X_ctx_b helpers in ANFConvertCorrect.lean

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## MEMORY: ~4.4GB available. Still use LSP only.

## STATUS: CC 11 sorries (all architecturally blocked). Your mission: ANF helpers.

## MISSION: Build remaining eval context helpers

### EXISTING helpers (L2357-2564, DO NOT DUPLICATE):
Already built: Steps_if_cond_ctx_b, Steps_seq_ctx_b, Steps_let_init_ctx_b, Steps_throw_ctx_b, Steps_return_some_ctx_b, Steps_await_ctx_b, Steps_yield_some_ctx_b, Steps_unary_ctx_b, Steps_binary_lhs_ctx_b, Steps_getProp_ctx_b, Steps_deleteProp_ctx_b, Steps_typeof_ctx_b, Steps_assign_ctx_b, Steps_getEnv_ctx_b, Steps_makeClosure_env_ctx_b, Steps_binary_rhs_ctx_b, Steps_call_func_ctx_b, Steps_setProp_obj_ctx_b, Steps_getIndex_obj_ctx_b, Steps_setIndex_obj_ctx_b, Steps_setProp_val_ctx_b, Steps_setIndex_val_ctx_b

### STILL MISSING — BUILD THESE (needed for L9074, L12630, L13436 catch-alls):
1. `Steps_call_env_ctx_b` — lift steps through `.call (.lit f) [·] args` (call env position)
2. `Steps_call_arg_ctx_b` — lift steps through call argument position
3. `Steps_newObj_func_ctx_b` — lift steps through `.newObj [·] envExpr args`
4. `Steps_newObj_env_ctx_b` — lift steps through newObj env position
5. `Steps_newObj_arg_ctx_b` — lift steps through newObj argument position
6. `Steps_getIndex_idx_ctx_b` — lift steps through `.getIndex (.lit obj) [·]`
7. `Steps_setIndex_idx_ctx_b` — lift steps through `.setIndex (.lit obj) [·] val`
8. `Steps_makeEnv_values_ctx_b` — lift steps through makeEnv value position
9. `Steps_objectLit_val_ctx_b` — lift steps through objectLit value position
10. `Steps_arrayLit_elem_ctx_b` — lift steps through arrayLit element position

### Pattern to follow (copy from Steps_binary_rhs_ctx_b at L2504):
Each new helper needs:
1. A `step?_X_ctx` single-step helper (check existing ones around L1654-1900)
2. Then `Steps_X_ctx_b` using `Steps_ctx_lift_b` with the step? helper

### CONCURRENCY
- proof agent works on L9066-10976
- wasmspec works on L12630, L13436 zones
- You: add helpers in the helper section ONLY (around L1654-2564)

### PRIORITY: Start with Steps_getIndex_idx_ctx_b and Steps_setIndex_idx_ctx_b — these are simpler 2-position helpers like binary_rhs.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
