# jsspec — Build missing Steps_X_ctx_b helpers in ANFConvertCorrect.lean

## RULES
- **DO NOT** run `lake build` — memory is tight (~300MB free). USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## STATUS: CC build fixed (all 12 CC blocked). Your mission: ANF helpers.

## MISSION: Build missing eval context helpers

The proof agent needs `Steps_X_ctx_b` helper theorems to close L8802 (catch-all sorry). These are mechanical theorems that lift inner steps through an evaluation context.

### EXISTING helpers (around L2115-2280, DO NOT DUPLICATE):
- `Steps_if_cond_ctx_b`, `Steps_seq_ctx_b`, `Steps_let_init_ctx_b`
- `Steps_throw_ctx_b`, `Steps_return_some_ctx_b`, `Steps_await_ctx_b`
- `Steps_yield_some_ctx_b`, `Steps_unary_ctx_b`, `Steps_binary_lhs_ctx_b`
- `Steps_getProp_ctx_b`, `Steps_deleteProp_ctx_b`, `Steps_typeof_ctx_b`
- `Steps_assign_ctx_b`, `Steps_getEnv_ctx_b`, `Steps_makeClosure_env_ctx_b`

### ALSO NEEDED: step?_X_ctx helpers
For each Steps_X_ctx_b, there should be a corresponding `step?_X_ctx` single-step helper. Check which ones exist around L1654-1760 and add any missing.

### MISSING helpers — BUILD THESE (add after existing helpers):
1. `Steps_binary_rhs_ctx_b` — lift steps through `.binary op (.lit lhs) [·]`
2. `Steps_call_func_ctx_b` — lift steps through `.call [·] args`
3. `Steps_call_arg_ctx_b` — lift steps through call argument position
4. `Steps_setProp_obj_ctx_b` — lift steps through `.setProp [·] prop val`
5. `Steps_setProp_val_ctx_b` — lift steps through `.setProp (.lit obj) prop [·]`
6. `Steps_getIndex_obj_ctx_b` — lift steps through `.getIndex [·] idx`
7. `Steps_setIndex_obj_ctx_b` — lift steps through `.setIndex [·] idx val`
8. `Steps_setIndex_val_ctx_b` — lift steps through `.setIndex (.lit obj) idx [·]`
9. `Steps_newObj_arg_ctx_b` — lift steps through newObj argument position
10. `Steps_objectLit_val_ctx_b` — lift steps through objectLit value position
11. `Steps_arrayLit_elem_ctx_b` — lift steps through arrayLit element position

### Pattern to follow (copy from Steps_binary_lhs_ctx_b):
Each new helper should:
1. First add a `step?_X_ctx` single-step helper
2. Then add a `Steps_X_ctx_b` using `Steps_ctx_lift_b` with the step? helper

### CONCURRENCY
- proof agent works on L8794-10865
- wasmspec works on L12355, L13161 zones
- You: add helpers in the helper section ONLY (around L1654-2280)

## PRIORITY: Start with Steps_binary_rhs_ctx_b and Steps_setProp_obj_ctx_b — these are needed for L8802.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
