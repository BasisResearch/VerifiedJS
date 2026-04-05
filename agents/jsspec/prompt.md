# jsspec — ALL Steps_X_ctx_b helpers built! Now: objectLit + arrayLit helpers

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## MEMORY: ~400MB free. USE LSP ONLY.

## STATUS: ALL basic helpers DONE. CC 12 sorries (all architecturally blocked).

## MISSION: Build remaining list-based eval context helpers

### EXISTING helpers (ALL BUILT — great work!):
Steps_if_cond_ctx_b, Steps_seq_ctx_b, Steps_let_init_ctx_b, Steps_throw_ctx_b, Steps_return_some_ctx_b, Steps_await_ctx_b, Steps_yield_some_ctx_b, Steps_unary_ctx_b, Steps_binary_lhs_ctx_b, Steps_getProp_ctx_b, Steps_deleteProp_ctx_b, Steps_typeof_ctx_b, Steps_assign_ctx_b, Steps_getEnv_ctx_b, Steps_makeClosure_env_ctx_b, Steps_binary_rhs_ctx_b, Steps_call_func_ctx_b, Steps_setProp_obj_ctx_b, Steps_getIndex_obj_ctx_b, Steps_setIndex_obj_ctx_b, Steps_setProp_val_ctx_b, Steps_setIndex_val_ctx_b, Steps_call_env_ctx_b, Steps_call_arg_ctx_b, Steps_newObj_func_ctx_b, Steps_newObj_env_ctx_b, Steps_newObj_arg_ctx_b, Steps_getIndex_idx_ctx_b, Steps_setIndex_idx_ctx_b, Steps_makeEnv_values_ctx_b

### STILL MISSING — BUILD THESE (needed for objectLit and arrayLit catch-all sub-cases):
1. `Steps_objectLit_val_ctx_b` — lift steps through objectLit value position (prop list)
2. `Steps_arrayLit_elem_ctx_b` — lift steps through arrayLit element position (elem list)

These are list-based like Steps_makeEnv_values_ctx_b. Follow the same pattern with `done` and `remaining` parameters.

You also need corresponding step? helpers:
1. `step?_objectLit_val_ctx` — single step lifting through objectLit prop value
2. `step?_arrayLit_elem_ctx` — single step lifting through arrayLit element

### CONCURRENCY
- proof agent works on L9504 zone
- wasmspec works on L13060, L13866 zones
- You: add helpers in the helper section ONLY (around L1500-2850)

### SECONDARY: Verify all existing helpers compile
Use `lean_diagnostic_messages` on the helper section to confirm no errors from recent additions.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
