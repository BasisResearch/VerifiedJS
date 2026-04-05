# jsspec — Build missing Steps_X_ctx_b helpers in ANFConvertCorrect.lean

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- MEMORY: 7.7GB total, NO swap. ~1.6GB available.

## STATUS: CC is DONE (all 12 blocked). Your new mission: ANF helpers.

## MISSION: Build missing eval context helpers

The proof agent needs `Steps_X_ctx_b` helper theorems to close L8755 (catch-all sorry). These are mechanical theorems that lift inner steps through an evaluation context.

### EXISTING helpers (around L2115-2252, DO NOT DUPLICATE):
- `Steps_if_cond_ctx_b`, `Steps_seq_ctx_b`, `Steps_let_init_ctx_b`
- `Steps_throw_ctx_b`, `Steps_return_some_ctx_b`, `Steps_await_ctx_b`
- `Steps_yield_some_ctx_b`, `Steps_unary_ctx_b`, `Steps_binary_lhs_ctx_b`
- `Steps_getProp_ctx_b`, `Steps_deleteProp_ctx_b`, `Steps_typeof_ctx_b`
- `Steps_assign_ctx_b`, `Steps_getEnv_ctx_b`, `Steps_makeClosure_env_ctx_b`

### MISSING helpers — BUILD THESE (add after L2252):
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

### Pattern to follow (copy from Steps_binary_lhs_ctx_b at ~L2192):
Each new helper should:
1. Take `h : Steps sf1 sf2 trace`
2. Wrap each step in the appropriate eval context
3. Return `Steps (wrapContext sf1) (wrapContext sf2) trace`

Look at the exact signature of `Steps_binary_lhs_ctx_b` and replicate the pattern for the new eval context position.

### BUILD COORDINATION
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use LSP tools instead.

### CONCURRENCY
- proof agent works on L8754-10657
- wasmspec works on L12000-12750
- You: add helpers AFTER L2252 only (helper section)

## PRIORITY: Start with Steps_binary_rhs_ctx_b and Steps_call_func_ctx_b — these are most likely needed first.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
