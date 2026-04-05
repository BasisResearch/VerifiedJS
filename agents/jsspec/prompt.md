# jsspec — ALL 12 CC sorries confirmed architecturally blocked. Help proof agent instead.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- MEMORY: 7.7GB total, NO swap. ~1.6GB available.

## STATUS: CC is DONE (blocked ceiling reached)

You confirmed L7917 (functionDef) is architecturally blocked due to step-count mismatch between Core (1 step) and Flat (multi-step makeClosure+makeEnv). All 12 CC sorries are now blocked by architectural issues.

**No more CC work to do.**

## NEW MISSION: Help proof agent with ANF eval context helpers

The proof agent needs `Steps_X_ctx_b` helper theorems for various eval contexts in ANFConvertCorrect.lean. These are mechanical theorems that lift inner steps through an evaluation context.

**You CAN now edit ANFConvertCorrect.lean** — but ONLY to add infrastructure theorems in the HELPER section (before line 8000, look for where other `Steps_X_ctx_b` theorems are defined).

### What to build (each follows the pattern of existing Steps_await_ctx_b):
1. `Steps_binary_rhs_ctx_b` — lift steps through `.binary op lhs [·]`
2. `Steps_call_func_ctx_b` — lift steps through `.call [·] args`
3. `Steps_call_arg_ctx_b` — lift steps through call argument position
4. `Steps_setProp_obj_ctx_b` — lift steps through `.setProp [·] prop val`
5. `Steps_setProp_val_ctx_b` — lift steps through `.setProp obj prop [·]`
6. `Steps_getIndex_obj_ctx_b` — lift steps through `.getIndex [·] idx`

### Pattern to follow
Find `Steps_await_ctx_b` in the file. Each new helper should:
1. Take `h : Steps sf1 sf2 trace`
2. Wrap each step in the appropriate eval context
3. Return `Steps (wrapContext sf1) (wrapContext sf2) trace`

### BUILD COORDINATION
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use LSP tools instead.

### CONCURRENCY
- proof agent works on L8915-10817
- wasmspec works on L12100-12900
- You: add helpers BEFORE L8000 only

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
