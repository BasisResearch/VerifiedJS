# wasmspec — 2 catch-all sorries remain. ALL helpers now exist!

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE, leave it alone
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~400MB free. USE LSP ONLY — no builds.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9504 zone (labeled_branch_step catch-all)
- jsspec works on helper section L1500-2850
- **YOU** own L13060 and L13866 zones ONLY

## YOUR 2 SORRIES:

| Line | Description |
|------|-------------|
| L13060 | catch-all in normalizeExpr_if_branch_step (true) |
| L13866 | catch-all in normalizeExpr_if_branch_step_false |

## ALL HELPERS NOW AVAILABLE!

jsspec has built ALL needed Steps_X_ctx_b helpers. You can now prove EVERY sub-case:

| Helper | Location |
|--------|----------|
| Steps_binary_rhs_ctx_b | L2675 |
| Steps_call_func_ctx_b | L2685 |
| Steps_call_env_ctx_b | L2745 |
| Steps_call_arg_ctx_b | L2755 |
| Steps_newObj_func_ctx_b | L2768 |
| Steps_newObj_env_ctx_b | L2778 |
| Steps_newObj_arg_ctx_b | L2788 |
| Steps_setProp_obj_ctx_b | L2695 |
| Steps_setProp_val_ctx_b | L2725 |
| Steps_getIndex_obj_ctx_b | L2705 |
| Steps_getIndex_idx_ctx_b | L2801 |
| Steps_setIndex_obj_ctx_b | L2715 |
| Steps_setIndex_idx_ctx_b | L2811 |
| Steps_setIndex_val_ctx_b | L2735 |
| Steps_makeEnv_values_ctx_b | L2821 |

## ACTION PLAN
1. Use `lean_goal` at L13060 to see what constructors the `| _ =>` catches
2. Replace the catch-all with explicit cases for each constructor
3. Follow the pattern of the already-proved cases above it (e.g., binary_lhs)
4. Each case: rename_i, simp, depth bound, IH, Steps_X_ctx_b, refine, preservation, normalizeExpr, well-formedness
5. For list cases (call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems): these are harder, can sorry individually
6. Do the same for L13866 (mirror of L13060)

## EXPECTED: You should be able to close most sub-cases. Only objectLit_props and arrayLit_elems may need individual sorries.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
