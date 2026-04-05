# wasmspec — 2 sorries remain. Expand catch-alls using NEW helpers!

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE, leave it alone
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~4.4GB available. Still use LSP only.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9066-10976
- jsspec works on helper section L1654-2564
- **YOU** own L12630 and L13436 zones

## YOUR 2 SORRIES:

| Line | Description |
|------|-------------|
| L12630 | catch-all in normalizeExpr_if_branch_step (true) |
| L13436 | catch-all in normalizeExpr_if_branch_step_false |

## NEW HELPERS AVAILABLE (jsspec just built these!)
You can NOW prove more cases using these newly-available Steps_X_ctx_b:
- `Steps_binary_rhs_ctx_b` (L2504) — for binary_rhs cases
- `Steps_call_func_ctx_b` (L2514) — for call_func cases
- `Steps_setProp_obj_ctx_b` (L2524) — for setProp_obj cases
- `Steps_setProp_val_ctx_b` (L2554) — for setProp_val cases
- `Steps_getIndex_obj_ctx_b` (L2534) — for getIndex_obj cases
- `Steps_setIndex_obj_ctx_b` (L2544) — for setIndex_obj cases
- `Steps_setIndex_val_ctx_b` (L2564) — for setIndex_val cases

## ACTION PLAN
1. Use `lean_goal` at L12630 to see what constructors the `| _ =>` catches
2. Replace the catch-all with explicit cases for each constructor:
   - For each that has a Steps_X_ctx_b helper: prove it following the pattern of binary_lhs (L12617)
   - For each that doesn't have a helper yet: keep as `| X => sorry`
3. Do the same for L13436 (mirror of L12630)

## EXPECTED: You should be able to close 7+ sub-cases (binary_rhs, call_func, setProp_obj, setProp_val, getIndex_obj, setIndex_obj, setIndex_val). The remaining (call_env/args, newObj_*, getIndex_idx, setIndex_idx, makeEnv, objectLit, arrayLit) stay as sorry until jsspec builds their helpers.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
