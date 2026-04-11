# proof — CLOSE noCallFrameReturn (L16955) + trivialChain batch

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- NoNestedAbrupt_step_preserved: **PROVED** (nice!)
- ANF: 30 sorries. CC: 16 (jsspec). Total: 46.

## P0: CLOSE L16955 (noCallFrameReturn sorry)

The sorry at L16955 needs to provide `catchParam ≠ "__call_frame_return__"`.

`normalizeExpr_tryCatch_step_sim` takes `hncf : catchParam ≠ "__call_frame_return__"`.

The key: `hna : NoNestedAbrupt sf.expr` is in scope. And `hnorm` says normalizeExpr produces `.tryCatch body catchParam catchBody finally_`. The Flat tryCatch preserves catchParam. The `noCallFrameReturn` predicate is separate from NoNestedAbrupt.

**APPROACH**: The `noCallFrameReturn` hypothesis `hncfr` should be available from anfConvert_step_star's preconditions. Check if it's already a parameter or if it needs to be added.

1. Run `lean_goal` at L16955 to see what's in context
2. Look for `hncfr : noCallFrameReturn sf.expr = true` in scope
3. If available, use: `noCallFrameReturn_tryCatch_param` (defined at L4120) which proves `cp ≠ "__call_frame_return__"` from `noCallFrameReturn (.tryCatch ...) = true`
4. If NOT in scope: we need to add `(hncfr : noCallFrameReturn sf.expr = true)` to `anfConvert_step_star` (L16798). Then:
   - Add it as a parameter after `NoNestedAbrupt sf.expr`
   - In the tryCatch case, `sf.expr` is known to be a tryCatch, so `noCallFrameReturn_tryCatch_param hncfr` gives the goal
   - Need to show preservation: when SimRel reconstructs sf', noCallFrameReturn sf'.expr = true. For most cases this is `noCallFrameReturn (.lit v) = true` (trivially rfl). For compound steps, it follows from depth decrease.

**The normalizeExpr decomposition**: `normalizeExpr (.tryCatch body cp cb fin) k` produces ANF `.tryCatch ...` where the catchParam comes from the Flat tryCatch's `cp`. The Flat `.tryCatch` has `noCallFrameReturn = true` from the precondition. Use `normalizeExpr_tryCatch_decomp` or similar to extract that the ANF catchParam equals the Flat cp.

**EXPECTED RESULT**: -1 sorry.

## P1: L16966 (body_sim IH) — INVESTIGATE ONLY

This needs anfConvert_step_star itself (strong induction/well-founded recursion). Run `lean_goal` to understand the shape. DO NOT attempt to close it — just document what it needs.

## P2: TRIVIALCHAIN HELPER (L10183-L10554, ~12 sorries)

These 12 sorries all need "stepping function/env to values first + list decomposition". They share a common pattern. Investigate if a single helper lemma could batch-close them:

1. Run `lean_goal` at L10183, L10408, L10491 to see their shapes
2. The pattern: labeled normalizeExpr produces `.call f e args` or `.newObj f e args` where f/e/args contain a sub-expression that steps. Need to show Flat steps correspondingly.
3. If a helper like `Flat_step?_call_func_step` or `Flat_step?_call_arg_step` exists, use it.

## SKIP: compound error prop (wasmspec), CC (jsspec), if_branch (K-mismatch blocked), while (blocked)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — noCallFrameReturn L16955" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
