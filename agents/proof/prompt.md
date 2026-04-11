# proof — CLOSE trivialChain BATCH (L10183-L10554, 12 sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- NoNestedAbrupt_step_preserved: PROVED (nice!)
- ANF: 31 sorries. CC: 15 (jsspec). Total: 46.

## P0: TRIVIALCHAIN BATCH (L10183-L10554, 12 sorries) — HIGHEST ROI

These 12 sorries are ALL in `normalizeExpr_labeled_step_sim` and share a common pattern. Each is a case where a sub-expression of `.call`/`.newObj`/`.objectLit`/`.arrayLit` steps.

**INVESTIGATE FIRST**: Run `lean_goal` at L10183, L10408, L10460 to see the exact shapes.

**EXPECTED PATTERN**: Each sorry needs to show that when a sub-expression `e` of a compound form steps (Flat.step? on the inner `e`), the whole compound form also steps (via a context-lifting lemma).

**APPROACH**:
1. Run `lean_local_search "trivialChain"` to find existing helpers
2. Run `lean_local_search "Steps_ctx"` for context-lifting lemmas
3. For each sorry:
   - Run `lean_goal` to see the exact goal
   - Identify which sub-expression steps (func, env, arg, prop value, element)
   - Find or create a `Flat_step?_FOO_ctx` lemma that lifts the inner step
   - Apply it
4. If a helper lemma is missing, create ONE that covers the general pattern, then reuse it

**DO THEM ONE AT A TIME**: Close L10183, verify, log, then L10231, verify, log, etc.

## P1: L16999 (noCallFrameReturn) — IF P0 IS BLOCKED

The sorry needs `catchParam ≠ "__call_frame_return__"`:
1. Run `lean_goal` at L16999
2. Look for `hncfr : noCallFrameReturn sf.expr = true` in scope
3. Use `noCallFrameReturn_tryCatch_param` (L4120) to extract the proof

## P2: L17229, L17300 — INVESTIGATE ONLY

Run `lean_goal` on each. Document what they need. Do NOT attempt without understanding.

## SKIP: compound error prop (wasmspec), CC (jsspec), if_branch (K-mismatch), while (blocked)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — trivialChain batch L10183-L10554" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
