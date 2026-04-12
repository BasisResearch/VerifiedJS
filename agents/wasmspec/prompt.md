# wasmspec — CLOSE 2 SORRIES: noCallFrameReturn threading + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T01:05
- Total: **42 real sorries** (ANF 30, CC 12). Stable.
- P0+P1 (step_nonError_preserves + step_error) fully proved.
- P2: `HasReturnInHead_Steps_steppable_core` is sorry-free, wrapper at L16877 has isolated sorry.
- **Bridge lemma DONE**: `noCallFrameReturn_normalizeExpr_tryCatch_param` (~330 lines, proven).
- **Infrastructure is READY. TIME TO CLOSE SORRIES.**

## P0: THREAD noCallFrameReturn THROUGH anfConvert_step_star (L25442 — 1 sorry)

Your bridge lemma `noCallFrameReturn_normalizeExpr_tryCatch_param` is proved. Now USE it.

### Concrete steps:
1. **Check current goal** at L25442 with `lean_goal` — you need `catchParam ≠ "__call_frame_return__"`
2. **Add `noCallFrameReturn sf.expr = true`** as a hypothesis to `anfConvert_step_star`:
   - Find the theorem statement (search for `anfConvert_step_star`)
   - Add `(hncfr : noCallFrameReturn sf.expr = true)` as a precondition
   - This is valid: the initial expression from normalizeExpr has no call frame returns
3. **At L25442**, apply your bridge lemma:
   ```lean
   exact noCallFrameReturn_normalizeExpr_tryCatch_param ... hncfr ...
   ```
   (adjust args to match actual types)
4. **Prove preservation**: In the simulation step cases, prove `noCallFrameReturn sf'.expr = true` from `noCallFrameReturn sf.expr = true` + step properties. The key insight: Flat.step? only introduces `__call_frame_return__` tryCatch for function calls, and the call case handles the entire function execution internally before returning.
5. **Update callers** of anfConvert_step_star to provide the new precondition.

### If threading is too invasive (>50 edits):
Alternative: at L25442, directly derive `catchParam ≠ "__call_frame_return__"` from the normalizeExpr decomposition. The `hnorm` hypothesis tells you what normalizeExpr produced. Use `normalizeExpr_tryCatch_decomp` to extract the catchParam and show it equals the source catchParam, then use your bridge lemma.

**Expected: -1 sorry**

## P1: HasNonCallFrameTryCatchInHead (L16877 — 1 sorry)

The sorry needs `¬HasNonCallFrameTryCatchInHead a`.

### Approach: prove normalizeExpr_no_tryCatch_in_head
- `normalizeExpr` output never has tryCatch in eval-head position
- Structural induction: normalizeExpr produces .let, .seq, .labeled, .trivial — NONE are .tryCatch
- Then at L16877: `exact normalizeExpr_no_tryCatch_in_head ...`

### Alternative (if direct proof is hard):
Thread `¬HasNonCallFrameTryCatchInHead` through the caller chain:
- `hasReturnInHead_return_steps` → add as precondition
- `normalizeExpr_return_step_sim` → derive from normalizeExpr properties
- Top-level → derive from `normalizeExpr_no_tryCatch_in_head`

**Expected: -1 sorry**

## DO NOT WORK ON:
- L10799-L11557 (labeled trivial mismatch — proof agent)
- ClosureConvertCorrect.lean (jsspec)
- Any CC file

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — noCallFrameReturn threading + HasNonCallFrameTryCatch" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
