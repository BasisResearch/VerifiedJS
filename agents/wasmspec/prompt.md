# wasmspec — BREAK/CONTINUE + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T11:05
- **BUILD FIXED** by supervisor (24 compilation errors resolved in noCallFrameReturn_normalizeExpr area).
- ANF line numbers shifted ~+280. Always verify with `lean_goal`.
- Break/continue cases DECOMPOSED from 2 monolithic sorries to 18 per-case sorries (proof agent owns most).

## P0: noCallFrameReturn (L29822) — catchParam ≠ "__call_frame_return__"

This is `(sorry /- catchParam ≠ "__call_frame_return__": needs noCallFrameReturn ... -/)`.

**Approach**: The file now has `noCallFrameReturn_normalizeExpr_tryCatch_param_aux` (around L10087-10216) which proves that if `noCallFrameReturn e = true` and `normalizeExpr e k` produces `.tryCatch`, then `catchParam ≠ "__call_frame_return__"`. **This infrastructure was just fixed by the supervisor** (was previously broken with 24 compilation errors).

Steps:
1. `lean_goal` at L29822 to see what's needed
2. Check if `noCallFrameReturn_normalizeExpr_tryCatch_param` (no `_aux`) exists as a wrapper
3. Apply it with the `hncfr` hypothesis from the context

## P1: HasNonCallFrameTryCatch (L19022) — ¬HasNonCallFrameTryCatchInHead a

This is the hardest sorry. The comment explains three approaches (A, B, C):
- **(A)** Thread `noCallFrameReturn` as precondition + prove ¬Head when all tryCatch are user-level
- **(B)** Restructure `_core` to use normalizeExpr evidence directly in Steps induction
- **(C)** Factor through a "no tryCatch at all" predicate provable from noCallFrameReturn + normalizeExpr

**Recommended: Approach C.** Define:
```lean
def noTryCatchInHead : Flat.Expr → Prop := ...
```
Prove: `noCallFrameReturn e → normalizeExpr e k produces .return → noTryCatchInHead (normalizeExpr result)`
Then: `noTryCatchInHead → ¬HasNonCallFrameTryCatchInHead`

**BUT**: The comment says `step_error_noNonCallFrameTryCatch_isLit` has 70+ errors. Fix those first.

## P2: body_sim IH (L29823) — inner simulation recursive call

This needs `anfConvert_step_star` itself (strong induction). Check if the theorem is set up with `WellFoundedRelation` or has a fuel parameter that provides the IH.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
