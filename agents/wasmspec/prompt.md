# wasmspec — BREAK/CONTINUE + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T10:05
- Total: **47 real sorry instances** (ANF 35, CC 12). Previous count of 30 was undercounting.
- FLAT since 09:05. Nothing committed in the last hour.
- L18325 closed previously. But L18673 is a DIFFERENT sorry in the same area — still open.

## P0: BREAK/CONTINUE COMPOUND (2 sorries — L27249, L27250)

**LINE NUMBERS SHIFTED** from last prompt (was L27278, L27349). Verify with `lean_goal`.

- **L27249**: `(sorry /- catchParam ≠ "__call_frame_return__": needs noCallFrameReturn threaded as precondition or derived from source well-formedness -/)`
- **L27250**: `(sorry /- body_sim: inner simulation IH, needs anfConvert_step_star to be proved by strong induction -/)`

These are inside `anfConvert_step_star` (L27092). Both are in parenthesized sorry with comments explaining what's needed.

### For L27249:
Need to show catchParam ≠ "__call_frame_return__". This should follow from source well-formedness or from `noCallFrameReturn` being threaded as a precondition. Check:
1. `lean_local_search "noCallFrameReturn"` — does the precondition exist?
2. `lean_hover_info` on the surrounding context to see available hypotheses
3. If noCallFrameReturn is available, derive the inequality from it

### For L27250:
This is the inner simulation IH for the tryCatch body. It needs `anfConvert_step_star` itself (recursive). Check if strong induction is already set up — if the theorem uses `WellFoundedRelation` or `termination_by`, the IH should be available.

## P1: HasNonCallFrameTryCatch (1 sorry — L18673)

This is `(sorry /- ¬HasNonCallFrameTryCatchInHead a: EvalFirst approach INSUFFICIENT -/)` inside `HasReturnInHead_Steps_steppable` (L18663).

This is NOT the same as L18325 (which you already closed). The comment says the EvalFirst approach is insufficient. Check:
1. `lean_goal` at L18673 to see what's actually needed
2. The theorem is about HasReturnInHead + steppability. The sorry needs ¬HasNonCallFrameTryCatchInHead.
3. Since this is in a .return context, `normalizeExpr_tryCatch_not_return_none/some` should help establish that tryCatch can't appear.

## P2: END-OF-FILE SORRIES (2 — L27469, L27540)

Check what declarations these are in and what's needed. These may be simpler structural gaps.

## EXECUTION ORDER:
1. L27249 (noCallFrameReturn) — likely closable with existing infrastructure
2. L18673 (HasNonCallFrameTryCatch) — same infrastructure area as L18325
3. L27250 (IH) — depends on recursive structure
4. L27469, L27540 (end-of-file)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
