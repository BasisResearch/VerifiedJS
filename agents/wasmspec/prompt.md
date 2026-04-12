# wasmspec — CLOSE P2 (HasNonCallFrameTryCatch threading)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T00:05
- Total: **42 real sorries** (ANF 30, CC 12). Stable.
- P0+P1 fully proved (step_nonError_preserves + step_error).
- P2 restructured: `HasReturnInHead_Steps_steppable_core` is sorry-free, wrapper has isolated sorry.
- You are currently running on P2 threading. CONTINUE.

## P0: THREAD ¬HasNonCallFrameTryCatchInHead THROUGH CALLERS (L16490)

The sorry at L16490 needs `¬HasNonCallFrameTryCatchInHead a` where `a` comes from `normalizeExpr` with a `.return` continuation.

### Your restructuring is good. Now complete the threading:

1. **Prove normalizeExpr_no_tryCatch_in_head**: normalizeExpr output never has tryCatch in eval-head position (tryCatch only appears from Flat.step? function calls, not from normalizeExpr)
   - Structural induction on expression
   - Key cases: normalizeExpr produces .let, .seq, .labeled, .trivial, etc. — NONE are .tryCatch

2. **Thread through callers** (~90 edits across 3 theorems per your last analysis):
   - `hasReturnInHead_return_steps` needs `¬HasNonCallFrameTryCatchInHead` precondition
   - `normalizeExpr_return_step_sim` needs to derive it from normalizeExpr properties
   - Top-level caller derives from `normalizeExpr_no_tryCatch_in_head`

3. **Alternative (simpler)**: At L16490, directly prove `¬HasNonCallFrameTryCatchInHead a` by:
   - `a` = result of `normalizeExpr sf.expr (fun t => pure (.return (some (.trivial t))))`
   - Use `normalizeExpr_no_tryCatch_in_head` directly
   - No need to thread through callers if you can derive it at the sorry site

**Expected: -1 sorry**

## P1: noCallFrameReturn (L25055) — SECOND PRIORITY

The sorry needs `catchParam ≠ "__call_frame_return__"`. Approach:
1. Prove: normalizeExpr output has no "__call_frame_return__" catch params
2. Or: add NoCallFrameParam predicate to SimRel preconditions

Only attempt after P0 is done.

**Expected: -1 sorry**

## DO NOT WORK ON:
- L10799-L11170 (labeled trivial mismatch — proof agent)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — P2 threading continued" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
