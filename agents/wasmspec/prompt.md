# wasmspec — PROVE HasNonCallFrameTryCatch LEMMA BODIES

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T22:05
- Total: **44 real sorries** (ANF 32, CC 12). Down from 50 (-6).
- You restructured Steps_steppable last run. 3 sorry stubs remain.
- proof agent closed 5 HasReturnInHead list cases.

## YOUR 3 SORRY STUBS (all in ANF)

These are the 3 sorries you created when restructuring Steps_steppable. You should be working on filling them in now.

### P0: step_nonError_preserves_noNonCallFrameTryCatch
Strong induction on `e.depth`. Case split on `e`:
- **Compound expressions**: Non-error step modifies sub-expression. Wrapper preserved. IH on sub-expression (depth decreased).
- **`.call f env args` with all values**: Produces `tryCatch body "__call_frame_return__" ...` — this IS a call-frame tryCatch, so `¬HasNonCallFrameTryCatchInHead` holds.
- **`.tryCatch body cp cb fin`** with `cp ≠ "__call_frame_return__"`: Contradiction with `¬HasNonCallFrameTryCatchInHead` hypothesis.

### P1: step_error_noNonCallFrameTryCatch_isLit
Strong induction on `e.depth`. Case split:
- **Non-tryCatch compound**: Error from sub-expression → wrapper drops → recurse by IH.
- **`.tryCatch body cp cb fin`**: Must be call-frame. Apply `callFrame_tryCatch_step_error_isLit`.
- **Atoms**: Don't step to error, or deterministic.

### P2: Initial condition (outer application sorry)
Prove `¬HasNonCallFrameTryCatchInHead a` where `a` comes from `normalizeExpr ... (.return ...)`. Should follow from `normalizeExpr_return_*` theorems.

## PRIORITY: P0 → P1 → P2

Closing all 3: **-3 sorries**.

## DO NOT WORK ON:
- L11345, L11377, L11408 (labeled list tail — proof agent)
- L5005, L6143 (break/continue — proof agent)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasNonCallFrameTryCatch P0+P1+P2" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
