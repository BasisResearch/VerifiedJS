# wasmspec — HasNonCallFrameTryCatchInEvalHead for L15348

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T20:05
- Total: **49 real sorries** (ANF 37, CC 12).
- YOU proved `callFrame_tryCatch_step_error_isLit` at L9488. Great work.
- The L15348 sorry is in `HasReturnInHead_Steps_steppable`: needs `¬HasTryCatchInHead s1.expr` but this is NOT preserved in general (function calls introduce call-frame tryCatch).

## P0: Close L15348 (HasTryCatchInHead sorry in Steps_steppable)

### YOUR PLAN from analysis (EXECUTE THIS):

1. **Define `HasNonCallFrameTryCatchInEvalHead`** — same as `HasTryCatchInHead` but the `tryCatch_direct` constructor requires `cp ≠ "__call_frame_return__"`. Only tracks non-call-frame tryCatch in eval-first positions (seq_left, let_init, binary_lhs, etc.).

2. **Prove `step_nonError_preserves_noNonCallFrameTryCatchInEvalHead`** — non-error steps don't introduce non-call-frame tryCatch. Key insight: only `call_func` introduces tryCatch (call-frame), and only source try/catch produces non-call-frame tryCatch.

3. **Prove normalizeExpr .return context has ¬HasNonCallFrameTryCatchInEvalHead** — since normalizeExpr(.return) never produces tryCatch in eval head.

4. **Use as invariant in Steps_steppable** — replace `¬HasTryCatchInHead` with `¬HasNonCallFrameTryCatchInEvalHead` in the hypothesis.

5. **Close L15348** using the new invariant + `callFrame_tryCatch_step_error_isLit` (already proved at L9488).

### CONCRETE IMPLEMENTATION:
Write the inductive type FIRST. Verify with LSP. Then write preservation lemma one constructor at a time. Each constructor should be independently verifiable.

### SIZE BUDGET: ~400 lines total
- Inductive definition: ~30 lines
- Preservation lemma: ~300 lines
- Caller fixup: ~70 lines

### FALLBACK:
If this is too large for one run, write JUST the inductive definition + 5 preservation cases, verify they compile, and leave the rest for next run.

## DO NOT WORK ON:
- L18952-L19264 (list cases — proof agent)
- ClosureConvertCorrect.lean (jsspec)
- L10843-L11214 (trivialChain zone)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasNonCallFrameTryCatchInEvalHead P0" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
