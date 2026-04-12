# wasmspec — L18325: USE YOUR FIXED INFRASTRUCTURE TO CLOSE IT

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T08:05
- Total: **42 real sorries** (ANF 30, CC 12). Unchanged for 2 hours.
- EvalFirst approach: **DEAD** (confirmed by your own analysis).
- **BUT**: You FIXED the infrastructure at 07:37!
  - `step_error_noNonCallFrameTryCatch_isLit`: 0 errors ✓
  - `step_nonError_preserves_noNonCallFrameTryCatch`: 0 errors ✓
  These lemmas WORK. Now USE them.

## P0: L18325 — CLOSE THIS (-1 sorry)

The sorry is: `¬HasNonCallFrameTryCatchInHead a` passed to `HasReturnInHead_Steps_steppable_core`.

Your fixed infrastructure gives you:
1. `step_error_noNonCallFrameTryCatch_isLit`: error steps with no non-call-frame tryCatch produce .lit
2. `step_nonError_preserves_noNonCallFrameTryCatch`: non-error steps preserve no-non-call-frame-tryCatch

### THE PLAN (approach A+C combined):

**Step 1**: Thread `noCallFrameReturn` into `HasReturnInHead_Steps_steppable`.
Add `(hncfr : noCallFrameReturn a)` as a parameter. This is available from callers because
the expression comes from normalizeExpr in .return context on a source program with noCallFrameReturn.

**Step 2**: Prove `noCallFrameReturn a → ¬HasNonCallFrameTryCatchInHead a`.
Key insight: in a program with noCallFrameReturn, ALL tryCatches are user-level (non-call-frame).
normalizeExpr in .return context never produces tryCatch (normalizeExpr_tryCatch_not_return_none/some).
So the expression has NO tryCatch at all → certainly no non-call-frame tryCatch in head.

Wait — this is wrong. noCallFrameReturn means no `return "__call_frame_return__"`, not "no tryCatch".
The actual insight: tryCatches in normalizeExpr .return output are ALL call-frame tryCatches (wrapping
function calls). So HasNonCallFrameTryCatchInHead is false.

**Step 2 (corrected)**: Prove `NoNonCallFrameTryCatch a` from the normalizeExpr .return context.
Since normalizeExpr_tryCatch_not_return_none/some shows normalizeExpr never produces tryCatch in
.return context, the output has no tryCatch at all. No tryCatch → no non-call-frame tryCatch.

Then: `NoNonCallFrameTryCatch a → ¬HasNonCallFrameTryCatchInHead a` (trivial — Head requires tryCatch to exist).

**Step 3**: Replace the sorry at L18325 with:
```lean
(have hncf : ¬HasNonCallFrameTryCatchInHead a :=
   noTryCatch_implies_noNonCallFrameTryCatchInHead a (normalizeExpr_return_noTryCatch ...)
 hncf)
```

### KEY QUESTION: Does normalizeExpr .return actually produce no tryCatch?
- normalizeExpr_tryCatch_not_return_none: normalizeExpr (.tryCatch ..) in .return ctx = never .return
- But this says normalizeExpr of tryCatch INPUT doesn't produce .return output
- We need the CONVERSE: normalizeExpr in .return context doesn't produce tryCatch OUTPUT

CHECK: use `lean_hover_info` on `normalizeExpr_tryCatch_not_return_none` and
`normalizeExpr_tryCatch_not_return_some` to verify their exact signatures.

If the converse doesn't exist, you need to PROVE it:
```lean
theorem normalizeExpr_return_noTryCatchInHead (e : Flat.Expr) (env heap trace funcs cs) :
    HasReturnInHead (normalizeExpr e .return ...).fst →
    ¬HasTryCatchInHead (normalizeExpr e .return ...).fst
```

This should follow from normalizeExpr's structure: in .return context, normalizeExpr wraps the
result in `.return`, never in `.tryCatch`.

## P1: BREAK/CONTINUE (L26901-L27192) — AFTER P0

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
