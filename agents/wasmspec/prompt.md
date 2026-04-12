# wasmspec — COMPLETE EvalFirst INFRASTRUCTURE + SWAP IN

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T06:05
- Total: **42 real sorries** (ANF 30, CC 12). Down from 43 (-1).
- HasNonCallFrameTryCatchInEvalFirst: DEFINED ✓
- normalizeExpr_return_implies_noEvalFirstTryCatch: PROVED ✓
- Next: complete the EvalFirst chain and swap it in at L18100

## P0: COMPLETE THE EvalFirst CHAIN — HIGHEST PRIORITY (-1 sorry)

You've defined the predicate and proved the key enabler. Now finish:

### Step 1: step_nonError_preserves_noEvalFirstTryCatch
Prove: if ¬HasNonCallFrameTryCatchInEvalFirst e and step? doesn't produce error,
then ¬HasNonCallFrameTryCatchInEvalFirst e' for the result.
This is a case analysis on step? — each non-error case either:
- Reduces to a sub-expression that also has no eval-first tryCatch
- Produces a .lit (stuck)

### Step 2: HasReturnInHead_implies_noEvalFirstTryCatch (or equivalent)
Show: normalizeExpr output with HasReturnInHead has no eval-first non-call-frame tryCatch.
You already proved normalizeExpr_return_implies_noEvalFirstTryCatch — check if this IS that.

### Step 3: SWAP IN at L18100
Replace `sorry /- ¬HasNonCallFrameTryCatchInHead` with the EvalFirst-based proof:
- Use normalizeExpr output → ¬HasNonCallFrameTryCatchInEvalFirst
- Use step preservation to maintain it across Steps
- Use the EvalFirst version where the old predicate was needed

### Expected: -1 sorry (L18100 closed)

## P1: BREAK/CONTINUE COMPOUND (L26891, L26962) — if P0 done

Check if `HasBreakInHead_step_nonError` and `HasContinueInHead_step_nonError` exist.
If not, define them following the EXACT pattern of HasThrowInHead_step_nonError.
These would enable closing L26891 and L26962.

## P2: catchParam (L26671) — if P1 done

Thread noCallFrameReturn as precondition. Check caller scope.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — EvalFirst chain completion" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
