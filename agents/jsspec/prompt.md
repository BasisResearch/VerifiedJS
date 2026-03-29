# jsspec — CREATE ANFInversion.lean (STILL NOT DONE)

## STATUS: 62 grep sorries. Your staging inversion proofs are COMPLETE but STILL STUCK in `.lake/_tmp_fix/`.

## This is the 3rd consecutive run where integration hasn't happened. The proof agent CANNOT use your work.

## PRIORITY 0: Create `VerifiedJS/Proofs/ANFInversion.lean`

This is the ONLY thing that matters this run. Do it NOW:

1. Create `VerifiedJS/Proofs/ANFInversion.lean`
2. Add the correct module header and imports (match what ANFConvertCorrect.lean imports)
3. Copy from `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`:
   - `HasBreakInHead` / `HasBreakInHeadList` / `HasBreakInHeadProps` mutual inductive
   - `normalizeExprList_break_or_k`, `normalizeProps_break_or_k`, `normalizeExpr_break_or_k`
   - `normalizeExpr_break_implies_hasBreakInHead`
   - `bindComplex_never_break_general`
4. Copy from `.lake/_tmp_fix/VerifiedJS/Proofs/anf_labeled_inversion.lean`:
   - `HasLabeledInHead` / `HasLabeledInHeadList` / `HasLabeledInHeadProps` mutual inductive
   - `normalizeExprList_labeled_or_k`, `normalizeProps_labeled_or_k`, `normalizeExpr_labeled_or_k`
   - `normalizeExpr_labeled_implies_hasLabeledInHead`
5. Build: `lake build VerifiedJS.Proofs.ANFInversion`
6. If it fails, fix imports until it builds.

## PRIORITY 1: Write break/continue step_sim helpers

From `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_sim.lean`:
- `Flat.step?_break_is_some`
- `Flat.step?_continue_is_some`
- `ANF.normalizeExpr_break_run`
- `ANF.normalizeExpr_continue_run`

Add these to ANFInversion.lean.

## PRIORITY 2: Continue inversion (mirrors break exactly)

Write `HasContinueInHead` and `normalizeExpr_continue_implies_hasContinueInHead`.

## FILES: `VerifiedJS/Proofs/ANFInversion.lean` (NEW — create this), `.lake/_tmp_fix/` (read)
## DO NOT EDIT: `VerifiedJS/Proofs/ClosureConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md
