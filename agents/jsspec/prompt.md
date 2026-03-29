# jsspec — MOVE STAGING INTO MAIN CODEBASE + BREAK SIM HELPER

## STATUS: 63 grep sorries. Your labeled + break inversion is COMPLETE and VERIFIED. OUTSTANDING WORK.

## THE PROBLEM: Your infrastructure is sitting in `.lake/_tmp_fix/` where it can't be used.

The proof agent needs your theorems in the ACTUAL build. They can't import from `.lake/_tmp_fix/`.

## PRIORITY 0: Create importable inversion module

Create a new file: `VerifiedJS/Proofs/ANFInversion.lean`

Copy from your staging files:
1. From `anf_break_inversion.lean`:
   - `HasBreakInHead` / `HasBreakInHeadList` / `HasBreakInHeadProps` mutual inductive
   - `normalizeExprList_break_or_k`
   - `normalizeProps_break_or_k`
   - `normalizeExpr_break_or_k`
   - `normalizeExpr_break_implies_hasBreakInHead`
   - `bindComplex_never_break_general`

2. From `anf_labeled_inversion.lean`:
   - `HasLabeledInHead` / `HasLabeledInHeadList` / `HasLabeledInHeadProps` mutual inductive
   - `normalizeExprList_labeled_or_k`
   - `normalizeProps_labeled_or_k`
   - `normalizeExpr_labeled_or_k`
   - `normalizeExpr_labeled_implies_hasLabeledInHead`
   - `normalizeExpr_not_labeled_of_no_head_no_k`

3. From `anf_break_sim.lean`:
   - `Flat.step?_break_is_some`
   - `Flat.step?_continue_is_some`
   - `ANF.normalizeExpr_break_run`
   - `ANF.normalizeExpr_continue_run`

Add `import VerifiedJS.Proofs.ANFInversion` to `ANFConvertCorrect.lean`.

**VERIFY THE BUILD**: `lake build VerifiedJS.Proofs.ANFConvertCorrect` must still pass.

## PRIORITY 1: Write `normalizeExpr_break_step_sim` for the BASE case

Your analysis in `anf_break_sim.lean` showed the base case works (sf.expr = .break label directly).
Write the complete proof for this case:

```lean
theorem normalizeExpr_break_base_step_sim
    (sf : Flat.State) (label : String)
    (hsf_expr : sf.expr = .break label) :
    ∃ sf', Flat.step? sf = some (.error ("break:" ++ label), sf') ∧
      sf'.expr = .lit .undefined := by
  rw [hsf_expr]; simp [Flat.step?]
```

Then show: when `normalizeExpr sf.expr k = .break label` and `k` is trivial-preserving,
by `normalizeExpr_break_implies_hasBreakInHead`, `HasBreakInHead sf.expr label`.
Case-split on HasBreakInHead to get the structure, then construct Flat multi-steps.

The general case (break inside compound expression) IS harder due to dead code.
For now, at minimum prove the `.break label` direct case.

## PRIORITY 2: Continue inversion (same pattern as break/labeled)

Write `normalizeExpr_continue_or_k` and `normalizeExpr_continue_implies_hasContinueInHead`.
This mirrors break exactly.

## FILES: `VerifiedJS/Proofs/ANFInversion.lean` (NEW — create this), `.lake/_tmp_fix/` (read), `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`
## DO NOT EDIT: `VerifiedJS/Proofs/ClosureConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md
