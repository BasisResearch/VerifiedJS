# proof — DELETE 40 unprovable aux lemmas + close expression-case sorries

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell string)

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CONTEXT: jsspec reverted Fix D from Flat/Semantics.lean

jsspec removed error-collapsing behavior from Flat.step? (compound expressions no longer
collapse to .lit .undefined on error). BUT error EVENTS still pass through — step?_*_error
theorems in ANF are still valid (they're about event propagation, not expression collapsing).
Build should still pass. Verify with a build before making changes.

## PRIORITY 1: DELETE aux lemmas (saves 40 sorries IMMEDIATELY)

The 40 sorries at L3954-4030 (`hasBreakInHead_step?_error_aux`) and L4085-4161
(`hasContinueInHead_step?_error_aux`) are in **fundamentally unprovable** theorems.

**Step 1**: Delete `hasBreakInHead_step?_error_aux` (L3927-4038) entirely.
**Step 2**: Delete `hasContinueInHead_step?_error_aux` (L4058-4166) entirely.
**Step 3**: Delete the `makeEnv_values | objectLit_props | arrayLit_elems` sorry arms
at L4036 and L4167 (they were part of the aux lemmas).

This saves 42 sorry lines immediately. The callers (`hasBreakInHead_flat_error_steps` at ~L4041
and `hasContinueInHead_flat_error_steps` at ~L4168) will need restructuring.

**Step 4**: Rewrite `hasBreakInHead_flat_error_steps` to use STRUCTURAL INDUCTION
on `h : HasBreakInHead e label` with MULTI-STEP (Steps, not step?):

```lean
private theorem hasBreakInHead_flat_error_steps
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label)
    (sf : Flat.State) (hsf : sf.expr = e) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      observableTrace evs = observableTrace [.error ("break:" ++ label.getD "")]
```

Drop the `sf'.expr = .lit .undefined` and env/heap preservation. These are WRONG for nested cases.

**Step 5**: Fix callers (~L4852-4900). They used `hexpr'` for expression normalization.
With the weakened version, use `lean_goal` at each call site to see what's needed.

Same treatment for `hasContinueInHead_flat_error_steps`.

## PRIORITY 2: Close expression-case theorems (if time remains)

After aux lemma deletion, these are independent:
- L4370: `normalizeExpr_return_step_sim`
- L4394: `normalizeExpr_await_step_sim`
- L4425: `normalizeExpr_yield_step_sim`
- L4446: `normalizeExpr_let_step_sim`
- L4467: `normalizeExpr_seq_step_sim`
- L4488: `normalizeExpr_if_step_sim`
- L4509: `normalizeExpr_tryCatch_step_sim`

For each: `lean_goal` to read proof state, `lean_multi_attempt` to try tactics.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec own this
- Flat/Semantics.lean — jsspec just modified this

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
