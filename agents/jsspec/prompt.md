# jsspec — Close compound HasBreakInHead sub-cases via step_sim theorems

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build individual modules: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -u jsspec -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (11:05 Mar 30)
- **Sorries**: 17 ANF + 23 CC + 2 Wasm (comments) = 42 grep-c
- **Your break_step_sim staging is good** — proof agent will integrate break/continue direct case
- **After integration**: break/continue will decompose into ~28 compound sub-case sorries

## YOUR MISSION: Make the compound sub-cases closeable

### TOP PRIORITY: Verify and complete normalizeExpr_break_step_sim

Your staging file `.lake/_tmp_fix/anf_break_step_sim.lean` has the theorem structure. The compound cases (seq_left, seq_right, let_init, getProp_obj, etc.) each need:

1. **IH**: The inner sub-expression steps (from HasBreakInHead IH)
2. **Context step**: The enclosing expression (seq/let/etc.) propagates the step
3. **Error propagation (Fix D)**: When sub-expression produces error, enclosing context propagates it

The KEY lemma for each compound case is a context-stepping lemma:
- `Flat.step?_seq_ctx`: if `step? a = some (ev, a')` then `step? (seq a b) = some (ev, seq a' b)` (or error propagation)
- `Flat.step?_let_ctx`: similar for let
- `Flat.step?_getProp_obj_ctx`: similar for getProp

**Check if these context-stepping lemmas exist** in Flat/Semantics.lean. If they do, the compound cases are straightforward. If not, stage them.

```bash
grep -n "step?_seq_ctx\|step?_let_ctx\|step?_getProp" VerifiedJS/Flat/Semantics.lean | head -20
```

### SECONDARY: Stage normalizeExpr_throw_step_sim

Same pattern as break_step_sim but for HasThrowInHead. The throw case (L3396) has `all_goals sorry` covering 2 sub-cases. A throw_step_sim would close them.

### TERTIARY: Stage return/yield/await step_sim

Check `.lake/_tmp_fix/anf_return_await_inversion.lean` — if HasReturnInHead etc. are defined, write the corresponding step_sim theorems.

## WORKFLOW
1. Work in `.lake/_tmp_fix/` ONLY
2. Test that staged theorems type-check standalone if possible
3. LOG every 30 min to agents/jsspec/log.md

## CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`, `VerifiedJS/Flat/Semantics.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
