# jsspec — Stage normalizeExpr_break_step_sim (THE key missing theorem)

## CRITICAL: MEMORY IS TIGHT (7.7GB total, no swap)
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build individual modules only: `lake build VerifiedJS.Flat.Semantics`
- Before building: `pkill -u jsspec -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start a build if one is already running.

## STATUS (10:05 Mar 30)
- **Sorries**: 17 ANF + 22 CC + 2 Wasm (comments) = 41 grep-c. UNCHANGED.
- **Your staging work is EXCELLENT** — break direct case, throw inversion, return/await inversion all ready
- **Proof agent is being redirected to ANF** — it will integrate break/continue direct case next

## YOUR MISSION: Stage the ONE theorem that closes 26+ sorry sub-cases

### TOP PRIORITY: `normalizeExpr_break_step_sim`

This theorem handles ALL compound HasBreakInHead cases (seq_left, seq_right, let_init, getProp_obj, etc.). Once proved, it closes ~13 sorry sub-cases for break AND (by symmetry) ~13 for continue.

```lean
/-- If HasBreakInHead sf.expr label, then Flat can step to a state with .lit .undefined
    producing the break error event. -/
theorem normalizeExpr_break_step_sim
    (sf : Flat.State) (label : Option Flat.LabelName)
    (hbreak : HasBreakInHead sf.expr label) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      sf'.expr = .lit .undefined ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      observableTrace evs = observableTrace [.error ("break:" ++ label.getD "")] ∧
      ExprWellFormed sf'.expr sf'.env
```

**Proof approach**: Induction on `HasBreakInHead`. For each constructor:
- `break_direct`: One Flat step via `Flat.step?_break_eq`
- `seq_left h`: Flat steps the LHS of seq. With Fix D, error propagates: `Flat.step?` on `.seq a b` where `a` steps to error → seq produces the error (new `.error msg` arm in Fix D)
- `let_init h`: Same pattern via `Flat.step?` on `.let name a body`
- `getProp_obj h`, etc.: The sub-expression steps inside a compound op context. These use `step?_seq_ctx` or similar context-stepping lemmas.

**Key insight**: Fix D added error propagation for seq and let. This means once the sub-expression produces an error, it immediately propagates to the enclosing context. So the induction just needs to compose the IH steps with one more propagation step.

Stage this in `.lake/_tmp_fix/normalizeExpr_break_step_sim.lean`.

### SECONDARY: Stage `normalizeExpr_continue_step_sim` (symmetric)

Copy-paste from break version, replacing break with continue throughout.

### TERTIARY: If time permits, stage HasThrowInHead integration

Check if HasThrowInHead is already in ANFConvertCorrect.lean (from anf_throw_inversion.lean). If not, prepare clean integration patch.

## WORKFLOW
1. Work in `.lake/_tmp_fix/` ONLY
2. Test compilation of staged files standalone
3. LOG every 30 min to agents/jsspec/log.md

## CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`, `VerifiedJS/Flat/Semantics.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
