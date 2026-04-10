# jsspec — CLOSE ERROR-CASE SORRIES + BUILD MULTI-STEP INFRASTRUCTURE

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- BUILD PASSES. LSP available.
- CC: 15 sorries. CCStateAgreeWeak assessed infeasible (good analysis, confirmed).
- Error propagation now extended to ALL compound cases in Flat/Semantics.lean (48 `.error _` patterns).
- Proof agent is fixing cascading ANF errors. CC error-case sorries (L5079, L5175, L5411) should now be closable or nearly closable.

## P0: CLOSE 3 ERROR-CASE SORRIES — DO THIS FIRST

The error propagation is now in Flat/Semantics.lean. With error events, `Flat.step?` on compound expressions (`.let`, `.assign`, `.seq`) now propagates `.error _` events by unwrapping the wrapper (setting `s'.expr = sa.expr` instead of wrapping in `.let`/`.assign`/`.seq`).

### L5079 (let compound error case)
After error propagation, when `t = .error msg`:
- `sf'.expr = sa.expr` (unwrapped, not `.let name sa.expr body`)
- `sf'.env = sa.env`, `sf'.heap = sa.heap`
- The Core step also produces an error event
- Need to show `convertExpr sf'.expr ... = convertExpr sa.expr ...`
- This should be provable since both sides are the same sub-expression

Check with `lean_goal` at L5079 to see the exact goal. Try:
```lean
simp_all [Flat.step?, Flat.pushTrace]
```
or unfold Flat.step? and use the `herr` hypothesis to simplify the error branch.

### L5175 (assign compound error case)
Same pattern as L5079 but for `.assign`.

### L5411 (seq compound error case)
Same pattern for `.seq`.

### APPROACH
1. Check diagnostics at each location to see if they compile now
2. Read the exact goal with `lean_goal`
3. If the goal is about `convertExpr` matching after error unwrap, use:
   - `unfold Flat.step?` + `split` on the error match
   - The error branch should give `s'.expr = sa.expr` directly
4. If still blocked, document exactly what's needed

## P1: MULTI-STEP SIMULATION LEMMAS (if P0 done or blocked)

3 sorries need multi-step simulation:
- **L4921**: `Flat .getEnv (.var envVar) idx` takes 2 steps (var lookup + getEnv eval)
- **L6062**: Core `newObj` allocates immediately, Flat needs multiple steps
- **L6071**: Same as L6062

These need helper lemmas proving that 2+ Flat steps simulate 1 Core step.

### For L4921 (getEnv multi-step):
Define a lemma:
```lean
theorem Flat_getEnv_two_steps (envVar : Flat.VarName) (idx : Nat)
    (env : Flat.Env) (heap : Core.Heap) ...
    (henv : env.lookup envVar = some envVal) :
    ∃ evs sf', Flat.Steps ⟨.getEnv (.var envVar) idx, env, heap, ...⟩ evs sf' ∧
    sf'.expr = ... ∧ ...
```
This factors out the 2-step sequence so the main proof can just `exact ⟨_, _, Flat_getEnv_two_steps ...⟩`.

### For L6062/L6071 (newObj multi-step):
Similar — prove that evaluating func/env args to values then allocating takes N flat steps matching 1 Core newObj.

## P2: FUNCSCORR INFRASTRUCTURE (if P0+P1 done)

L5851 and L7952 are blocked on FuncsCorr invariant. If time permits, define the `FuncsCorr` relation between Core and Flat function tables and prove basic properties.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — error-case + multi-step" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
