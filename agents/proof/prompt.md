# proof — Close ANF expression-case sorries

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell string)

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (16:05 Mar 30)
- ANF: 17 sorries, 3 groups:
  - 7 depth-induction (L3825-3923) — skip
  - 2 consolidated context (L4116, L4327) — skip (need multi-step restructure)
  - 8 expression-case (L4423, 4425, 4427, 4447, 4449, 4451, 4453, 4455) — YOUR TARGET
- Fix D is APPLIED in Flat/Semantics.lean ✓
- hnoerr guards applied in CC ✓

## PRIORITY 1: Close the `let` case (L4423)

Goal state at L4423 (supervisor read it):
```
case let
sa : ANF.State, sf : Flat.State, ev : Core.TraceEvent, sa' : ANF.State
hewf : ExprWellFormed sf.expr sf.env
hstep_eq : ANF.step? sa = some (ev, sa')
hheap : sa.heap = sf.heap, henv : sa.env = sf.env
htrace : observableTrace sa.trace = observableTrace sf.trace
k : ANF.Trivial → ANF.ConvM ANF.Expr
n m : Nat
hnorm : StateT.run (ANF.normalizeExpr sf.expr k) n = Except.ok (sa.expr, m)
hk_triv : ∀ arg n', ∃ m', StateT.run (k arg) n' = Except.ok (.trivial arg, m')
name : ANF.VarName, rhs : ANF.ComplexExpr, body : ANF.Expr
hsa : sa.expr = ANF.Expr.let name rhs body
⊢ ∃ sf' evs, Flat.Steps sf evs sf' ∧
    observableTrace [ev] = observableTrace evs ∧ ANF_SimRel s t sa' sf' ∧ ExprWellFormed sf'.expr sf'.env
```

Strategy:
1. `subst hsa` to substitute the expr form
2. `simp [ANF.step?]` on hstep_eq to unfold the let-stepping
3. ANF.step? on `.let name rhs body` evaluates `rhs` (ComplexExpr):
   - If rhs evaluates to a value: extends env, continues with body
   - If rhs steps: produces intermediate state
4. Use `lean_goal` after each tactic to see what remains
5. For the Flat side: `normalizeExpr` of `sf.expr` produced `.let name rhs body`,
   so `sf.expr` has a let in head position (possibly wrapped in seq/let chains)
6. Use normalizeExpr inversion lemma to decompose
7. Construct Flat.Steps matching the ANF step

Try `lean_multi_attempt` at L4423 with:
```
["subst hsa; simp [ANF.step?, ANF.evalComplex, ANF.pushTrace] at hstep_eq",
 "subst hsa; simp only [ANF.step?] at hstep_eq"]
```
Then continue from whatever state remains.

## PRIORITY 2: Close `seq` case (L4425) — similar to let

## PRIORITY 3: Close `if` case (L4427) — cond is trivial after ANF

## PRIORITY 4: Close `throw` case (L4447)
Already partially destructed (L4436-4447). Two subgoals remain after evalTrivial cases.
Use `lean_goal` at L4447 to see exact remaining state.

## DO NOT TOUCH:
- Depth-induction cases (L3825-3923)
- Consolidated context cases (L4116, L4327)
- ClosureConvertCorrect.lean — jsspec and wasmspec own this

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
