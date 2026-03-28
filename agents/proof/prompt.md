# proof — THROW/RETURN/AWAIT + EXPAND WILDCARDS

## CURRENT STATE: 17 ANF sorries. Target: ≤12 this run (-5).

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## PRIORITY 0: EXPAND `| _ => sorry` AT L1597, L1663, L1680 (-3 → ~0 net after exfalso)

These 3 remaining wildcards cover bindComplex + compound cases. You already proved this pattern dozens of times in the return-some/yield-some blocks above. Apply the EXACT same expansion:

**L1597** (return-some/labeled, after proved cases): Replace `| _ => sorry` with:
```lean
      | call _ _ _ | newObj _ _ _ | getProp _ _ | setProp _ _ _ | getIndex _ _ | setIndex _ _ _ | deleteProp _ _ | typeof _ | getEnv _ _ | makeEnv _ | makeClosure _ _ | unary _ _ | binary _ _ _ | assign _ _ | «throw» _ | «await» _ =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [ANF.bindComplex, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
        repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
      | «let» _ _ _ | seq _ _ | «if» _ _ _ => sorry -- compound: needs induction
      | objectLit _ | arrayLit _ => sorry -- list-based
      | forIn | forOf | functionDef _ _ _ _ _ => sorry -- unsupported
```
**L1663**: Same expansion (inside yield-some/labeled).
**L1680**: Same expansion but for general `k`.

Net effect: 3 sorry → many exfalso (closed) + ~5 sorry each = ~12 new sorry lines BUT covering only compound/list/unsupported cases. Most are genuinely unreachable via exfalso.

## PRIORITY 1: THROW (L1774) — CONCRETE GOAL ANALYSIS

The goal at L1774 (I checked with lean_goal):
```
case throw
arg : ANF.Trivial
hsa : sa.expr = ANF.Expr.throw arg
hnorm : StateT.run (ANF.normalizeExpr sf.expr k) n = Except.ok (sa.expr, m)
hstep_eq : ANF.step? sa = some (ev, sa')
⊢ ∃ sf' evs, Flat.Steps sf evs sf' ∧ observableTrace [ev] = observableTrace evs ∧ ANF_SimRel s t sa' sf' ∧ ExprWellFormed sf'.expr sf'.env
```

ANF.step? on throw (ANF/Semantics.lean:376-383):
- Calls `evalTrivial s.env arg`
- If ok _: produces `(.error "throw", pushTrace {...} (.error "throw"))`
- If error msg: produces `(.error msg, pushTrace {...} (.error msg))`

Key lemma: `normalizeExpr_throw'` says `normalizeExpr (.throw flat_arg) k = normalizeExpr flat_arg (fun argTriv => pure (.throw argTriv))`.

Strategy:
```lean
  | throw arg =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    -- Case split on evalTrivial
    cases heval : ANF.evalTrivial sa_env arg <;> simp [heval] at hstep_eq
    all_goals (obtain ⟨rfl, rfl⟩ := hstep_eq)
    -- Now need: what is sf.expr? Use hnorm to determine it must be .throw flat_arg
    -- Then show Flat.step? on .throw flat_arg produces matching step
    sorry -- fill after examining unfolded goal
```

Use `lean_goal` after the `cases heval` to see the exact remaining goal, then match Flat.step?.

## PRIORITY 2: RETURN (L1778) — cases on `arg : Option ANF.Trivial`

```lean
  | «return» arg =>
    cases arg with
    | none =>
      -- ANF.step? on return none: just pushTrace with .return event
      obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
      simp only [] at hsa; subst hsa
      simp only [ANF.step?, ANF.pushTrace] at hstep_eq
      obtain ⟨rfl, rfl⟩ := hstep_eq
      -- normalizeExpr (.return none) k = ... use normalizeExpr_return' or unfold
      sorry -- fill after lean_goal
    | some val =>
      sorry -- similar to throw but with return event
```

## PRIORITY 3: AWAIT (L1782) — same bindComplex pattern as throw

## SKIP: L1760 (let), L1762 (seq), L1764 (if) — hardest, skip unless P0-P2 done
## SKIP: L1806 (break), L1808 (continue) — semantic mismatch, permanent sorry

## WORKFLOW
1. Expand L1597, L1663, L1680 → build after each
2. `lean_goal` at L1774 after subst+simp → write throw proof → build
3. `lean_goal` at L1778 → write return proof → build
4. Log progress to agents/proof/log.md
