# proof — EXPAND WILDCARD SORRIES INTO PER-CONSTRUCTOR CASES

## CURRENT STATE: 13 ANF sorries. Target: ≤8 this run (-5).

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## PRIORITY 0: INTEGRATE STAGING LEMMAS INTO Convert.lean — YOU HAVE NOT DONE THIS YET

**YOU own Convert.lean** (proof user). jsspec CANNOT write to it.

1. Read `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean`
2. Read `VerifiedJS/ANF/Convert.lean` and find `end VerifiedJS.ANF`
3. Copy ALL lemmas from ConvertHelpers.lean into Convert.lean BEFORE `end VerifiedJS.ANF`
4. Build: `lake build VerifiedJS.ANF.Convert`
5. Fix any issues

## PRIORITY 1: EXPAND `| _ => sorry` AT L1563 AND L1595 (EASIEST -2 WINS)

L1563 and L1595 are `| _ => sorry` in return-some/yield-some labeled cases. They match ~30 Flat.Expr constructors. The `| _` hides easy cases. EXPAND into individual constructors and close the trivial ones:

**For L1563 (return-some, non-labeled val):**

Replace `| _ => sorry -- non-labeled sub-expression: requires induction on val depth` with per-constructor cases. I have verified the goals. Here are the EXACT tactics:

### Trivial cases (exfalso — normalizeExpr calls k which returns .return, not .labeled):
```lean
      | var name =>
        exfalso
        simp only [ANF.normalizeExpr, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
        split at hnorm
        · simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        · simp at hnorm
      | lit _ =>
        exfalso
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
        exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | this =>
        exfalso
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
        exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
```

### bindComplex-based cases (exfalso — normalizeExpr produces .let, not .labeled):
For call, newObj, getProp, setProp, getIndex, setIndex, deleteProp, typeof, getEnv, makeEnv, makeClosure, unary, binary, assign:
```lean
      | call _ _ _ | newObj _ _ _ | getProp _ _ | setProp _ _ _ | getIndex _ _ | setIndex _ _ _ | deleteProp _ _ | typeof _ | getEnv _ _ | makeEnv _ | makeClosure _ _ | unary _ _ | binary _ _ _ | assign _ _ =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [ANF.bindComplex, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
        repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
```

### Already-proved pattern (copy from L1596-1611):
```lean
      | while_ _ _ =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
        repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm))
      | tryCatch _ _ _ _ =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
        cases ‹Option Flat.Expr› with
        | none => simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm; repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
        | some _ => simp only [Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm; repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
```

### Control flow (exfalso — break/continue/return/yield-none/await produce specific constructors, not labeled):
```lean
      | «break» _ | «continue» _ =>
        exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
        exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | «return» arg =>
        cases arg with
        | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        | some _ => sorry -- nested return-some: recursive, leave for now
      | yield arg delegate =>
        cases arg with
        | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        | some _ => sorry -- nested yield-some: recursive, leave for now
      | «throw» _ | «await» _ =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [ANF.bindComplex, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
        repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
```

### Hard cases (leave as sorry):
```lean
      | «let» _ _ _ | seq _ _ | «if» _ _ _ => sorry -- compound: needs induction on depth
      | objectLit _ | arrayLit _ => sorry -- list-based bindComplex
      | forIn | forOf => sorry -- unsupported
      | functionDef _ _ _ _ _ => sorry -- unsupported
```

**For L1595**: Same pattern as L1563 (yield-some vs return-some). Copy the same expansion.

**This converts 1 sorry → many exfalso + ~8 small sorries. Net effect: proves 20+ sub-cases, leaves ~8 compound sorries.**

## PRIORITY 2: SAME EXPANSION FOR L1612

L1612 (`| _ => sorry` in normalizeExpr_labeled_step_sim) has the SAME pattern. The goals are identical shape. Expand with same tactic templates. Key differences:
- The continuation is `k` (general) instead of `fun t => pure (.return (some t))`
- For trivial cases (var/lit/this), use `hk` instead of no-confusion on `.return`
- For bindComplex cases, same exfalso pattern works

## PRIORITY 3: MAIN THEOREM (L1692-L1714) — ONLY IF TIME

- These need forward simulation (step the Flat side). Much harder. Skip if P1/P2 not done.

## SKIP: L1738 (break), L1740 (continue) — semantic mismatch, permanent sorry

## WORKFLOW
1. Integrate staging lemmas → build
2. Expand L1563 → build → fix
3. Copy for L1595 → build → fix
4. Expand L1612 → build → fix
5. Log progress to agents/proof/log.md
