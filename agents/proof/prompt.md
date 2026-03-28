# proof — FINISH WILDCARD EXPANSION + START MAIN THEOREM

## CURRENT STATE: 17 ANF sorries. Target: ≤12 this run (-5).

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## GOOD NEWS: P0 DONE (staging lemmas integrated), P1 PARTIAL (expanded L1563/L1595 successfully!)

You proved 80+ sub-cases via exfalso in the return-some/yield-some labeled cases. Excellent.

## PRIORITY 0: EXPAND REMAINING `| _ => sorry` AT L1597, L1663, L1680 (EASY -3)

These 3 wildcards STILL cover bindComplex cases that are trivially exfalso. You already proved the pattern — just apply it here too.

**L1597** (inside return-some/labeled, after the proved cases): Replace `| _ => sorry` with:

```lean
      -- bindComplex cases: normalizeExpr produces .let, not .labeled
      | call _ _ _ | newObj _ _ _ | getProp _ _ | setProp _ _ _ | getIndex _ _ | setIndex _ _ _ | deleteProp _ _ | typeof _ | getEnv _ _ | makeEnv _ | makeClosure _ _ | unary _ _ | binary _ _ _ | assign _ _ | «throw» _ | «await» _ =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [ANF.bindComplex, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
        repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
      -- compound cases: need induction (leave sorry)
      | «let» _ _ _ | seq _ _ | «if» _ _ _ => sorry -- compound: needs induction
      | objectLit _ | arrayLit _ => sorry -- list-based
      | forIn | forOf => sorry -- unsupported
      | functionDef _ _ _ _ _ => sorry -- unsupported
```

**L1663**: Same pattern (inside yield-some/labeled). Copy the same expansion.

**L1680** (normalizeExpr_labeled_step_sim, general k): Same pattern but add throw/await to bindComplex group.

This converts 3 sorry → ~12 exfalso + ~5 sorry each = ~15 sorry per location, netting to ~12 total small sorries. But most are CLOSED, leaving only compound/list/unsupported.

## PRIORITY 1: MAIN THEOREM — throw (L1774), return (L1778), await (L1782)

These 3 main theorem cases are simpler than let/seq/if. Pattern:

**throw (L1774)**: ANF step evaluates trivial arg and produces error event. Flat side: throw produces error.
```lean
  | throw arg =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    -- ANF normalizeExpr on throw uses bindComplex: produces .let with evalComplex
    -- ANF.step? evaluates the let, calls evalComplex on the arg
    -- Use lean_goal here to see exact goal, then match Flat.step? .throw
    sorry
```

Use `lean_goal` at L1774 to see the EXACT goal structure, then write the proof.

**return (L1778)**: Similar — evaluate optional arg, produce return event.
- `cases arg with | none => ... | some val => ...`
- For none: `simp [ANF.step?]` should close
- For some: need to show trivial evaluation matches

**await (L1782)**: Same bindComplex pattern as throw.

## PRIORITY 2: Main theorem let (L1760), seq (L1762), if (L1764)

These are the HARDEST cases — skip unless P0 and P1 are done.

## SKIP: L1806 (break), L1808 (continue) — semantic mismatch, permanent sorry

## WORKFLOW
1. Expand L1597 → build
2. Copy expansion for L1663 → build
3. Copy expansion for L1680 → build
4. Use lean_goal at L1774, L1778, L1782 → write proofs → build
5. Log progress to agents/proof/log.md
