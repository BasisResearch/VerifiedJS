# proof — GENERALIZE hk IN normalizeExpr_labeled_step_sim

## CURRENT STATE: 17 ANF sorries (7 in labeled_step_sim, 10 in anfConvert_step_star). 20 CC grep / 18 actual.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## THE BLOCKER YOU HIT

The depth induction restructuring is done — `ih` is in scope. But you CAN'T apply `ih` for nested return-some/yield-some (L1617, L1621, L1683, L1687) because:

- `ih` requires `hk : ∀ arg n', ∃ m', (k arg).run n' = .ok (.trivial arg, m')`
- The inner continuation is `fun t => pure (.return (some t))` which produces `.return`, not `.trivial`

## PRIORITY 0: Generalize `hk` to `hk_not_labeled`

Replace the `hk` hypothesis in `normalizeExpr_labeled_step_sim` with a weaker one:

```lean
(hk : ∀ (arg : ANF.Trivial) (n' m' : Nat) (l : String) (b : ANF.Expr),
    (k arg).run n' ≠ .ok (.labeled l b, m'))
```

This says "k never produces .labeled" instead of "k always produces .trivial". This is WEAKER so the IH hypothesis is EASIER to satisfy:

- `fun t => pure (.return (some t))` satisfies `hk_not_labeled` because `.return _ ≠ .labeled _ _` (noConfusion)
- `fun t => pure (.yield (some t) delegate)` satisfies `hk_not_labeled` for the same reason
- The original `hk_triv` hypothesis at the call site (L1834) implies `hk_not_labeled` because `.trivial _ ≠ .labeled _ _`

### Steps:
1. Change the hypothesis name and type in the theorem signature
2. Update the `| labeled l b_flat =>` case (L1474 area): currently uses `hk` to get `(k arg).run n' = .ok (.trivial arg, m')`. With the weaker hypothesis, you need to show `.labeled` is impossible via `hk_not_labeled`, then handle other constructors. Check if the existing proof already only uses the "not labeled" direction.
3. Verify all other proved cases still type-check (var, this, lit, break, continue, return-none, yield-none, while_, tryCatch should only need "k result ≠ .labeled")
4. Update the call site at L1834: pass a proof that `hk_triv` implies `hk_not_labeled`

### For the call site conversion:
```lean
have hk_nl : ∀ (arg : ANF.Trivial) (n' m' : Nat) (l : String) (b : ANF.Expr),
    (k arg).run n' ≠ .ok (.labeled l b, m') := by
  intro arg n' m' l b h
  obtain ⟨m'', hm''⟩ := hk_triv arg n'
  rw [hm''] at h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
```

### After generalization, close L1617 (nested return-some in return context):
```lean
| some inner =>
  -- inner : Flat.Expr, context: e = .return (some inner)
  -- Apply ih on inner (depth inner < depth (.return (some inner)) = succ d)
  have hd_inner : inner.depth ≤ d := by
    simp [Flat.Expr.depth] at hd; omega
  have hk_inner : ∀ (arg : ANF.Trivial) (n' m' : Nat) (l : String) (b : ANF.Expr),
      (fun t => pure (.return (some t) : ANF.Expr)).run n' ≠ .ok (.labeled l b, m') := by
    intro arg n' m' l b h
    simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
  exact ih d (Nat.le_refl d) inner hd_inner (fun t => pure (.return (some t))) n m label body hk_inner hnorm sf rfl hewf
```

(Adjust the `ih` application to match actual parameter order after generalization.)

## PRIORITY 1: LowerCorrect.lean — use step_sim_stutter

**IMPORTANT DISCOVERY**: `step_sim` (L6631 in Wasm/Semantics.lean) is 1:1 (single IR step). Many cases (return-some, let, seq, if, etc.) need 1:N steps. The 12 Wasm sorries in step_sim are structurally unprovable as 1:1.

`step_sim_stutter` (L7370) already handles return-some. The catch-all delegates to step_sim for other cases.

**Fix**: Refactor `lower_sim_steps` in LowerCorrect.lean (L47-61) to use `step_sim_stutter` instead of `step_sim`. Change:

```lean
-- OLD (L58):
obtain ⟨ir₂, hirStep, hrel₂⟩ := IR.LowerSimRel.step_sim s t _ _ _ _ hrel hmapped

-- NEW:
obtain ⟨ir₂, ir_trace₂, hirSteps₂, hrel₂, hobs₂⟩ := IR.LowerSimRel.step_sim_stutter s t _ _ _ _ hrel hmapped
```

You'll also need to adjust the trace composition at L61 to concatenate `ir_trace₂` with the recursive result instead of using `.tail (.mk hirStep)`. And the conclusion's trace needs to change from `traceListFromCore` (which maps 1:1) to an observable-events formulation.

This is a BIGGER refactor — it requires changing the conclusion of `lower_sim_steps` and `lower_behavioral_correct` to use observable events. Only do this if P0 goes smoothly.

## WORKFLOW
1. Generalize hk → build → fix any breakage
2. Apply IH for L1617, L1621, L1683, L1687 → build
3. If time: attempt LowerCorrect.lean refactor
4. Log to agents/proof/log.md
