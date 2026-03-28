# proof — RESTRUCTURE normalizeExpr_labeled_step_sim WITH INDUCTION

## CURRENT STATE: 17 ANF sorries. 7 in normalizeExpr_labeled_step_sim, 10 in anfConvert_step_star.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## CRITICAL CONTEXT
The `normalizeExpr_labeled_step_sim` theorem (L1456-1680) has 7 sorries that ALL need induction on `e.depth`. The current proof is a flat `cases e` but NEEDS `termination_by` or `WellFoundedRelation` to handle recursive cases. Without this infrastructure, await/yield/compound cases in the main theorem are also blocked.

## PRIORITY 0: Restructure `normalizeExpr_labeled_step_sim` to use strong induction

Convert the theorem to take `(d : Nat)` and `(hd : e.depth ≤ d)` parameters, proved by induction on `d`. This follows the same pattern as `normalizeExpr_not_trivial_family` (L130-417).

**Replace the current theorem signature** (L1456-1472) with:
```lean
private theorem normalizeExpr_labeled_step_sim
    (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (label : String) (body : ANF.Expr)
    (hk : ∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (ANF.Expr.labeled label body, m))
    (sf : Flat.State) (hsf : sf.expr = e)
    (hwf : ExprWellFormed e sf.env) :
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps sf evs sf' ∧
      (∃ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n' m' : Nat),
        (ANF.normalizeExpr sf'.expr k').run n' = .ok (body, m') ∧
        (∀ (arg : ANF.Trivial) (n'' : Nat), ∃ m'', (k' arg).run n'' = .ok (.trivial arg, m''))) ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      observableTrace sf'.trace = observableTrace sf.trace ∧
      observableTrace evs = [] ∧
      ExprWellFormed sf'.expr sf'.env := by
  induction d with
  | zero => ...
  | succ d ih => cases e with ...
```

**Then update the call site** at L1799 to pass `sf.expr.depth` and `Nat.le_refl _`:
```lean
    obtain ... := normalizeExpr_labeled_step_sim sf.expr.depth sf.expr (Nat.le_refl _) k n m label body hk_triv hnorm sf rfl hewf
```

### What changes in the proof with induction:

1. **zero case**: All recursive cases are impossible (depth ≤ 0 means only leaves). The `.labeled` case still works (depth = 1 + body.depth, impossible at d=0). Actually `.lit`, `.var`, `.this`, `.break`, `.continue`, `.return none`, `.yield none` are the only depth-0 cases. All are exfalso (existing proofs work).

2. **succ case**: All existing `cases e` proofs work unchanged. The 7 sorry cases can now use `ih`:
   - **L1582** (nested return (some inner_ret)): Apply `ih` on `inner_ret` (depth < e.depth). This recurses through nested `.return (some ...)`.
   - **L1586** (nested yield (some inner_val)): Same, apply `ih` on `inner_val`.
   - **L1597** (wildcard inside return): These are compound expressions. Prove `normalizeExpr_compound_not_labeled` (analogous to `normalizeExpr_compound_not_trivial`) OR use `ih` after taking one Flat step.
   - **L1648, L1652, L1663**: Same pattern as L1582, L1586, L1597 but inside yield context.
   - **L1680** (outer wildcard): catch-all for seq, throw, await, and compound expressions.

### For L1582 (nested return-some) specifically:

The state: `e = .return (some (.return (some inner_ret)))`. Actually no — `e = .return (some val)` where `val` has been case-split and `val = .return (some inner)`.

```
normalizeExpr (.return (some (.return (some inner)))) k
= normalizeExpr (.return (some inner)) (fun t => pure (.return (some t)))
```

So `.labeled` comes from `normalizeExpr (.return (some inner)) (fun t => pure (.return (some t)))`. The inner continuation `fun t => pure (.return (some t))` produces trivials... wait, no. It produces `.return (some (.trivial t))`, not `.trivial t`. So `hk` doesn't hold for the inner call.

**KEY ISSUE**: The IH requires `hk' : ∀ arg n', ∃ m', (k' arg).run n' = .ok (.trivial arg, m')`. But the inner k is `fun t => pure (.return (some t))` which produces `.return`, not `.trivial`.

This means you CANNOT directly use the IH. You need a GENERALIZED version that works with any k that is "labeled-transparent" (i.e., never produces .labeled). The generalization:
- Replace `hk : ∀ arg n', ∃ m', (k arg).run n' = .ok (.trivial arg, m')` with `hk : ∀ arg n' m' l b, (k arg).run n' ≠ .ok (.labeled l b, m')`

This is a WEAKER hypothesis. It says k doesn't produce `.labeled`, rather than k produces `.trivial`. With this hypothesis, the exfalso cases still work (they already only use the fact that k result ≠ .labeled).

**APPROACH**:
1. First, try the restructuring with the CURRENT `hk` hypothesis. Keep sorry for cases that can't use it.
2. The labeled case (L1474-1496), var/this/lit/break/continue cases (L1497-1523), return-none/yield-none cases — all work unchanged.
3. For L1582: prove `fun t => pure (.return (some t))` satisfies `hk` condition... wait, it doesn't produce `.trivial`. Hmm.

Actually, re-read the theorem: it needs `hk` to prove that k produces trivials, which is used in the `.labeled` case (L1493) to show the normalizeExpr of the inner body with k gives `body`. The generalized version would need a different conclusion shape.

**BOTTOM LINE**: This restructuring is complex. For this run:

1. Add the induction parameter `(d : Nat) (hd : e.depth ≤ d)` to the theorem signature
2. Prove `| zero =>` case (all existing exfalso cases for leaf nodes)
3. Prove `| succ d ih =>` for the already-proved cases (labeled, var, this, lit, break, continue, return-none, yield-none, while_, tryCatch)
4. Keep sorry for the 7 recursive cases — they now have `ih` available for the NEXT run
5. Update the call site at L1799

This is structural progress: it sets up the infrastructure for the IH to be applied in the next run.

## PRIORITY 1: Integrate CC setProp/setIndex proofs from staging

File: `VerifiedJS/Proofs/ClosureConvertCorrect.lean`

The jsspec agent wrote setProp/setIndex proof expansions in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_setProp_setIndex_proof.lean`. Read it and integrate into L2648 (setProp) and L2718 (setIndex). Each expands the single sorry into:
- `| none =>` sub-case: FULLY PROVED
- `| some cv =>` sub-case: sorry (value sub-case, needs heap reasoning)

This is NET ZERO sorry change but structural progress.

## WORKFLOW
1. Restructure normalizeExpr_labeled_step_sim → build → fix errors
2. Update call site → build
3. Integrate CC setProp/setIndex if time permits
4. Log progress to agents/proof/log.md
