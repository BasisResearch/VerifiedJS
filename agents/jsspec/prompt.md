# jsspec — INTEGRATE STAGING LEMMAS + SEQ/IF SIMULATION HELPERS

## STATUS: You've written great lemmas in staging files. But NONE of them are in the actual proof files yet. The proof agent CANNOT USE staging lemmas.

## CRITICAL: YOUR STAGING LEMMAS MUST BE INTEGRATED

The proof agent's normalizeExpr_labeled_step_sim has 3 helper sorries because it needs no-confusion lemmas for compound cases. Your staging files have some of these but they're in `.lake/_tmp_fix/` which is NOT imported.

## PRIORITY 0: Write normalizeExpr compound no-confusion lemmas INTO `VerifiedJS/ANF/Convert.lean`

These lemmas prove that normalizeExpr of compound expressions (return some, yield some, let, seq, if, throw, await) cannot produce `.labeled`. They should go BEFORE `end VerifiedJS.ANF` in Convert.lean.

Pattern (all should be provable by `unfold normalizeExpr; simp [bind, StateT.bind, ...]; split; ...`):

```lean
theorem normalizeExpr_return_some_not_labeled (v : Flat.Expr) (k : Trivial → ConvM Expr)
    (n : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.return (some v)) k).run n ≠ .ok (.labeled label body, _) := by
  unfold normalizeExpr
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; split at h <;> simp [pure, Pure.pure, StateT.pure, Except.pure] at h
  <;> exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

theorem normalizeExpr_seq_not_labeled (a b : Flat.Expr) (k : Trivial → ConvM Expr)
    (n : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.seq a b) k).run n ≠ .ok (.labeled label body, _) := by
  unfold normalizeExpr
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; split at h <;> simp [pure, Pure.pure, StateT.pure, Except.pure] at h
  <;> exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
```

If this exact pattern doesn't work, use `lean_multi_attempt` at each to find what does.

## PRIORITY 1: Write seq simulation helper

The proof agent needs a helper like `normalizeExpr_var_step_sim` but for the seq case in anfConvert_step_star. The seq case is:

ANF.step? for `.seq a b`:
- If a steps: inner step on a, remain in seq
- If a is value: skip to b

normalizeExpr (.seq a b) k = `normalizeExpr a (fun _ => normalizeExpr b k)`

Helper needed:
```lean
/-- When ANF steps .seq a b by stepping a, Flat can simulate with steps on normalizeExpr a -/
private theorem normalizeExpr_seq_inner_step_sim
    (a b : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (result : ANF.Expr)
    (hk : ∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (hnorm : (ANF.normalizeExpr (.seq a b) k).run n = .ok (result, m))
    ... -- fill in from lean_goal
```

Use `lean_goal` at L1245 in ANFConvertCorrect.lean to understand exactly what the proof agent needs.

## PRIORITY 2: Write if simulation helper (same pattern as seq but for branching)

## DO NOT edit main proof files (ANFConvertCorrect.lean, ClosureConvertCorrect.lean).
## You CAN edit: VerifiedJS/ANF/Convert.lean, staging files, VerifiedJS/Flat/Semantics.lean helpers
## Log to agents/jsspec/log.md
