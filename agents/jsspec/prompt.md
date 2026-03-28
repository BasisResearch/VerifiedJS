# jsspec — INTEGRATE STAGING LEMMAS + COMPOUND NO-CONFUSION

## STATUS: Staging lemmas written but NOT integrated. The proof agent CANNOT USE them from `.lake/_tmp_fix/`. You MUST write them into actual source files.

## CRITICAL: Proof agent has 4 helper sorries in normalizeExpr_labeled_step_sim that need no-confusion lemmas.

The 4 helper sorries (L1180, L1181, L1187, L1204 in ANFConvertCorrect.lean) need to show normalizeExpr of compound expressions can't produce `.labeled`. The while_ and tryCatch cases are already proved (L1188-1203). You need lemmas for the remaining cases.

## PRIORITY 0: Write normalizeExpr compound no-confusion lemmas INTO `VerifiedJS/ANF/Convert.lean`

Add these BEFORE `end VerifiedJS.ANF` in Convert.lean. Each proves normalizeExpr of a compound expression can't produce `.labeled`:

```lean
@[simp] theorem normalizeExpr_let_not_labeled (name : String) (rhs body : Flat.Expr)
    (k : Trivial → ConvM Expr) (n : Nat) (label : String) (b : Expr) :
    (normalizeExpr (.let name rhs body) k).run n ≠ .ok (.labeled label b, _) := by
  unfold normalizeExpr
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; repeat (first | split at h | (simp [pure, Pure.pure, StateT.pure, Except.pure] at h; try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

@[simp] theorem normalizeExpr_seq_not_labeled (a b : Flat.Expr)
    (k : Trivial → ConvM Expr) (n : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.seq a b) k).run n ≠ .ok (.labeled label body, _) := by
  unfold normalizeExpr
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; repeat (first | split at h | (simp [pure, Pure.pure, StateT.pure, Except.pure] at h; try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

@[simp] theorem normalizeExpr_if_not_labeled (cond then_ else_ : Flat.Expr)
    (k : Trivial → ConvM Expr) (n : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.if cond then_ else_) k).run n ≠ .ok (.labeled label body, _) := by
  unfold normalizeExpr
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; repeat (first | split at h | (simp [pure, Pure.pure, StateT.pure, Except.pure] at h; try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

@[simp] theorem normalizeExpr_throw_not_labeled (arg : Flat.Expr)
    (k : Trivial → ConvM Expr) (n : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.throw arg) k).run n ≠ .ok (.labeled label body, _) := by
  unfold normalizeExpr
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; repeat (first | split at h | (simp [pure, Pure.pure, StateT.pure, Except.pure] at h; try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

@[simp] theorem normalizeExpr_await_not_labeled (arg : Flat.Expr)
    (k : Trivial → ConvM Expr) (n : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.await arg) k).run n ≠ .ok (.labeled label body, _) := by
  unfold normalizeExpr
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; repeat (first | split at h | (simp [pure, Pure.pure, StateT.pure, Except.pure] at h; try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))
```

Use `lean_multi_attempt` to verify each tactic works BEFORE editing. If `repeat` times out, try `set_option maxHeartbeats 400000`.

Also add simple cases for trivial expressions:
```lean
@[simp] theorem normalizeExpr_var_not_labeled (name : String)
    (k : Trivial → ConvM Expr) (n : Nat) (label : String) (body : Expr)
    (hk : ∀ t n', (k t).run n' ≠ .ok (.labeled label body, _)) :
    (normalizeExpr (.var name) k).run n ≠ .ok (.labeled label body, _) := by
  simp [normalizeExpr]; exact hk ..
```

## PRIORITY 1: ExprWellFormed inversion lemma

The proof agent has an ExprWellFormed sorry at L1180. They need:
```lean
theorem ExprWellFormed.return_some_inner {v : Flat.Expr} {env : Flat.Env}
    (h : ExprWellFormed (.return (some v)) env) : ExprWellFormed v env
```
Check how ExprWellFormed is defined, then write this inversion into the appropriate file.

## PRIORITY 2: seq simulation helper (for anfConvert_step_star L1277)

Use `lean_goal` at L1277 in ANFConvertCorrect.lean to understand what the proof agent needs, then write a helper theorem.

## DO NOT edit ANFConvertCorrect.lean or ClosureConvertCorrect.lean.
## You CAN edit: VerifiedJS/ANF/Convert.lean, VerifiedJS/Flat/Semantics.lean, VerifiedJS/Core/*.lean
## Log to agents/jsspec/log.md
