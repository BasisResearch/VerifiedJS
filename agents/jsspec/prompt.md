# jsspec — CLOSE 18 sorries via depth induction on Core_step_preserves_supported

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: You ran 4.5 hours with ZERO closures last run. UNACCEPTABLE.

## TASK: Add depth induction to Core_step_preserves_supported (L3375)

The current proof uses `cases hexpr : s.expr` — no induction hypothesis available. The 7 `| none => sorry` cases (L3426, L3456, L3466, L3478, L3488, L3498, L3508) and the 11 constructor cases (L3509-3519) ALL need an IH because Core.step? on a compound with non-value sub-expression steps that sub-expression, and we need `supported` preserved on the stepped sub.

### EXACT APPROACH — wrap with `suffices`:

```lean
private theorem Core_step_preserves_supported (s s' : Core.State) (ev : Core.TraceEvent)
    (hsupp : s.expr.supported = true) (hstep : Core.step? s = some (ev, s')) :
    s'.expr.supported = true := by
  suffices h : ∀ (n : Nat) (e : Core.Expr), e.depth ≤ n →
    ∀ (s s' : Core.State) (ev : Core.TraceEvent),
      s.expr = e → e.supported = true → Core.step? s = some (ev, s') →
      s'.expr.supported = true from
    h s.expr.depth s.expr (Nat.le_refl _) s s' ev rfl hsupp hstep
  intro n
  induction n with
  | zero =>
    intro e hd s s' ev hexpr hsupp hstep
    -- depth 0 means leaf. All compound exprs have depth ≥ 1.
    cases e <;> simp [Core.Expr.depth] at hd
    -- Only leaves survive. Copy existing leaf proofs (var, this, break, continue, etc.)
    -- But actually: lit has step? = none (contradiction), var/this/break/continue are fine
    all_goals (rw [state_with_expr_eq hexpr] at hstep; simp [Core.step?, Core.pushTrace] at hstep)
    all_goals (try (obtain ⟨-, rfl⟩ := hstep; rfl))
    -- var and this need lookup split — copy from existing proof
    all_goals sorry
  | succ n ih =>
    intro e hd s s' ev hexpr hsupp hstep
    cases hexpr' : e with
    -- PUT ALL EXISTING CASES HERE, but:
    -- 1. Replace `hexpr` references with `hexpr'` and `he : s.expr = e`
    -- 2. In each | none => case, apply ih:
```

### THE KEY PATTERN for `| none =>` cases:

Each `| none =>` case means `exprValue? sub = none`, so Core.step? steps `sub`. The result expression wraps the stepped sub-expression in the same constructor. Example for `| «return» (some arg) =>`:

```lean
    | none =>
      -- arg is not a value, so Core.step? steps arg
      rw [state_with_expr_eq hexpr] at hstep  -- where hexpr : s.expr = .return (some arg)
      simp [Core.step?, Core.exprValue?, hval] at hstep
      -- Now hstep tells us step? on arg produced some result
      -- Split on step? result
      split at hstep
      · next sub_ev sub_s' hsub =>
        obtain ⟨-, rfl⟩ := hstep
        simp [Core.Expr.supported]
        -- Need: sub_s'.expr.supported = true
        -- Use ih n arg (by simp [Core.Expr.depth] at hd; omega) ...
        exact ih n arg (by cases e <;> simp [Core.Expr.depth] at hd ⊢; omega)
          {s with expr := arg} sub_s' sub_ev rfl
          (by simp [Core.Expr.supported] at hsupp; exact hsupp)  -- arg.supported from compound.supported
          hsub
      · simp at hstep  -- step? = none contradicts hstep
```

### FOR THE 11 CONSTRUCTOR CASES (L3509-3519):

These (unary, call, binary, getProp, setProp, getIndex, setIndex, deleteProp, objectLit, arrayLit, tryCatch) are the same pattern but with multiple sub-expressions. Each needs:

1. `rw [state_with_expr_eq hexpr] at hstep`
2. `simp [Core.step?, Core.exprValue?] at hstep` to unfold
3. Case split on which sub-expression gets stepped
4. Apply `ih` for the stepped sub

### STEP BY STEP PLAN:

1. Use `lean_goal` at L3377 and `lean_hover_info` on `Core.Expr.depth` to understand the depth function.
2. Add the `suffices` wrapper. Put ALL existing proof code after `cases hexpr : s.expr with` inside the `| succ n ih =>` branch, changing `hexpr` to work with the new structure.
3. Handle the `zero` base case (leaves only).
4. Test that existing working cases still compile (use `lean_multi_attempt`).
5. Fix `| none =>` cases one at a time using `ih`.
6. Attack constructor cases.

### IMPORTANT: Incremental approach
- Start by JUST adding the suffices wrapper and making the existing cases compile under it
- Then fix sorry cases one at a time
- Build after each batch of changes

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
