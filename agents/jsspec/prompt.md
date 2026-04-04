# jsspec — Close CC sorries via depth induction on Core_step_preserves_supported

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3GB available (supervisor freed memory).
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## SORRY COUNT: 33 total in ClosureConvertCorrect.lean

### PRIMARY TARGET: `| none =>` sorries (L3426, L3456, L3466, L3479, L3489, L3499, L3509, L3519)

These 8 sorries are ALL the same pattern: a sub-expression is NOT a value, Core.step? steps it. The result expression has the SAME outer constructor with the stepped sub-expression. `supported` is preserved because:
1. The stepped sub-expression preserves `supported` (by INDUCTION on the sub-step)
2. The surrounding structure is unchanged

**THE PROBLEM**: The current proof uses `cases e` with NO induction. Without an IH, these can't close.

**THE FIX**: Add depth induction. Here's the EXACT approach:

1. Find the theorem `Core_step_preserves_supported` (around L3375). It currently starts with something like:
```lean
theorem Core_step_preserves_supported ... : s'.expr.supported = true := by
  ... cases s.expr ...
```

2. Wrap with depth induction. Change to:
```lean
theorem Core_step_preserves_supported ... : s'.expr.supported = true := by
  have : ∀ n (e : Core.Expr), e.depth ≤ n → ... := by
    intro n; induction n with
    | zero => intro e hd; cases e <;> simp [Core.Expr.depth] at hd
    | succ n ih => intro e hd; cases e with
      -- ... existing cases, but now `ih` is available
  exact this _ _ (Nat.le_refl _) ...
```

3. For each `| none =>` case, the pattern becomes:
```lean
    | none =>
      -- Core.step? steps the sub-expression
      simp [Core.step?] at hstep
      -- Extract stepped sub-expression
      split at hstep
      · -- sub-step exists
        obtain ⟨-, rfl⟩ := hstep
        simp [Core.Expr.supported]
        exact ⟨ih _ (by simp [Core.Expr.depth] at hd; omega) ... hsupp_sub ..., hrest⟩
      · -- no step → contradiction
        simp at hstep
```

4. Use `lean_multi_attempt` to test each case BEFORE committing.

### SECONDARY TARGET: Bottom 10 cases (L3520-L3529)

These are: call, binary, getProp, setProp, getIndex, setIndex, deleteProp, objectLit, arrayLit, tryCatch.

Same pattern but more complex — each has multiple sub-expressions that could be values or not. With depth induction + IH available, use `simp [Core.step?, Core.Expr.supported] at hstep ⊢` then case split.

### IMPORTANT: Don't break existing proofs!

The cases that already work (lit, var, «break», «continue», functionDef, while_, newObj, etc.) must still compile. Test with `lean_goal` on a few existing cases after your changes.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
