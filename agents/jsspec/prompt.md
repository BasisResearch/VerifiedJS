# jsspec — Close CC sorries. 30 active sorry lines. Focus on Core_step_preserves_supported (19 of them).

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.1GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## SORRY BREAKDOWN (30 total)

### GROUP 1: Core_step_preserves_supported (19 sorry lines: L3412 + L3431-3447)
This is your PRIMARY target. 19 of 30 CC sorries are in this one theorem.

**Problem**: The theorem at L3375 does case analysis but NO induction. The proved cases (var, this, break, continue, etc.) work because Core.step? produces a `.lit v` or similar atomic result. The sorry'd cases (let, assign, if, seq, call, etc.) are compound: Core.step? steps a sub-expression, producing a new expression that also needs `supported = true`.

**Fix**: Convert to depth induction. Replace the current proof with:

```lean
private theorem Core_step_preserves_supported (s s' : Core.State) (ev : Core.TraceEvent)
    (hsupp : s.expr.supported = true) (hstep : Core.step? s = some (ev, s')) :
    s'.expr.supported = true := by
  suffices ∀ n e, e.depth ≤ n → ∀ env heap trace funcs cs ev s',
    e.supported = true →
    Core.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, s') →
    s'.expr.supported = true from
    this _ _ (Nat.le_refl _) _ _ _ _ _ _ _ hsupp (by rwa [show s = ⟨s.expr, s.env, s.heap, s.trace, s.funcs, s.callStack⟩ from by cases s; rfl])
  intro n
  induction n with
  | zero => intro e hd; omega  -- depth is always ≥ 1 for steppable exprs... or handle base case
  | succ n ih =>
    intro e hd env heap trace funcs cs ev s' hsupp hstep
    cases e with
    -- ... same cases as before, but now with `ih` available for recursive calls
```

For compound cases with IH available, the pattern is:
```lean
    | «let» name init body =>
      simp [Core.Expr.supported] at hsupp
      obtain ⟨hinit_supp, hbody_supp⟩ := hsupp
      rw [state_with_expr_eq rfl] at hstep
      simp [Core.step?, Core.pushTrace] at hstep
      -- Core.step? on let: if init is value, substitute; if not, step init
      -- Case split on whether init is a value
      sorry -- fill in: use ih on sub-expression step
```

Use `lean_multi_attempt` on each sorry case to check if `simp_all [Core.Expr.supported]` closes it after the induction rewrite. Many cases may close with just the IH + simp.

### GROUP 2: Other sorry groups (11 lines)
- **L3513**: captured var (multi-step) — SKIP (architectural)
- **L3842, L3865**: if CCStateAgree — SKIP (architectural)
- **L4429**: non-consoleLog call — needs funcs correspondence
- **L4637, L4645**: newObj semantic mismatch — SKIP (architectural)
- **L5283**: getIndex string — marked UNPROVABLE
- **L6525**: functionDef — needs closure allocation proof
- **L6682**: tryCatch inline sorry
- **L6683**: tryCatch with finally — SKIP (CCStateAgree)
- **L6755**: tryCatch inner
- **L6863**: while_ CCState — SKIP (architectural)

## PRIORITY ORDER
1. Convert Core_step_preserves_supported to depth induction
2. Close as many of the 19 compound cases as possible (each is -1 sorry)
3. Try L6525 (functionDef) and L4429 (non-consoleLog call) if time permits

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
