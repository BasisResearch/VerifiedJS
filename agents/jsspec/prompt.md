# jsspec — Close CC sorries via depth induction on Core_step_preserves_supported

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~100MB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## SORRY COUNT: 33 total in ClosureConvertCorrect.lean

### PRIMARY TARGET: 17 compound cases at L3412, L3431-L3447

These are in `Core_step_preserves_supported`. The theorem at L3375 does case analysis but NO induction. The sorry'd cases (let, assign, if, seq, call, unary, binary, getProp, setProp, getIndex, setIndex, deleteProp, objectLit, arrayLit, throw, tryCatch, typeof) are compound: Core.step? steps a sub-expression.

**STATUS**: L3412 (return some) is the only one separate. L3431-L3447 are 17 blank sorries.

**FIX**: Convert to depth induction. The current proof structure is `cases e with ...`. You need:

1. Add a `suffices` with depth induction BEFORE the `cases e`:
```lean
  suffices ∀ n e, e.depth ≤ n → ∀ env heap trace funcs cs ev s',
    e.supported = true →
    Core.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, s') →
    s'.expr.supported = true from
    this _ _ (Nat.le_refl _) _ _ _ _ _ _ _ hsupp (by rwa [show s = ⟨s.expr, s.env, s.heap, s.trace, s.funcs, s.callStack⟩ from by cases s; rfl])
  intro n
  induction n with
  | zero =>
    intro e hd env heap trace funcs cs ev s' hsupp hstep
    cases e with
    | lit => simp [Core.step?] at hstep
    | var => simp [Core.Expr.depth] at hd  -- depth ≥ 1
    | _ => simp [Core.Expr.depth] at hd  -- depth ≥ 1 for all compound
  | succ n ih =>
    intro e hd env heap trace funcs cs ev s' hsupp hstep
    cases e with
    -- ... same cases as current proof, but now ih is available
```

2. For each compound case, the pattern is:
```lean
    | «let» name init body =>
      simp [Core.Expr.supported] at hsupp
      obtain ⟨hinit, hbody⟩ := hsupp
      -- Core.step? for let: if init is value → substitute, if not → step init
      simp [Core.step?] at hstep
      -- Case split on exprValue? init
      split at hstep
      · -- init is value: body with substitution. supported preserved by subst
        sorry -- may need supported_subst lemma
      · -- init not value: step init, produce .let stepped body
        -- Use ih on the sub-step
        sorry -- ih _ (by simp [Core.Expr.depth] at hd; omega) ...
```

3. Many cases may close with just `simp_all [Core.Expr.supported]` after the IH is applied.

**USE `lean_multi_attempt` on each case** to test whether `simp_all [Core.Expr.supported, Core.step?, Core.pushTrace]` closes it.

### SECONDARY TARGETS (if time permits)
- L6525: functionDef — needs closure allocation proof
- L4429: non-consoleLog call — needs funcs correspondence
- L6682, L6755: tryCatch — inline sorry

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
