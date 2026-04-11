# wasmspec — CLOSE 6 CALLSTACK CONDITION SORRIES (L13351-L13397)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- Total: ~51 sorries (ANF 36, CC 15).
- Steps_preserves_funcs, Steps_trace_append: PROVED
- Steps_preserves_callStack: PROVED (condition callback)
- step?_preserves_callStack: PROVED (two conditions)
- hasReturnInHead_callStackSafe: PROVED (L13239)
- hasAbruptCompletion_step_preserved: PROVED (L15729)

## P0: CLOSE 6 CALLSTACK CONDITION SORRIES (HIGHEST PRIORITY)

The 6 sorries at L13351+L13353, L13374+L13375, L13396+L13397 each need:
1. `smid'.expr ≠ .tryCatch body "__call_frame_return__" catch_ fin`
2. `smid'.expr = .call f env args → some sub-expr is not a value`

These are inside the `hpres` callback for `Steps_preserves_callStack`, within `hasReturnInHead_return_steps` (seq_left case).

### THE KEY INSIGHT

At each intermediate step `smid → smid'`, `smid` has `HasReturnInHead smid.expr` (from the outer invariant). `hasReturnInHead_callStackSafe` (L13239) already proves BOTH conditions for states with HasReturnInHead. So the question is: does `HasReturnInHead` hold at `smid`?

**YES, if HasReturnInHead is preserved through non-terminal steps.**

### APPROACH: Prove HasReturnInHead preservation for non-value steps

```lean
private theorem HasReturnInHead_step_preserved (e : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env) (ev : Core.TraceEvent) (sf' : Flat.State)
    (hret : HasReturnInHead e)
    (hna : NoNestedAbrupt e)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf'))
    (hnv : ¬ Flat.isValue sf'.expr) :
    HasReturnInHead sf'.expr := by
  cases hret with
  | return_none_direct => simp [Flat.step?] at hstep; obtain ⟨_, h⟩ := hstep; subst h; simp [Flat.isValue] at hnv
  | return_some_direct v hv => simp [Flat.step?, Flat.exprValue?] at hstep; sorry -- v is value, step gives lit, contradiction with hnv
  | return_some_arg inner hri =>
    simp [Flat.step?] at hstep
    sorry -- step inner, IH gives HasReturnInHead inner' ∨ value. hnv eliminates value.
  | seq_left a b hret_a =>
    simp [Flat.step?] at hstep
    sorry -- step a. If a→a' non-value: sf'.expr = .seq a' b, HasReturnInHead a' by IH → seq_left. If a→value: sf'.expr = b, but b may not have HasReturnInHead.
  -- similar for other constructors
```

**THE HARD CASE**: `seq_left` when `a` steps to a value in one step (e.g., `a = .return none` → `.lit ...`). Then `sf'.expr = b` which may not have HasReturnInHead. BUT: `hnv` says `sf'.expr` is not a value. And `b` could be a non-value expression without HasReturnInHead.

**ALTERNATIVE**: Instead of proving HasReturnInHead preserved, prove the TWO CONDITIONS DIRECTLY preserved through steps:

```lean
private theorem callStackSafe_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hret : HasReturnInHead sf.expr)
    (hna : NoNestedAbrupt sf.expr)
    (hstep : Flat.step? sf = some (ev, sf')) :
    (∀ body catch_ fin, sf'.expr ≠ .tryCatch body "__call_frame_return__" catch_ fin) ∧
    (∀ f' env' args', sf'.expr = .call f' env' args' →
      Flat.exprValue? f' = none ∨ Flat.exprValue? env' = none ∨ Flat.valuesFromExprList? args' = none) := by
  sorry
```

Then at each step in the `hpres` callback:
- If `HasReturnInHead smid.expr`: use `hasReturnInHead_callStackSafe`
- If not: we need the conditions to still hold (this is the hard part)

**SIMPLEST PATH**: Check if the `Steps` in the hpres callback are BOUNDED by the error event. If the steps only go up to when the return fires (producing an error), then HasReturnInHead holds at ALL intermediate steps (since value states don't step further).

Run `lean_goal` at L13351 to check the available hypotheses. Look for a length bound or termination condition.

### STEP-BY-STEP
1. Run `lean_goal` at L13351
2. Check if there's a bound showing intermediate states still have HasReturnInHead
3. If yes: apply `hasReturnInHead_callStackSafe` directly at each sorry
4. If no: prove HasReturnInHead preservation (start with `return_none_direct` base case, which gives contradiction with non-value)
5. Apply to all 6 sorry sites

## P1: L13407 (remaining compound HasReturnInHead cases)
After P0, expand `| _ => sorry` into explicit constructor matches.

## P2: HasAwaitInHead + HasYieldInHead (L13763, L13936)
Same architecture as P0-P1.

## SKIP
- L10183-L10554 (trivialChain — proof agent)
- L14033-14864 (while/if — BLOCKED)
- L15705-15726 (tryCatch — BLOCKED)
- L17053-17354 (end-of-file — BLOCKED)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — callStack condition sorries L13351-L13397" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
