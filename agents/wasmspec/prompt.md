# wasmspec — CLOSE 6 CALLSTACK CONDITION SORRIES (L13351-L13397)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- Total: ~47 sorries (ANF 33, CC 14).
- Steps_preserves_funcs, Steps_trace_append: PROVED (in Flat/Semantics.lean)
- Steps_preserves_callStack: PROVED (takes condition callback, L2339 in Semantics.lean)
- step?_preserves_callStack: PROVED (single-step, two conditions: no __call_frame_return__ tryCatch, no all-value call)
- hasReturnInHead_callStackSafe: PROVED (L13239 in ANFConvertCorrect.lean)
- hasAbruptCompletion_step_preserved: PROVED (L15729 in ANFConvertCorrect.lean)

## P0: CLOSE 6 CALLSTACK CONDITION SORRIES (HIGHEST PRIORITY)

The 6 identical sorry pairs are at L13351+L13353, L13374+L13375, L13396+L13397. Each is inside the `hpres` callback for `Steps_preserves_callStack`. They need to prove at each intermediate state `smid'`:
1. `smid'.expr ≠ .tryCatch body "__call_frame_return__" catch_ fin` (sorry #1 in each pair)
2. `smid'.expr = .call f env args → some sub-expr is not a value` (sorry #2 in each pair)

### CONTEXT

These are in `hasReturnInHead_return_steps`, seq_left case. The Steps are from `⟨a, env, heap, trace, funcs, cs⟩` where `HasReturnInHead a` and `NoNestedAbrupt a` (from the outer expression).

### APPROACH: Prove HasReturnInHead is preserved through single steps

**Key theorem to prove** (place near L13239):

```lean
private theorem HasReturnInHead_step_preserved_or_value (e : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env) (ev : Core.TraceEvent) (sf' : Flat.State)
    (hret : HasReturnInHead e)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf')) :
    HasReturnInHead sf'.expr ∨ Flat.isValue sf'.expr := by
  sorry
```

**Proof sketch by cases on hret**:
- `return_none_direct`: `e = .return none`. step? gives `.lit (...)`. Right disjunct (isValue).
- `return_some_direct v hv`: `e = .return (some v)`, v is value. step? gives `.lit (...)`. Right disjunct.
- `return_some_arg hret_inner`: `e = .return (some inner)`, HasReturnInHead inner. step? steps inner → inner'. By IH: `HasReturnInHead inner' ∨ isValue inner'`. Left → `.return_some_arg`. Right → inner' is value, but then step? would give `.lit (...)` directly (check exactly what step? does for `.return (some value)`).
- `seq_left hret_a`: `e = .seq a b`, HasReturnInHead a. step? steps a → a'. If a' NOT value: `sf'.expr = .seq a' b`, and by IH `HasReturnInHead a' ∨ isValue a'`. Left → seq_left. Right → contradiction (a' value but we're in not-value branch). If a' IS value: `sf'.expr = b`. Left disjunct fails. Right only if b is value. **THIS IS THE HARD CASE**.
- Similar for let_init, binary_lhs, call_func, call_env, call_args, etc.

### THE HARD CASE: compound wrapper dissolves

When `HasReturnInHead (.seq a b)` via `seq_left`, step? evaluates `a`. If `a` steps to a value in ONE step (e.g., `a = .return none` → `.lit ...`), then `sf'.expr = b` which may have neither HasReturnInHead nor be a value.

**SOLUTION**: You need a STRONGER invariant. Instead of just HasReturnInHead, prove:

```lean
/-- During evaluation of a HasReturnInHead expression, at every intermediate state,
    the expression either has HasReturnInHead OR has hasAbruptCompletion = false
    (meaning it's a "normal" continuation after the return fired). -/
private theorem HasReturnInHead_steps_callStackSafe
    (a : Flat.Expr) (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (hret : HasReturnInHead a) (hna : NoNestedAbrupt a)
    (hfuncs_ac : ∀ (i : Nat) (fd : Flat.FuncDef), funcs[i]? = some fd → hasAbruptCompletion fd.body = false)
    (smid : Flat.State) (evs_pre : List Core.TraceEvent)
    (hsteps : Flat.Steps ⟨a, env, heap, trace, funcs, cs⟩ evs_pre smid)
    (t : Core.TraceEvent) (smid' : Flat.State)
    (hstep : Flat.step? smid = some (t, smid')) :
    (∀ body catch_ fin, smid.expr ≠ .tryCatch body "__call_frame_return__" catch_ fin) ∧
    (∀ f' env' args', smid.expr = .call f' env' args' →
      Flat.exprValue? f' = none ∨ Flat.exprValue? env' = none ∨ Flat.valuesFromExprList? args' = none) := by
  sorry
```

**KEY INSIGHT**: NoNestedAbrupt (.seq a b) means BOTH a and b have no nested abrupt completions. So:
- Before return fires: HasReturnInHead smid.expr → `hasReturnInHead_callStackSafe` gives both conditions
- After return fires: smid.expr comes from evaluating a continuation `b`. `NoNestedAbrupt b` means `hasAbruptCompletion b = false`. `hasAbruptCompletion_step_preserved` keeps this invariant. And when `hasAbruptCompletion = false`:
  - Condition 1: The expr can't be `.tryCatch _ "__call_frame_return__" _ _` because `"__call_frame_return__"` tryCatch is only created by step? during call dispatch. It's never in normalizeExpr output. And once created, it HAS abrupt completion (the body was a call result which can return). Since `hasAbruptCompletion = false` for our expression, it can't BE a __call_frame_return__ tryCatch.
  - Condition 2: Even with `hasAbruptCompletion = false`, a `.call f env args` with all values IS possible. BUT: normalizeExpr output always wraps calls in `.let` or other compound forms, so the call arguments are NEVER all values in the initial expression. During evaluation, sub-expressions get evaluated to values... but by the time all args are values, the call fires and produces a new expression. The question is whether an intermediate state can have all-value call args.

**ALTERNATIVE SIMPLER APPROACH**: Instead of this complex invariant, check if the `evs1.length ≤ evs.length` bound helps. The `evs` is the trace from evaluating the full HasReturnInHead expression. Maybe the Steps only go up to the error event (when the return fires), and after that there are no more steps. If so, HasReturnInHead is preserved at ALL relevant intermediate steps.

**CHECK THIS**: Run `lean_goal` at L13351 to see exactly what hypotheses are available, especially the length bound. If `evs1.length ≤ evs.length` limits the Steps to only the error-producing prefix, then the continuation after return never runs within these Steps.

### STEP-BY-STEP PLAN

1. Run `lean_goal` at L13351 to understand the exact proof state
2. Check if the length bound `_hlen` eliminates the post-return continuation case
3. If YES: Prove HasReturnInHead_step_preserved_or_value (the simpler theorem). At each intermediate state, HasReturnInHead holds (since value states don't step, so we're always in the HasReturnInHead branch). Apply hasReturnInHead_callStackSafe.
4. If NO: Prove the full HasReturnInHead_steps_callStackSafe theorem with the compound invariant.
5. Apply the theorem at all 6 sorry sites (they're all identical, just copy-paste).

## P1: CLOSE L13407 (remaining compound HasReturnInHead cases)

After P0, expand `| _ => sorry` at L13407 into explicit constructor matches, following the seq_left pattern. Each compound case (let_init, binary_lhs, call_func, call_env, etc.) follows the same template as seq_left (L13325-L13406).

## P2: HasAwaitInHead + HasYieldInHead (L13763, L13936)

Same architecture as HasReturnInHead. Apply the same pattern from P0-P1.

## SKIP
- L10183-L10554 (trivialChain — BLOCKED, do not touch)
- L14033-14864 (while/if — BLOCKED)
- L15705-15726 (tryCatch — BLOCKED)
- L17283, L17354 (unknown, low priority)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — callStack condition sorries L13351-L13397" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
