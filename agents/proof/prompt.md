# proof — Propagate NoNestedAbrupt invariant + close L8343

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## GREAT JOB closing L8204 (NESTED_THROW) via NoNestedAbrupt exfalso. Now propagate hna.

## STATE: ANF has 24 sorry lines. Your targets: L9409 (hna propagation) then L8343.

## TASK 1 (HIGHEST PRIORITY): Close L9409 — propagate NoNestedAbrupt invariant

L9409 is:
```lean
all_goals have hna_sf : NoNestedAbrupt sf.expr := sorry -- TODO: propagate NoNestedAbrupt invariant
```

This is inside `anfConvert_step_star` (the main step simulation). You need to:

1. Add `(hna : NoNestedAbrupt sf.expr)` to the signature of `anfConvert_step_star`
2. Replace the sorry with `hna`
3. Update `anfConvert_steps_star` (the caller that calls `anfConvert_step_star` inductively) to:
   - Take `hna` as a parameter
   - Prove that after each step, NoNestedAbrupt is preserved for the new state sf'

The key insight: `NoNestedAbrupt` should be preserved by Flat steps. If `NoNestedAbrupt e` and `Flat.step? ⟨e, ...⟩ = some (ev, ⟨e', ...⟩)`, then `NoNestedAbrupt e'`.

You may need a lemma `NoNestedAbrupt_step_preserved`:
```lean
theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr) (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr
```

This should follow by cases on the step. Most Flat steps reduce to sub-expressions (which are NoNestedAbrupt by inversion) or produce literals (which are trivially NoNestedAbrupt).

Use `lean_local_search` for `NoNestedAbrupt` to see what inversions are available.

### Step-by-step:
1. `lean_local_search "NoNestedAbrupt"` to see constructors/inversions
2. Write `NoNestedAbrupt_step_preserved` (~30-50 lines, cases on Flat.step?)
3. Add `(hna : NoNestedAbrupt sf.expr)` to `anfConvert_step_star`
4. Replace `sorry` at L9409 with `hna`
5. Add `hna` to `anfConvert_steps_star` and prove preservation via `NoNestedAbrupt_step_preserved`
6. Verify build passes

## TASK 2: Close L8343 — compound throw dispatch

L8343 is the `| _ =>` case in `normalizeExpr_throw_step_sim` at L8341-8343:
```lean
  | _ =>
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    sorry
```

This handles compound expressions (seq, let, if, call, etc.) that have `HasThrowInHead` somewhere inside. Unlike the L8204 exfalso case, this is NOT contradictory — it's a real proof case.

Use `lean_goal` at L8343 to see the exact goal. The expression `e` is compound with `HasThrowInHead e`, and `NoNestedAbrupt (.throw e)` gives `AbruptFree e`, but wait — `e` here is the `_` match so it's the Flat expression, not the throw argument.

Actually, re-read the code: `normalizeExpr_throw_step_sim` matches on `sf.expr` cases. The `| .throw arg => ...` case is handled above. The `| _ =>` at L8341 catches expressions that are NOT `.throw arg`. So `sf.expr` is some compound expression, and the goal is to show that `normalizeExpr sf.expr k = .ok (.throw ...)` implies Flat can step.

This is a **step simulation for non-throw expressions that normalize to throw**. The expression must have a HasThrowInHead sub-expression. With `hna : NoNestedAbrupt sf.expr`, you know the throw arguments are simple.

Use `lean_goal` and `lean_multi_attempt` to explore this before editing.

## TASK 3 (IF TIME): Apply NoNestedAbrupt pattern to return/yield/await

L8493/8496 (return), L8666/8669 (await), L8820/8823 (yield) follow the exact same pattern as throw. Once Task 1 is done, these should be approachable with the same exfalso + trivialChain pattern.

## DO NOT:
- Work on Group A (L7516-7702) eval context lifting — PARKED
- Work on L8850 (let step sim), L8898 (while step sim) — wasmspec handles
- Work on L9116/L9117/L9235/L9236 (if step sim compound) — wasmspec handles
- Work on L9280 (tryCatch) — DEFERRED
- Work on L9660/L9713 (break/continue compound) — needs Flat.step? semantics change, PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
