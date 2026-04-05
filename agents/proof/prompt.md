# proof — Close hasAbruptCompletion_step_preserved + NoNestedAbrupt_step_preserved

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.8GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: step?_preserves_funcs is PROVED! Steps_preserves_funcs also proved. Now close the two big case-split theorems.

The Flat/Semantics.lean infrastructure is DONE (0 sorries). Your job now: close the two sorry'd theorem bodies at L9460 and L9469 in ANFConvertCorrect.lean. These are the HIGHEST IMPACT targets — they unblock NoNestedAbrupt_steps_preserved which chains into anfConvert_steps_star.

## TASK 1: PROVE hasAbruptCompletion_step_preserved (L9460) — HIGHEST PRIORITY

At L9453-9460:
```lean
private theorem hasAbruptCompletion_step_preserved (e : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env) (ev : Core.TraceEvent) (sf' : Flat.State)
    (hac : hasAbruptCompletion e = false)
    (hfuncs_ac : ∀ (i : Nat) (fd : Flat.FuncDef), funcs[i]? = some fd → hasAbruptCompletion fd.body = false)
    (hstep : Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf')) :
    hasAbruptCompletion sf'.expr = false := by
  sorry
```

**HOW TO PROVE**: This is a big case split on `e`. Use `lean_goal` at L9460 to see the state. Then:

```lean
  unfold Flat.step? at hstep
  -- Case split on e
  cases e with
  | lit v => simp at hstep  -- lit doesn't step (step? returns none)
  | var name => simp [Flat.step?] at hstep; ... -- var steps to lit, hasAbruptCompletion lit = false
  | seq a b => ...
  | let_ name init body => ...
  -- etc. for each Flat.Expr constructor
```

For each constructor:
1. The step? match tells you what sf'.expr is
2. Show hasAbruptCompletion sf'.expr = false using:
   - hac (the input doesn't have abrupt completion, so sub-exprs don't either)
   - hfuncs_ac (for call/funcDef cases where a function body is looked up)
   - simp [hasAbruptCompletion] to reduce

**Key patterns:**
- `seq a b` stepping a: result is `seq a' b` — hasAbruptCompletion propagates from a and b
- `let_ name init body` stepping init: result is `let_ name init' body`
- `call` with all values and funcs lookup: result is the function body — use hfuncs_ac
- `if cond then_ else_`: if cond is value, result is then_ or else_ — both have hasAbruptCompletion = false from hac

Use `set_option maxHeartbeats 1600000 in` before the theorem if needed. The case split will be large but each case should be straightforward.

Try `lean_multi_attempt` at L9460 with:
```
["unfold Flat.step? at hstep; cases e <;> simp_all [hasAbruptCompletion, Flat.pushTrace, Flat.allocFreshObject]",
 "simp [Flat.step?] at hstep; split at hstep <;> simp_all [hasAbruptCompletion, Flat.pushTrace]"]
```

## TASK 2: PROVE NoNestedAbrupt_step_preserved (L9469) — SECOND PRIORITY

At L9462-9469:
```lean
private theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr)
    (hfuncs_na : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → NoNestedAbrupt fd.body)
    (hfuncs_ac : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → hasAbruptCompletion fd.body = false)
    (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr := by
  sorry
```

Same structure as Task 1 but for NoNestedAbrupt. Case split on sf.expr:
- Each eval-context case (seq, let, if stepping sub-expr): NoNestedAbrupt of wrapper from NoNestedAbrupt of sub-result + original parts
- Value-producing cases: lit values are trivially NoNestedAbrupt
- Call cases: use hfuncs_na for function body lookup

## TASK 3: Close L9866 + L9919 (break/continue compound eval context)

These need Flat.step? error propagation through eval contexts. Pattern: if the expression has a break/continue in eval context position, Flat.step? steps the inner sub-expression, producing a new state where break/continue is still in eval context. Use the same case-split technique.

## PRIORITY ORDER
1. hasAbruptCompletion_step_preserved (L9460) — most impactful
2. NoNestedAbrupt_step_preserved (L9469) — same technique, second biggest
3. L9866 + L9919 — break/continue compound

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
