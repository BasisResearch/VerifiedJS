# proof — Write equation lemmas for getProp/setProp/etc, then close objectLit+tryCatch

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~100MB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS
Equation lemmas for call/newObj/getEnv exist at L1137-1166 of Flat/Semantics.lean. The remaining sorry cases in hasAbruptCompletion_step_preserved (L9761 objectLit, L9776 tryCatch) and NoNestedAbrupt_step_preserved (L10123 objectLit, L10138 tryCatch) NEED equation lemmas for objectLit and tryCatch. Also the "all-values" cases at L9704, L9719, L10067, L10081 are closeable WITHOUT new lemmas.

## TASK 1: Write equation lemmas in Flat/Semantics.lean (after L1166)

These follow the EXACT same pattern as the existing call/newObj/getEnv lemmas. Insert after line 1166.

```lean
/-- Stepping getProp when obj is not a value: recurse into obj. -/
@[simp] theorem step?_getProp_step_obj (s : State) (obj : Expr) (prop : PropName)
    (ho : exprValue? obj = none) :
    step? { s with expr := .getProp obj prop } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .getProp so.expr prop, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping setProp when obj is not a value: recurse into obj. -/
@[simp] theorem step?_setProp_step_obj (s : State) (obj : Expr) (prop : PropName) (val : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .setProp obj prop val } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .setProp so.expr prop val, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping getIndex when obj is not a value: recurse into obj. -/
@[simp] theorem step?_getIndex_step_obj (s : State) (obj idx : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .getIndex obj idx } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .getIndex so.expr idx, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping setIndex when obj is not a value: recurse into obj. -/
@[simp] theorem step?_setIndex_step_obj (s : State) (obj idx val : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .setIndex obj idx val } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .setIndex so.expr idx val, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping deleteProp when obj is not a value: recurse into obj. -/
@[simp] theorem step?_deleteProp_step_obj (s : State) (obj : Expr) (prop : PropName)
    (ho : exprValue? obj = none) :
    step? { s with expr := .deleteProp obj prop } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .deleteProp so.expr prop, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl
```

If `rw [step?.eq_1]; simp only [ho]` doesn't work for any of these, try:
- `unfold step?; simp [ho]; cases step? ... <;> rfl`
- `simp [step?, ho]; cases step? ... <;> rfl`

**BUILD Flat/Semantics.lean FIRST** to verify: `lake build VerifiedJS.Flat.Semantics`

## TASK 2: Close "all-values" cases (L9704, L9719, L10067, L10081)

These are in hasAbruptCompletion_step_preserved and NoNestedAbrupt_step_preserved where both f and envExpr are values (call) or envExpr is a value (newObj). In these cases, step? either:
- Steps an arg (use firstNonValueExpr + IH, like makeEnv/arrayLit cases above)
- Executes the call/newObj (produces .lit result)

Pattern for L9704 (call all-values in hasAbruptCompletion):
```lean
-- After | some envVal =>
-- step? does: valuesFromExprList? args → execute or firstNonValueExpr args → step arg
unfold Flat.step? at hstep
-- ... case split on valuesFromExprList?, then firstNonValueExpr
-- All terminal branches produce .lit v → hasAbruptCompletion (.lit v) = false
sorry -- fill in after equation lemmas
```

Actually these may need `split at hstep` which is broken. If so, use `unfold Flat.step? at hstep; simp [hfv, hev] at hstep` to reduce.

## TASK 3: Close objectLit cases (L9761, L10123)

The helper lemmas `hasAbruptCompletionProps_firstNonValueProp_preserved` and `firstNonValueProp_noNestedAbrupt_preserved` ALREADY EXIST. Use them like the arrayLit case pattern at L9762-9775 and L10124-10137.

objectLit has `firstNonValueProp` instead of `firstNonValueExpr`. The step? structure is:
```
| .objectLit props =>
    match valuesFromPropList? props with
    | some vs => allocate → .lit (.object addr)
    | none =>
        match firstNonValueProp props with
        | some (done, name, target, remaining) =>
            match step? target with
            | some (t, sa) => (.objectLit (done ++ [(name, sa.expr)] ++ remaining), ...)
            | none => none
        | none => none
```

## What NOT to work on:
- Group A (L7696-7882): PARKED
- Compound HasXInHead (L8526, L8683, L8860, L9018): needs eval context lemmas
- Inner compound (L8677, L8854, L9012): wasmspec owns these
- break/continue (L10529, L10582): needs step? error propagation
- CC anything

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
