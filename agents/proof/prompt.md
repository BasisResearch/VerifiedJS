# proof — Write MISSING equation lemmas, then prove hasAbruptCompletion + NoNestedAbrupt

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.1GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS

Equation lemmas for call/newObj/getEnv/step_func/step_env exist at L1137-1166 of Flat/Semantics.lean (PROVED, @[simp]). But hasAbruptCompletion_step_preserved (L9428) and NoNestedAbrupt_step_preserved (L9707) are STILL monolithic sorry. The 16:30 run found that getProp/setProp/getIndex/setIndex/deleteProp/objectLit/arrayLit cases need ADDITIONAL equation lemmas.

## TASK 1: Write MISSING equation lemmas in Flat/Semantics.lean

Insert these AFTER the existing step?_getEnv_step_env (L1166). All are `simp [step?, h]` one-liners.

```lean
/-- Stepping getProp when obj is not a value. -/
@[simp] theorem step?_getProp_step_obj (s : State) (obj : Expr) (prop : PropName)
    (ho : exprValue? obj = none) :
    step? { s with expr := .getProp obj prop } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .getProp so.expr prop, env := so.env, heap := so.heap } t) := by
  simp [step?, ho]

/-- Stepping setProp when obj is not a value. -/
@[simp] theorem step?_setProp_step_obj (s : State) (obj : Expr) (prop : PropName) (val : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .setProp obj prop val } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .setProp so.expr prop val, env := so.env, heap := so.heap } t) := by
  simp [step?, ho]

/-- Stepping getIndex when obj is not a value. -/
@[simp] theorem step?_getIndex_step_obj (s : State) (obj idx : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .getIndex obj idx } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .getIndex so.expr idx, env := so.env, heap := so.heap } t) := by
  simp [step?, ho]

/-- Stepping setIndex when obj is not a value. -/
@[simp] theorem step?_setIndex_step_obj (s : State) (obj idx val : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .setIndex obj idx val } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .setIndex so.expr idx val, env := so.env, heap := so.heap } t) := by
  simp [step?, ho]

/-- Stepping deleteProp when obj is not a value. -/
@[simp] theorem step?_deleteProp_step_obj (s : State) (obj : Expr) (prop : PropName)
    (ho : exprValue? obj = none) :
    step? { s with expr := .deleteProp obj prop } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        some (t, pushTrace { s with expr := .deleteProp so.expr prop, env := so.env, heap := so.heap } t) := by
  simp [step?, ho]
```

If any of these fail with `simp [step?, ho]`, try `unfold step?; simp [ho]` or `unfold step?; dsimp; rw [ho]; rfl`.

**BUILD Flat/Semantics.lean first** to verify: `lake build VerifiedJS.Flat.Semantics`

## TASK 2: Prove hasAbruptCompletion_step_preserved (L9428)

Replace the monolithic `sorry` at L9428 with depth-induction proof. The KEY insight: for every constructor, either:
- `exprValue? sub = some v` → step produces `.lit v'` → `hasAbruptCompletion (.lit v') = false` ✓
- `exprValue? sub = none` → use equation lemma → `simp [Option.bind] at hstep` → get inner step → IH gives `hasAbruptCompletion sf'.sub = false` → reconstruct

Here's the proof skeleton for the call case:

```lean
| .call f envE args =>
  simp [hasAbruptCompletion] at hac
  obtain ⟨hf_nac, henv_nac, hargs_nac⟩ := hac  -- from the Bool.or = false
  cases hfv : exprValue? f with
  | none =>
    rw [step?_call_step_func ⟨_, env, heap, trace, funcs, cs⟩ f envE args hfv] at hstep
    simp [Option.bind] at hstep
    obtain ⟨t', sf_inner, hinner, hev_eq, hsf'_eq⟩ := hstep
    subst hev_eq hsf'_eq
    simp [hasAbruptCompletion, Flat.pushTrace, Flat.State.expr]
    exact ⟨ih _ (by omega) _ _ _ _ _ _ _ hf_nac hinner, henv_nac, hargs_nac⟩
  | some fv =>
    cases hev : exprValue? envE with
    | none =>
      rw [step?_call_step_env ⟨_, env, heap, trace, funcs, cs⟩ f envE args fv hfv hev] at hstep
      simp [Option.bind] at hstep
      obtain ⟨t', se_inner, hinner, hev_eq, hsf'_eq⟩ := hstep
      subst hev_eq hsf'_eq
      simp [hasAbruptCompletion, Flat.pushTrace, Flat.State.expr]
      exact ⟨by simp [exprValue?] at hfv; sorry, ih _ (by omega) _ _ _ _ _ _ _ henv_nac hinner, hargs_nac⟩
    | some ev =>
      -- Both values: step args or execute call. Result is .lit v → hasAbruptCompletion = false
      sorry -- value case: produces .lit, trivially non-abrupt
```

For simpler cases like `.getProp obj prop`:
```lean
| .getProp obj prop =>
  simp [hasAbruptCompletion] at hac
  cases ho : exprValue? obj with
  | none =>
    rw [step?_getProp_step_obj ⟨_, env, heap, trace, funcs, cs⟩ obj prop ho] at hstep
    simp [Option.bind] at hstep
    obtain ⟨t', so, hinner, hev_eq, hsf'_eq⟩ := hstep
    subst hev_eq hsf'_eq
    simp [hasAbruptCompletion, Flat.pushTrace, Flat.State.expr]
    exact ih _ (by omega) _ _ _ _ _ _ _ hac hinner
  | some v =>
    -- obj is a value: getProp produces .lit v, which has hasAbruptCompletion = false
    simp [step?, ho] at hstep
    -- All branches produce .lit something via pushTrace
    sorry -- should be: simp [hasAbruptCompletion, Flat.pushTrace, Flat.State.expr] after decomposition
```

Even if you leave `sorry` on value-case branches, closing the `none` (stepping) branches is HUGE progress. Get as many as you can.

## TASK 3: Same approach for NoNestedAbrupt_step_preserved (L9707)

Identical structure. NoNestedAbrupt is structural like hasAbruptCompletion.

## What NOT to work on:
- Group A (L7696-7882): PARKED
- Compound HasXInHead (L8526, L8683, L8860, L9018): needs eval context lemmas
- break/continue (L10405, L10458): needs step? error propagation
- CC anything

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
