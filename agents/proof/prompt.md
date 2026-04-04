# proof — Write step? equation lemmas in Flat/Semantics.lean, then close L9398 + L9677

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

## STATUS: ANF has 11 sorries. The #1 blocker is `have` bindings in step? preventing `split at hstep`.

## YOUR #1 TASK: Write step? equation lemmas in VerifiedJS/Flat/Semantics.lean

Insert these AFTER the existing `step?_call_consoleLog` at line 1134. The `call` case in `step?` (L428-436) recurses when funcExpr is not a value. We need equation lemmas that package this cleanly.

**IMPORTANT**: Build Flat/Semantics.lean FIRST (`lake build VerifiedJS.Flat.Semantics`) to verify these lemmas. They should be straightforward since `simp [step?]` reduces `have` (which is syntactic `let`) bindings.

### Lemma 1: call stepping funcExpr
```lean
@[simp] theorem step?_call_step_func (s : State) (f envE : Expr) (args : List Expr)
    (hf : exprValue? f = none) :
    step? { s with expr := .call f envE args } =
      (step? { s with expr := f }).bind fun (t, sf) =>
        some (t, pushTrace { s with expr := .call sf.expr envE args, env := sf.env, heap := sf.heap } t) := by
  simp [step?, hf]
```

### Lemma 2: call stepping envExpr
```lean
@[simp] theorem step?_call_step_env (s : State) (f envE : Expr) (args : List Expr)
    (hf : exprValue? f = some fv) (he : exprValue? envE = none) :
    step? { s with expr := .call f envE args } =
      (step? { s with expr := envE }).bind fun (t, se) =>
        some (t, pushTrace { s with expr := .call f se.expr args, env := se.env, heap := se.heap } t) := by
  simp [step?, hf, he]
```

### Lemma 3: newObj stepping funcExpr
```lean
@[simp] theorem step?_newObj_step_func (s : State) (f envE : Expr) (args : List Expr)
    (hf : exprValue? f = none) :
    step? { s with expr := .newObj f envE args } =
      (step? { s with expr := f }).bind fun (t, sf) =>
        some (t, pushTrace { s with expr := .newObj sf.expr envE args, env := sf.env, heap := sf.heap } t) := by
  simp [step?, hf]
```

### Lemma 4: getEnv stepping envExpr
```lean
@[simp] theorem step?_getEnv_step_env (s : State) (envE : Expr) (idx : Nat)
    (he : exprValue? envE = none) :
    step? { s with expr := .getEnv envE idx } =
      (step? { s with expr := envE }).bind fun (t, se) =>
        some (t, pushTrace { s with expr := .getEnv se.expr idx, env := se.env, heap := se.heap } t) := by
  simp [step?, he]
```

**TEST**: Use `lean_multi_attempt` on Lemma 1 first. If `simp [step?]` doesn't close it, try:
- `unfold step?; simp [hf]`
- `unfold step?; dsimp; split <;> simp_all`
- `unfold step?; rfl` (unlikely but try)

## TASK 2: Once equation lemmas build, close L9398 (hasAbruptCompletion_step_preserved)

With the equation lemmas, rewrite the `call` case:
```lean
| call f fenv args =>
  simp [hasAbruptCompletion] at hac
  cases hf : exprValue? f with
  | none =>
    rw [step?_call_step_func _ _ _ _ hf] at hstep
    simp [Option.bind] at hstep
    obtain ⟨t', sf', hinner, heq⟩ := hstep
    -- Use the IH: call sub-expression preserves non-abruptness
    sorry -- structured sub-sorry
  | some fv => sorry -- step env or args
```

Even if the inner IH sorry remains, decomposing the monolithic sorry into per-branch sub-sorries is progress.

## TASK 3: Close L9677 (NoNestedAbrupt_step_preserved) using same strategy

## What NOT to work on:
- Group A (L7696-7882): PARKED
- Compound HasXInHead (L8526, L8683, L8860, L9018): needs eval context lemmas
- break/continue (L10375, L10428): needs step? error propagation
- CC anything

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
