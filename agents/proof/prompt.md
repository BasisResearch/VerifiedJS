# proof — Write step? equation lemmas, then uncomment hasAbruptCompletion/NoNestedAbrupt proofs

## RULES
- Edit: ANFConvertCorrect.lean AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build EndToEnd: `lake build VerifiedJS.Proofs.EndToEnd`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.9GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: ANF has 25 sorries. hasAbruptCompletion + NoNestedAbrupt proofs are blocked by `have` bindings in step?

## THE BLOCKER: `have` bindings in Flat.step?

The `call`, `newObj`, `getEnv` cases in `Flat.step?` (Flat/Semantics.lean) use `have : Expr.depth target < Expr.depth s.expr := by ...` for termination proofs. When you `unfold Flat.step? at hstep`, these `have` bindings remain in the hypothesis and `split at hstep` cannot decompose through them.

## YOUR #1 TASK: Write step? equation lemmas in Flat/Semantics.lean

Write equation lemmas that pre-package each branch of step? for call/newObj/getEnv WITHOUT exposing `have` bindings. These already exist for some cases (see `step?_call_closure` at L1106, `step?_newObj_allValues` at L1948).

**You need to add these lemmas near those existing ones:**

### For call — stepping funcExpr:
```lean
@[simp] theorem step?_call_step_func {s : State} {f envE : Expr} {args : List Expr}
    (hexp : s.expr = .call f envE args) (hf : exprValue? f = none) :
    step? s = (step? { s with expr := f }).bind fun (t, sf) =>
      some (t, pushTrace { s with expr := .call sf.expr envE args, env := sf.env, heap := sf.heap } t) := by
  subst hexp; simp [step?, hf]
```

### For call — stepping envExpr:
```lean
@[simp] theorem step?_call_step_env {s : State} {f envE : Expr} {args : List Expr} {fv : Value}
    (hexp : s.expr = .call f envE args) (hf : exprValue? f = some fv) (he : exprValue? envE = none) :
    step? s = (step? { s with expr := envE }).bind fun (t, se) =>
      some (t, pushTrace { s with expr := .call f se.expr args, env := se.env, heap := se.heap } t) := by
  subst hexp; simp [step?, hf, he]
```

### For call — stepping an arg:
```lean
@[simp] theorem step?_call_step_arg {s : State} {f envE : Expr} {args done remaining : List Expr} {target : Expr} {fv ev : Value}
    (hexp : s.expr = .call f envE args) (hf : exprValue? f = some fv) (he : exprValue? envE = some ev)
    (hvals : valuesFromExprList? args = none) (hfn : firstNonValueExpr args = some (done, target, remaining)) :
    step? s = (step? { s with expr := target }).bind fun (t, sa) =>
      some (t, pushTrace { s with expr := .call f envE (done ++ [sa.expr] ++ remaining), env := sa.env, heap := sa.heap } t) := by
  subst hexp; simp [step?, hf, he, hvals, hfn]
```

### Same pattern for newObj and getEnv:
```lean
-- newObj stepping funcExpr
@[simp] theorem step?_newObj_step_func {s : State} {f envE : Expr} {args : List Expr}
    (hexp : s.expr = .newObj f envE args) (hf : exprValue? f = none) :
    step? s = (step? { s with expr := f }).bind fun (t, sf) =>
      some (t, pushTrace { s with expr := .newObj sf.expr envE args, env := sf.env, heap := sf.heap } t) := by
  subst hexp; simp [step?, hf]

-- getEnv stepping envExpr
@[simp] theorem step?_getEnv_step_env {s : State} {envE : Expr} {idx : Nat}
    (hexp : s.expr = .getEnv envE idx) (he : exprValue? envE = none) :
    step? s = (step? { s with expr := envE }).bind fun (t, se) =>
      some (t, pushTrace { s with expr := .getEnv se.expr idx, env := se.env, heap := se.heap } t) := by
  subst hexp; simp [step?, he]
```

**IMPORTANT**: The `simp [step?]` in these lemma proofs should work because `simp` can reduce `have` bindings (they're syntactic sugar for `let`). If `simp [step?]` doesn't work, try `unfold step?; simp` or `unfold step?; dsimp; rfl`.

**TEST**: Use `lean_multi_attempt` on the first lemma before writing all of them.

## TASK 2: Once equation lemmas exist, use them in hasAbruptCompletion/NoNestedAbrupt

Once the lemmas are in Flat/Semantics.lean, the sorry cases in the block comments become:
```lean
| call f fenv args =>
  simp only [hasAbruptCompletion] at hac
  -- Now use the equation lemma instead of unfold + split:
  cases hf : exprValue? f with
  | none =>
    rw [step?_call_step_func rfl hf] at hstep
    simp [Option.bind] at hstep
    obtain ⟨t', sf', hstep_inner, hstep_eq⟩ := hstep
    -- Now hstep_inner : step? {s with expr := f} = some (t', sf')
    -- Apply IH on f (sub-expression)
    sorry -- but now STRUCTURED
  | some fv =>
    cases he : exprValue? fenv with
    | none => rw [step?_call_step_env rfl hf he] at hstep; sorry
    | some ev => ...
```

## TASK 3 (if tasks 1-2 are blocked): break/continue (L10375, L10428)

## What NOT to work on:
- Group A (L7696-7882): eval context lifting — PARKED
- If compound (L9257-9346): needs trivialChain — PARKED
- Compound throw/return/await/yield (L8526-9018): wasmspec handles these

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
