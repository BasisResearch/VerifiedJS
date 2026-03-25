# proof — ANF IS YOUR PRIORITY

ALL 6 real CC sorries are **architecturally blocked** by heap address divergence:
- Flat `makeEnv` allocates env objects to the same heap as regular objects
- After any function definition, `sf.heap.objects.size > sc.heap.objects.size`
- So `objectLit`/`arrayLit`/`newObj` allocate at different addresses in Core vs Flat
- `convertValue (.object addr) = .object addr` but the addrs don't match
- This affects ALL CC cases: objectLit, arrayLit, newObj, call, functionDef, captured-var

**DO NOT work on CC.** It needs an architectural fix (separate env heap or address mapping).

## TASK 1: Close ANF L1365 — left-spine flattening lemma

At L1365, `c1 = .seq _ _` inside nested seq. Need a lemma that says any trivial chain (composed of lit/var/this/seq) reduces to a literal in finitely many silent steps.

Define this helper and lemma in ANFConvertCorrect.lean:

```lean
/-- A trivial chain is an expr composed only of .lit, .var, .this, .seq of trivial chains. -/
private def isTrivialChain : Flat.Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .this => true
  | .seq a b => isTrivialChain a && isTrivialChain b
  | _ => false

/-- A trivial chain always evaluates to a value in finitely many silent Flat steps,
    provided all variables in it are bound in the environment. -/
private theorem trivialChain_steps (e : Flat.Expr) (env : Flat.Env) (heap : Core.Heap)
    (trace : List Core.TraceEvent) (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (htc : isTrivialChain e = true)
    (henv : ∀ name, e.hasVar name → env.lookup name ≠ none) :
    ∃ v (sf' : Flat.State) (n : Nat),
      Flat.StepsN ⟨e, env, heap, trace, funcs, cs⟩ n sf' ∧
      sf'.expr = .lit v ∧
      sf'.heap = heap ∧
      sf'.trace = trace := by
  induction e with
  | lit v => exact ⟨v, _, 0, .refl, rfl, rfl, rfl⟩
  | var name =>
    simp [isTrivialChain] at htc
    have hsome := henv name (by simp [Flat.Expr.hasVar])
    obtain ⟨fv, hfv⟩ := Option.ne_none_iff_exists.mp hsome
    -- Flat.step? (.var name) with env.lookup name = some fv produces (.lit fv, .silent)
    exact ⟨fv, _, 1, .step (by simp [Flat.step?, hfv]) .refl, rfl, rfl, rfl⟩
  | this =>
    -- Flat.step? (.this) with env.lookup "this" = some v produces (.lit v, .silent)
    have hsome := henv "this" (by simp [Flat.Expr.hasVar])
    obtain ⟨fv, hfv⟩ := Option.ne_none_iff_exists.mp hsome
    exact ⟨fv, _, 1, .step (by simp [Flat.step?, hfv]) .refl, rfl, rfl, rfl⟩
  | seq a b iha ihb =>
    simp [isTrivialChain] at htc
    obtain ⟨hta, htb⟩ := htc
    -- First reduce a to .lit va
    obtain ⟨va, sfa', na, hstepsa, hexpra, hheapa, htracea⟩ := iha hta (by
      intro name hmem; exact henv name (by simp [Flat.Expr.hasVar]; left; exact hmem))
    -- Then .seq (.lit va) b steps to b (1 step)
    -- Then reduce b to .lit vb
    obtain ⟨vb, sfb', nb, hstepsb, hexprb, hheapb, htraceb⟩ := ihb htb (by
      intro name hmem; exact henv name (by simp [Flat.Expr.hasVar]; right; exact hmem))
    -- Combine: na steps (a→lit) + contextual lifting into .seq + 1 step (seq-lit) + nb steps (b→lit)
    sorry -- combine the step sequences with contextual lifting
  | _ => simp [isTrivialChain] at htc
```

The `seq` case needs contextual lifting: if `a →* .lit va` then `.seq a b →* .seq (.lit va) b`. You need:

```lean
/-- Contextual lifting: steps inside .seq left position. -/
private theorem seq_left_steps (a b : Flat.Expr) (env : Flat.Env) (heap : Core.Heap)
    (trace : List Core.TraceEvent) (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (v : Flat.Value) (sf' : Flat.State) (n : Nat)
    (h : Flat.StepsN ⟨a, env, heap, trace, funcs, cs⟩ n sf' ∧ sf'.expr = .lit v) :
    ∃ sf'', Flat.StepsN ⟨.seq a b, env, heap, trace, funcs, cs⟩ n sf'' ∧
      sf''.expr = .seq (.lit v) b := by
  sorry -- induction on n, using .seq stepping rule for each sub-step
```

Use `lean_goal` at L1365 first to see the exact goal state, then write these helpers.

## TASK 2: ANF L106 — anfConvert_step_star

This is the main theorem. The proof architecture is in the comments at L107-L142. Start with the `intro` and `sorry`-skeleton:

```lean
  intro sa sf ev sa' hrel hwf hstep
  -- Strong induction on sf.expr.depth
  obtain ⟨scope, envVar, envMap, st, st', hconv⟩ := hrel.2.2.2.2.2
  -- Case split on sf.expr
  match hsf : sf.expr with
  | .lit v => sorry     -- Case 3: terminal, 0 Flat steps
  | .var name => sorry  -- Case 4: 1 Flat step → lit → Case 3
  | .seq a b => sorry   -- Case 1/5: seq-lit or seq-compound
  | _ => sorry          -- Case 6: compound expression
```

Focus on Case 1 (`.seq (.lit v) b`) first — it's the simplest and most common.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- lean_goal + lean_multi_attempt BEFORE editing
- Log to agents/proof/log.md
- DO NOT touch CC — it's architecturally blocked
