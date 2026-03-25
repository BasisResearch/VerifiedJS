# proof — Close ANF L1499 (trivial chain in seq4 context)

## Build ONLY your module
```
bash scripts/lake_build_concise.sh VerifiedJS.Proofs.ANFConvertCorrect
```

## Use MCP BEFORE editing
- lean_goal to see state
- lean_multi_attempt to test tactics
- lean_diagnostic_messages for errors

## TASK: Close the sorry at ANFConvertCorrect.lean L1499

### Context
The sorry is inside `anfConvert_halt_star_aux`, in the `| seq c1a c1b =>` branch. The expression is:
```
sf.expr = .seq (.seq (.seq (.seq (.seq c1a c1b) c2) d) a2) b
```
where `c1 = .seq c1a c1b` is a **trivial chain** (`isTrivialChain c1 = true`).

The sibling branches (lit, var, this) are already proved by manually constructing 0-2 Flat steps. This case needs to do the same but recursively.

### Target
Show that sf can step (silently) to some `sf_target` where:
- `sf_target.expr = .seq (.seq (.seq c2 d) a2) b`
- `sf_target.env = sf.env`, `sf_target.heap = sf.heap`
- Then apply `ih` on `sf_target` (depth decreases)

### Strategy: add helper lemma BEFORE the main theorem

Add this helper around line 773 (after `step?_seq_ctx`):

```lean
/-- exprValue? of any seq is none (seq is never a value). -/
private theorem exprValue?_seq (a b : Flat.Expr) : Flat.exprValue? (.seq a b) = none := by
  simp [Flat.exprValue?]

/-- exprValue? of var/this is none (they are not values). -/
private theorem exprValue?_var (n : String) : Flat.exprValue? (.var n) = none := by
  simp [Flat.exprValue?]

private theorem exprValue?_this : Flat.exprValue? .this = none := by
  simp [Flat.exprValue?]

/-- A trivial chain evaluates to a literal via silent Flat steps.
    env, heap, funcs, callStack unchanged. -/
private theorem trivialChain_eval (n : Nat) (e : Flat.Expr) (s : Flat.State)
    (htc : isTrivialChain e = true)
    (hsf : s.expr = e)
    (hcost : trivialChainCost e ≤ n) :
    ∃ (v : Core.Value) (evs : List Core.TraceEvent) (s' : Flat.State),
      Flat.Steps s evs s' ∧ s'.expr = .lit v ∧
      s'.env = s.env ∧ s'.heap = s.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      observableTrace evs = [] := by
  induction n generalizing e s with
  | zero =>
    -- cost ≤ 0 means e = .lit v (only lit has cost 0 among trivials)
    cases e with
    | lit v => exact ⟨v, [], s, .refl, hsf, rfl, rfl, rfl, rfl, rfl⟩
    | var _ | «this» | seq _ _ => simp [trivialChainCost] at hcost
    | _ => simp [isTrivialChain] at htc
  | succ n ih =>
    cases e with
    | lit v => exact ⟨v, [], s, .refl, hsf, rfl, rfl, rfl, rfl, rfl⟩
    | var name =>
      -- step? resolves var to a value
      have hstep : ∃ val, Flat.step? s = some (.silent, { s with
          expr := .lit val, trace := s.trace ++ [.silent] }) := by
        rw [show s = { s with expr := .var name } from by cases s; simp_all]
        unfold Flat.step? Flat.exprValue?; unfold Flat.step?
        cases s.env.lookup name with
        | some v => exact ⟨v, rfl⟩
        | none => exact ⟨.undefined, rfl⟩
      obtain ⟨val, hstep⟩ := hstep
      exact ⟨val, [.silent], _, .tail ⟨hstep⟩ .refl, rfl, rfl, rfl, rfl, rfl,
        by simp [observableTrace]⟩
    | «this» =>
      -- Same pattern as var but with "this"
      have hstep : ∃ val, Flat.step? s = some (.silent, { s with
          expr := .lit val, trace := s.trace ++ [.silent] }) := by
        rw [show s = { s with expr := .this } from by cases s; simp_all]
        unfold Flat.step? Flat.exprValue?; unfold Flat.step?
        cases s.env.lookup "this" with
        | some v => exact ⟨v, rfl⟩
        | none => exact ⟨.undefined, rfl⟩
      obtain ⟨val, hstep⟩ := hstep
      exact ⟨val, [.silent], _, .tail ⟨hstep⟩ .refl, rfl, rfl, rfl, rfl, rfl,
        by simp [observableTrace]⟩
    | seq ea eb =>
      simp [isTrivialChain] at htc
      -- First: evaluate ea to a literal
      have hcost_a : trivialChainCost ea ≤ n := by
        simp [trivialChainCost] at hcost; omega
      obtain ⟨va, evs_a, s_a, hsteps_a, hlit_a, henv_a, hheap_a, hfuncs_a, hcs_a, hobs_a⟩ :=
        ih ea { s with expr := ea } htc.1 rfl hcost_a
      -- Now s_a.expr = .lit va. One step consumes .seq (.lit va) eb → eb
      -- ... (use step?_seq_ctx to lift ea steps through one .seq layer)
      -- Then evaluate eb
      -- This is the recursive structure — use ih on eb
      sorry
    | _ => simp [isTrivialChain] at htc
```

The `| seq ea eb =>` case in `trivialChain_eval` needs:
1. Use `step?_seq_ctx` to lift the `ea` evaluation through the `.seq ea eb` wrapping
2. After ea → .lit va, one step consumes `.seq (.lit va) eb` → `eb`
3. Use `ih` on `eb`

Then, add a SECOND helper to lift `trivialChain_eval` through 4 layers of seq context:

```lean
/-- Lift trivialChain_eval through nested seq context:
    if tc evaluates to .lit v, then .seq(.seq(.seq(.seq tc c2) d) a2) b
    steps to .seq(.seq(.seq(.seq (.lit v) c2) d) a2) b -/
private theorem trivialChain_eval_seq4 (s : Flat.State)
    (tc c2 d a2 b : Flat.Expr)
    (htc : isTrivialChain tc = true)
    (hsf : s.expr = .seq (.seq (.seq (.seq tc c2) d) a2) b) :
    ∃ (v : Core.Value) (evs : List Core.TraceEvent) (s' : Flat.State),
      Flat.Steps s evs s' ∧
      s'.expr = .seq (.seq (.seq (.seq (.lit v) c2) d) a2) b ∧
      s'.env = s.env ∧ s'.heap = s.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      observableTrace evs = [] := by
  sorry  -- Use trivialChain_eval on the inner tc, then step?_seq_ctx 4 times to lift
```

### Applying the helpers at L1499
Once you have `trivialChain_eval_seq4`, the sorry at L1499 becomes:
```lean
-- Get tc steps: c1 = .seq c1a c1b evaluates to .lit v
obtain ⟨v, evs_tc, sf_tc, hsteps_tc, hlit_tc, henv_tc, hheap_tc, _, _, hobs_tc⟩ :=
  trivialChain_eval_seq4 sf (Flat.Expr.seq c1a c1b) c2 d a2 b
    (by simp [isTrivialChain]; exact ⟨htc_a, htc_b⟩)  -- htc.1, htc.2
    (by rw [hsf, ha, ha1, hc, hc1])
-- One more step: .seq(.seq(.seq(.seq (.lit v) c2) d) a2) b → .seq(.seq(.seq c2 d) a2) b
-- (same pattern as the lit case at L1392)
-- Then apply ih
```

### Priority
1. First try to close L1499 with `trivialChain_eval_seq4` (even if the helper itself has sorry initially)
2. If that works structurally, close the helper sorries
3. Do NOT touch CC or other files

## Log progress to agents/proof/log.md
