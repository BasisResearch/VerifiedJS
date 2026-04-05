# proof — Prove step?_preserves_funcs + close funcs propagation sorries

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

## STATUS: You added funcs hypotheses to theorems. Now PROVE the lemma and close the sorries.

You added `hfuncs_ac`/`hfuncs_na` hypotheses to hasAbruptCompletion_step_preserved (L9453) and NoNestedAbrupt_step_preserved (L9462). Both bodies are sorry'd. You also added step?_preserves_funcs as a sorry stub at Flat/Semantics.lean L2041. This is your CRITICAL PATH.

## TASK 1: PROVE step?_preserves_funcs (Flat/Semantics.lean L2041-2043) — HIGHEST PRIORITY

This is at L2041-2043:
```lean
theorem step?_preserves_funcs (sf : Flat.State) (ev : Core.TraceEvent) (sf' : Flat.State)
    (h : step? sf = some (ev, sf')) : sf'.funcs = sf.funcs := by
  sorry
```

**HOW TO PROVE**: step? is a big match on `sf.expr`. Every branch constructs the result state with `{s with ...}` which copies funcs. The proof:

```lean
  unfold step? at h
  -- Try: split on expr, then in each branch extract that funcs is unchanged
  -- The key insight: every branch either returns none (contradiction with h)
  -- or returns some (ev, {s with expr := ..., heap := ..., ...}) where funcs is not set
  -- So sf'.funcs = sf.funcs by the {s with ...} update
  split at h
  all_goals (try simp_all [pushTrace])
  -- If simp_all doesn't close all goals, handle remaining manually:
  -- each remaining case: extract sf' from h, show .funcs field is unchanged
  all_goals (try { simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl })
```

If `split at h` creates too many goals and times out, try `lean_multi_attempt` with:
- `["simp [step?, pushTrace] at h ⊢; split at h <;> simp_all"]`
- `["unfold step? at h; cases sf.expr <;> simp_all [pushTrace]"]`

Use `set_option maxHeartbeats 800000 in` if needed.

Once proved, build Flat: `lake build VerifiedJS.Flat.Semantics`

## TASK 2: Close L9482 (NoNestedAbrupt_steps_preserved funcs propagation)

At L9482:
```lean
exact ih (NoNestedAbrupt_step_preserved _ _ _ hna hfuncs_na hfuncs_ac hstep_eq) sorry sorry
```

The two `sorry` args need `hfuncs_na` and `hfuncs_ac` for the stepped state. With step?_preserves_funcs proved:
```lean
    have hfuncs_eq := step?_preserves_funcs _ _ _ hstep_eq
    exact ih (NoNestedAbrupt_step_preserved _ _ _ hna hfuncs_na hfuncs_ac hstep_eq)
      (fun i fd h => hfuncs_na i fd (hfuncs_eq ▸ h))
      (fun i fd h => hfuncs_ac i fd (hfuncs_eq ▸ h))
```

## TASK 3: Close L10760-10761 (program funcs invariants in anfConvert_steps_star)

At L10760-10761:
```lean
have hfuncs_na_sf : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → NoNestedAbrupt fd.body := sorry
have hfuncs_ac_sf : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → hasAbruptCompletion fd.body = false := sorry
```

These should come from `hrel : ANF_SimRel s t sa sf`. Check what ANF_SimRel says about funcs. Use `lean_hover_info` on ANF_SimRel. If it has a funcs field, extract it.

If ANF_SimRel doesn't carry funcs invariants, add them as hypotheses to anfConvert_steps_star's caller and thread through. The key insight: sf.funcs is set during ANF.convert from the source program, and step? preserves funcs (Task 1). So the invariant holds throughout.

**Approach**: Add hypotheses to anfConvert_steps_star (L9487):
```lean
(hfuncs_na : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → NoNestedAbrupt fd.body)
(hfuncs_ac : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → hasAbruptCompletion fd.body = false)
```
Then in the `| tail` case, propagate using step?_preserves_funcs through hfsteps1. You may need a Steps_preserves_funcs wrapper:
```lean
theorem Steps_preserves_funcs {sf sf' : Flat.State} {evs : List Core.TraceEvent}
    (h : Flat.Steps sf evs sf') : sf'.funcs = sf.funcs := by
  induction h with
  | refl => rfl
  | tail hstep _ ih => obtain ⟨h⟩ := hstep; exact (step?_preserves_funcs _ _ _ h).symm ▸ ih
```

## TASK 4: Re-prove hasAbruptCompletion_step_preserved body (L9460)

The body is sorry'd. It was previously proved but needs re-proof with `hfuncs_ac` threaded through. This is a large case split on the expr. Use `lean_goal` at L9460 to see what's needed.

**Pattern**: unfold step? at hstep, split on expr cases, in each case show hasAbruptCompletion of the result expr is false. The hfuncs_ac hypothesis handles the funcDef/call cases where a function body might be looked up.

## PRIORITY ORDER
1. step?_preserves_funcs — unblocks everything
2. L9482 — quick 2-line fix once Task 1 done
3. L10760-10761 — threading hypotheses
4. L9460 — re-prove hasAbruptCompletion_step_preserved

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
