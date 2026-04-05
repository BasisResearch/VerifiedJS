# proof — Close L11680/L11681 (program funcs invariant) + L10402 (step propagation)

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

## TASK 1: Close L11680 + L11681 (program funcs invariant) — HIGHEST PRIORITY

These two sorries at L11680-11681 in `anfConvert_steps_star` are:
```lean
have hfuncs_na_sf : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → NoNestedAbrupt fd.body := sorry -- from program invariant
have hfuncs_ac_sf : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → hasAbruptCompletion fd.body = false := sorry -- from program invariant
```

These need to come from the PROGRAM-LEVEL invariant. The function table `sf.funcs` is populated during `ANF.convert` from the source program. Since we're proving correctness of compilation, all function bodies in the compiled program should satisfy NoNestedAbrupt and ¬hasAbruptCompletion.

### Approach
1. Add hypotheses to `anfConvert_steps_star` (L11662):
```lean
(hfuncs_na : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → NoNestedAbrupt fd.body)
(hfuncs_ac : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → hasAbruptCompletion fd.body = false)
```

2. In the `| tail` case, after getting `sf2` from `anfConvert_step_star`, you need to show the invariant propagates. Key insight: **Flat.step? does NOT change funcs**. Verify with `lean_hover_info` on Flat.step? — the funcs field should be preserved. If so:
```lean
have hfuncs_eq : sf2.funcs = sf.funcs := Flat.Steps_preserves_funcs hfsteps1
-- Then: hfuncs_na_sf2 follows from hfuncs_na + hfuncs_eq
```

If `Flat.Steps_preserves_funcs` doesn't exist, prove it: each step preserves funcs (check Flat.step? definition), then induct on Steps.

3. Replace `sorry` at L11680-11681 with the actual hypotheses.

4. Update the caller of `anfConvert_steps_star` (likely in EndToEnd.lean) to provide the funcs invariants. This should be derivable from the compilation process.

## TASK 2: Close L10402 (NoNestedAbrupt_steps_preserved propagation)

At L10402:
```lean
exact ih (NoNestedAbrupt_step_preserved _ _ _ hna hfuncs_na hfuncs_ac hstep_eq) sorry sorry
```

The two `sorry` args need `hfuncs_na` and `hfuncs_ac` for the STEPPED state `sf'`. Same insight: step? preserves funcs, so:
```lean
have hfuncs_eq : sf'.funcs = sf.funcs := by
  -- Extract from hstep_eq that funcs is unchanged
  sorry -- or prove Flat.step?_preserves_funcs
exact ih (NoNestedAbrupt_step_preserved _ _ _ hna hfuncs_na hfuncs_ac hstep_eq)
  (fun i fd h => hfuncs_na i fd (hfuncs_eq ▸ h))
  (fun i fd h => hfuncs_ac i fd (hfuncs_eq ▸ h))
```

Actually, if you can prove `Flat.step?_preserves_funcs` as a general lemma, it solves both tasks.

### Proving Flat.step?_preserves_funcs
```lean
theorem Flat.step?_preserves_funcs (sf : Flat.State) (ev : Core.TraceEvent) (sf' : Flat.State)
    (h : Flat.step? sf = some (ev, sf')) : sf'.funcs = sf.funcs := by
  -- Unfold step? and case split on expr
  simp [Flat.step?] at h
  -- Each case should show funcs unchanged
  sorry -- fill in
```

This is likely provable by inspection of step? — in every branch, the output state copies funcs from the input.

## TASK 3: Continue closing ANF sorry cases (IF TIME)

After Tasks 1-2, the remaining ANF sorries are:
- L7701-7887 (7): eval context lifting — PARKED
- L8531-9023 (7): compound HasX cases — PARKED
- L9050: let step sim (wasmspec)
- L9140, 9152: while step sim (wasmspec)
- L9333-9407 (4): if compound
- L9451: tryCatch step sim
- L10783: break/continue compound — needs eval context

Focus on what's achievable: the funcs invariant propagation (Tasks 1-2) closes 4 sorries and unblocks the end-to-end composition.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
