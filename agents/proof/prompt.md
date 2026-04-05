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

## STATUS: Infrastructure DONE. Now close L9460 + L9469.

step?_preserves_funcs, Steps_preserves_funcs, L9482, L10760-10761 are ALL PROVED. The only remaining work is the two big case-split theorems.

## TASK 1: PROVE hasAbruptCompletion_step_preserved (L9460) — HIGHEST PRIORITY

Signature at L9453-9460. This is a case split on ALL 31 Flat.Expr constructors.

**EXACT APPROACH — use lean_multi_attempt first:**

At L9460, try this tactic block:
```lean
  cases e with
  | lit => simp [Flat.step?] at hstep
  | var => simp [Flat.step?] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [hasAbruptCompletion]
  | this => simp [Flat.step?] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [hasAbruptCompletion]
  | seq a b =>
    simp [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
    simp [Flat.step?] at hstep
    split at hstep
    · -- a is value: step to b. Use hac.2
      obtain ⟨_, rfl⟩ := hstep; exact hac.2
    · -- a steps: result is seq a' b
      obtain ⟨_, _, _, rfl⟩ := hstep
      simp [hasAbruptCompletion, Bool.or_eq_false_iff]
      sorry -- may need IH pattern
  | «break» => simp [hasAbruptCompletion] at hac
  | «continue» => simp [hasAbruptCompletion] at hac
  | «return» => simp [hasAbruptCompletion] at hac
  | throw => simp [hasAbruptCompletion] at hac
  | _ => sorry
```

The key pattern for each eval-context constructor (seq, let, if, assign, etc.):
1. `simp [hasAbruptCompletion, Bool.or_eq_false_iff] at hac` to decompose hac
2. `simp [Flat.step?] at hstep` then `split at hstep` for value/non-value sub-cases
3. Value case: result expr has hasAbruptCompletion = false from hac components
4. Step case: result wraps sub-result in same constructor, hasAbruptCompletion propagates

For `call` with all values + funcs lookup: `exact hfuncs_ac _ _ ‹_›` or similar.

**IMPORTANT**: Use `set_option maxHeartbeats 3200000 in` before the theorem. This will be large.

If the full case split is too big, decompose into helper lemmas per constructor group.

## TASK 2: PROVE NoNestedAbrupt_step_preserved (L9469)

Same structure as Task 1 but cases on `sf.expr` with `NoNestedAbrupt` inversion.

```lean
  obtain ⟨e, env, heap, trace, funcs, cs⟩ := sf
  simp at hna hstep ⊢
  cases hna with
  | lit => simp [Flat.step?] at hstep; ...
  | seq hna_a hna_b => ...
  -- etc for each NoNestedAbrupt constructor
```

For each case, show sf'.expr is still NoNestedAbrupt. Use hfuncs_na for call/funcDef.

## TASK 3: Close L9866 + L9919 (break/continue) — IF TIME

## PRIORITY ORDER
1. hasAbruptCompletion_step_preserved (L9460) — most impactful
2. NoNestedAbrupt_step_preserved (L9469) — same technique
3. L9866 + L9919 — break/continue

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
