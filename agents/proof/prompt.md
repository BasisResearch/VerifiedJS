# proof — ANF ONLY. DO NOT TOUCH CC.

## ABSOLUTE RULE: YOU MAY ONLY EDIT ANFConvertCorrect.lean THIS RUN
- **DO NOT** open, read, build, or edit ClosureConvertCorrect.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -u proof -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## MEMORY: 7.7GB total, NO swap
- Build ONE module. Kill stale lean procs first.

## YOUR EXACT TASK: Close break/continue (-2 net sorries, but decompose is OK)

### Step 1: Replace L3427-3430 with this EXACT code

The break case at L3427-3428 currently reads:
```
  | «break» label =>
    sorry -- break: both produce .error, needs normalizeExpr inversion
```

Replace BOTH break (L3427-3428) and continue (L3429-3430) with this code. This follows the EXACT same pattern as the `labeled` case at L3405-3426 above it.

```lean
  | «break» label =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    obtain ⟨rfl, rfl⟩ := hstep_eq
    have hnorm_simp : (ANF.normalizeExpr sf.expr k).run n = .ok (.break label, m) := by
      simp only [ANF.State.expr] at hnorm; exact hnorm
    have hk_no_break : ∀ (t : ANF.Trivial) (n' m' : Nat),
        (k t).run n' = .ok (.break label, m') → False := by
      intro t n' m' hkt
      obtain ⟨m'', htriv⟩ := hk_triv t n'
      rw [htriv] at hkt; cases hkt
    rcases ANF.normalizeExpr_break_or_k sf.expr k label n m hnorm_simp with
      hbreak | ⟨t_k, n_k, m_k, hkt⟩
    · cases hbreak with
      | break_direct =>
        have hflat_step : Flat.step? sf =
          some (.error ("break:" ++ (label.getD "")),
                Flat.pushTrace { sf with expr := .lit .undefined } (.error ("break:" ++ (label.getD "")))) := by
          have : sf = { sf with expr := .break label } := by cases sf; simp_all
          rw [this]; simp [Flat.step?]
        refine ⟨Flat.pushTrace { sf with expr := .lit .undefined } (.error ("break:" ++ (label.getD ""))),
                [.error ("break:" ++ (label.getD ""))],
                Flat.Steps.tail (Flat.Step.mk hflat_step) (Flat.Steps.refl _), ?_, ?_, ?_⟩
        · simp [observableTrace_error, observableTrace_nil]
        · refine ⟨?_, ?_, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
          · simp [Flat.pushTrace]; rw [hheap]
          · simp [Flat.pushTrace]; rw [henv]
          · simp [Flat.pushTrace, observableTrace_append, observableTrace_error, observableTrace_nil]
            rw [htrace]
          · exact ANF.normalizeExpr_lit_undefined_trivial n
        · simp [Flat.pushTrace]; intro x hfx; cases hfx
      | seq_left h => sorry
      | seq_right h => sorry
      | let_init h => sorry
      | getProp_obj h => sorry
      | setProp_obj h => sorry
      | setProp_val h => sorry
      | binary_lhs h => sorry
      | binary_rhs h => sorry
      | unary_arg h => sorry
      | typeof_arg h => sorry
      | deleteProp_obj h => sorry
      | assign_val h => sorry
      | call_func h => sorry
      | call_env h => sorry
    · exact absurd hkt (hk_no_break t_k n_k m_k)
  | «continue» label =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    obtain ⟨rfl, rfl⟩ := hstep_eq
    have hnorm_simp : (ANF.normalizeExpr sf.expr k).run n = .ok (.continue label, m) := by
      simp only [ANF.State.expr] at hnorm; exact hnorm
    have hk_no_cont : ∀ (t : ANF.Trivial) (n' m' : Nat),
        (k t).run n' = .ok (.continue label, m') → False := by
      intro t n' m' hkt
      obtain ⟨m'', htriv⟩ := hk_triv t n'
      rw [htriv] at hkt; cases hkt
    rcases ANF.normalizeExpr_continue_or_k sf.expr k label n m hnorm_simp with
      hcont | ⟨t_k, n_k, m_k, hkt⟩
    · cases hcont with
      | continue_direct =>
        have hflat_step : Flat.step? sf =
          some (.error ("continue:" ++ (label.getD "")),
                Flat.pushTrace { sf with expr := .lit .undefined } (.error ("continue:" ++ (label.getD "")))) := by
          have : sf = { sf with expr := .continue label } := by cases sf; simp_all
          rw [this]; simp [Flat.step?]
        refine ⟨Flat.pushTrace { sf with expr := .lit .undefined } (.error ("continue:" ++ (label.getD ""))),
                [.error ("continue:" ++ (label.getD ""))],
                Flat.Steps.tail (Flat.Step.mk hflat_step) (Flat.Steps.refl _), ?_, ?_, ?_⟩
        · simp [observableTrace_error, observableTrace_nil]
        · refine ⟨?_, ?_, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
          · simp [Flat.pushTrace]; rw [hheap]
          · simp [Flat.pushTrace]; rw [henv]
          · simp [Flat.pushTrace, observableTrace_append, observableTrace_error, observableTrace_nil]
            rw [htrace]
          · exact ANF.normalizeExpr_lit_undefined_trivial n
        · simp [Flat.pushTrace]; intro x hfx; cases hfx
      | seq_left h => sorry
      | seq_right h => sorry
      | let_init h => sorry
      | getProp_obj h => sorry
      | setProp_obj h => sorry
      | setProp_val h => sorry
      | binary_lhs h => sorry
      | binary_rhs h => sorry
      | unary_arg h => sorry
      | typeof_arg h => sorry
      | deleteProp_obj h => sorry
      | assign_val h => sorry
      | call_func h => sorry
      | call_env h => sorry
    · exact absurd hkt (hk_no_cont t_k n_k m_k)
```

### Step 2: Verify build
```bash
pkill -u proof -f "lean.*\.lean" 2>/dev/null; sleep 5
lake build VerifiedJS.Proofs.ANFConvertCorrect 2>&1 | tail -30
```

### Step 3: If break/continue builds, try throw (L3396)

The throw case at L3385-3396 already has good structure. The `all_goals sorry` at L3396 covers 2 sub-cases. Check if `HasThrowInHead` is defined (grep for it). If so, use it. If not, see `.lake/_tmp_fix/anf_throw_inversion.lean` for the staging.

### Step 4: Try return (L3400), yield (L3402), await (L3404)

These follow the same pattern as throw. Check `.lake/_tmp_fix/anf_return_await_inversion.lean`.

## VERIFICATION CHECKLIST
- [ ] Edit ONLY ANFConvertCorrect.lean
- [ ] Build passes: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- [ ] Log to agents/proof/log.md with sorry count before/after
- [ ] DO NOT touch ClosureConvertCorrect.lean

## FILES
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw) — YOUR ONLY FILE
- `.lake/_tmp_fix/*.lean` (read for reference)
