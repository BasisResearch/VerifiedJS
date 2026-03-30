# proof — STOP CC. Switch to ANF. Close break/continue/throw NOW.

## CRITICAL: MEMORY IS TIGHT (7.7GB total, no swap)
- **NEVER run `lake build VerifiedJS`** (full build). It OOMs.
- Build ONE module at a time: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building, kill stale lean processes: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **Check `pgrep -af "lake build"` first** — do NOT start a build if one is already running.

## SITUATION: ANF has been UNTOUCHED for 25 HOURS. You've only been doing CC.
- ANF: 17 sorries. ZERO progress. **This is the critical path.**
- CC: 22 sorries. You closed 2 recently. Good — but ANF is MORE important now.
- The CC structural blockers (CCState threading, forIn/forOf stubs) are NOT fixable without impl changes. Stop banging your head on those.

## YOUR JOB: Close 4 ANF sorries RIGHT NOW

### STEP 1: Integrate break/continue direct case (-2 sorries)

Replace L3423-3426 in ANFConvertCorrect.lean with this EXACT code from jsspec staging:

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
      | seq_left h => sorry -- compound case: needs normalizeExpr_break_step_sim
      | seq_right h => sorry -- compound case: needs normalizeExpr_break_step_sim
      | let_init h => sorry -- compound case: needs normalizeExpr_break_step_sim
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

**This replaces 2 monolithic sorries with 2 provable direct cases + 26 compound sub-case sorries.** The direct cases are proved. Net sorry change: -2 (down from 17 to 15, replacing 2 sorries that covered EVERYTHING with 26 sorries that only cover compound sub-cases — but the CRITICAL break_direct and continue_direct cases are PROVED).

Wait — actually the net sorry count will go UP by 24. That's wrong. Instead:

**Actually: just use the direct case + `sorry` for compound cases.** This changes 2 sorries → ~26 sorries but makes the direct case provable. However, the compound cases share a SINGLE helper theorem `normalizeExpr_break_step_sim` that will close ALL of them. So the true progress is: the `break_direct`/`continue_direct` cases are PROVED.

**DO THIS ANYWAY.** 26 fine-grained sorries are better than 2 monolithic ones. Each compound case will be closed by a single shared helper.

### STEP 2: After break/continue, try throw direct case (-0 sorries, decompose)

Similar pattern. At L3382-3392, the throw case. The structure mirrors break but uses `normalizeExpr_throw_or_k` (see `.lake/_tmp_fix/anf_throw_inversion.lean` for the HasThrowInHead inductive — but check if it's been integrated into the main file yet).

If `HasThrowInHead` is NOT in ANFConvertCorrect.lean yet, integrate it from the staging file.

### STEP 3: After throw, try return/await

L3396 (return), L3398 (yield), L3400 (await) — same pattern using HasReturnInHead/HasAwaitInHead from `.lake/_tmp_fix/anf_return_await_inversion.lean`.

## BUILD VALIDATION
After EACH edit:
```bash
pkill -f "lean.*\.lean" 2>/dev/null; sleep 5
lake build VerifiedJS.Proofs.ANFConvertCorrect 2>&1 | tail -20
```

## FILES
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw) — YOUR FOCUS
- `.lake/_tmp_fix/*.lean` (read for integration)

## DO NOT EDIT
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (NOT NOW)
- `VerifiedJS/Wasm/Semantics.lean`
- `VerifiedJS/Flat/Semantics.lean`
