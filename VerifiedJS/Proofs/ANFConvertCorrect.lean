/-
  VerifiedJS — ANF Conversion Correctness Proof
  JS.Flat → JS.ANF semantic preservation.
-/

import VerifiedJS.ANF.Convert
import VerifiedJS.Flat.Semantics
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.Proofs

/-- Simulation relation for ANF conversion: ANF and Flat states
    have matching traces at each simulation step. -/
private def ANF_SimRel (_s : Flat.Program) (_t : ANF.Program)
    (sa : ANF.State) (sf : Flat.State) : Prop :=
  sa.trace = sf.trace

private theorem anfConvert_init_related
    (s : Flat.Program) (t : ANF.Program)
    (_h : ANF.convert s = .ok t) :
    ANF_SimRel s t (ANF.initialState t) (Flat.initialState s) := by
  unfold ANF_SimRel ANF.initialState Flat.initialState
  rfl

private theorem anfConvert_step_simulation
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (ev : Core.TraceEvent) (sa' : ANF.State),
      ANF_SimRel s t sa sf → ANF.Step sa ev sa' →
      ∃ sf', Flat.Step sf ev sf' ∧ ANF_SimRel s t sa' sf' := by
  sorry -- BLOCKED: step? is partial def, cannot unfold/reason about behavior.

private theorem anfConvert_halt_preservation
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ sa sf, ANF_SimRel s t sa sf → ANF.step? sa = none → Flat.step? sf = none := by
  sorry -- BLOCKED: step? is partial def, cannot unfold/reason about behavior.

private theorem anfConvert_steps_simulation
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (tr : List Core.TraceEvent) (sa' : ANF.State),
      ANF_SimRel s t sa sf → ANF.Steps sa tr sa' →
      ∃ sf', Flat.Steps sf tr sf' ∧ ANF_SimRel s t sa' sf' := by
  intro sa sf tr sa' hrel hsteps
  induction hsteps generalizing sf with
  | refl => exact ⟨sf, .refl sf, hrel⟩
  | tail hstep _ ih =>
    obtain ⟨sf2, hfstep, hrel2⟩ := anfConvert_step_simulation s t h _ _ _ _ hrel hstep
    obtain ⟨sf3, hfsteps, hrel3⟩ := ih sf2 hrel2
    exact ⟨sf3, .tail hfstep hfsteps, hrel3⟩

private theorem anfConvert_trace_reflection
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ b, ANF.Behaves t b → Flat.Behaves s b := by
  intro b ⟨sa, hsteps, hhalt⟩
  have hinit := anfConvert_init_related s t h
  obtain ⟨sf, hfsteps, hrel⟩ :=
    anfConvert_steps_simulation s t h _ _ _ _ hinit hsteps
  exact ⟨sf, hfsteps, anfConvert_halt_preservation s t h _ _ hrel hhalt⟩

theorem anfConvert_correct (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ b, ANF.Behaves t b → ∃ b', Flat.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact anfConvert_trace_reflection s t h b hb

end VerifiedJS.Proofs
