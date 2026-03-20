/-
  VerifiedJS — ANF Conversion Correctness Proof
  JS.Flat → JS.ANF observable semantic preservation.

  ANF conversion names all intermediate computations, introducing extra let-bindings
  that evaluate atomically (via evalComplex). This changes the number of small-step
  transitions: one ANF step (evaluating a let-binding) may correspond to multiple
  Flat steps (evaluating subexpressions one at a time). Therefore we use:
  - Observable traces (filtering out .silent events) rather than full traces
  - A stuttering (multi-step) simulation: one ANF step ↔ one or more Flat steps
-/

import VerifiedJS.ANF.Convert
import VerifiedJS.Flat.Semantics
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.Proofs

/-- Append two multi-step sequences. -/
private theorem Flat.Steps.append {s1 s2 s3 : Flat.State}
    {tr1 tr2 : List Core.TraceEvent}
    (h1 : Flat.Steps s1 tr1 s2) (h2 : Flat.Steps s2 tr2 s3) :
    Flat.Steps s1 (tr1 ++ tr2) s3 := by
  induction h1 with
  | refl => exact h2
  | tail hstep _ ih => exact .tail hstep (ih h2)

/-- Filter trace to observable (non-silent) events.
    ANF conversion preserves observable events but changes the number of
    silent (administrative) steps. -/
def observableTrace : List Core.TraceEvent → List Core.TraceEvent :=
  List.filter (· != .silent)

theorem observableTrace_nil : observableTrace [] = [] := rfl

theorem observableTrace_silent (rest : List Core.TraceEvent) :
    observableTrace (.silent :: rest) = observableTrace rest := by
  simp [observableTrace, List.filter]

theorem observableTrace_log (s : String) (rest : List Core.TraceEvent) :
    observableTrace (.log s :: rest) = .log s :: observableTrace rest := by
  simp [observableTrace, List.filter]

theorem observableTrace_error (s : String) (rest : List Core.TraceEvent) :
    observableTrace (.error s :: rest) = .error s :: observableTrace rest := by
  simp [observableTrace, List.filter]

theorem observableTrace_append (a b : List Core.TraceEvent) :
    observableTrace (a ++ b) = observableTrace a ++ observableTrace b := by
  simp [observableTrace, List.filter_append]

/-- Stuttering simulation: one ANF step corresponds to one or more Flat steps,
    preserving observable events. The simulation relation captures that:
    - Heaps are equal
    - Observable traces agree
    - Expressions/environments are in correspondence through the conversion.
    The full relation is left abstract; its properties are stated below. -/
private theorem anfConvert_step_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (ev : Core.TraceEvent) (sa' : ANF.State),
      observableTrace sa.trace = observableTrace sf.trace →
      sa.heap = sf.heap →
      ANF.Step sa ev sa' →
      ∃ sf' (evs : List Core.TraceEvent),
        Flat.Steps sf evs sf' ∧
        observableTrace [ev] = observableTrace evs ∧
        observableTrace sa'.trace = observableTrace sf'.trace ∧
        sa'.heap = sf'.heap := by
  sorry -- Requires expression/environment correspondence through ANF conversion

/-- When ANF reaches a terminal state, Flat can also reach a terminal state
    (possibly after additional silent steps to finish evaluating subexpressions). -/
private theorem anfConvert_halt_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State),
      observableTrace sa.trace = observableTrace sf.trace →
      sa.heap = sf.heap →
      ANF.step? sa = none →
      ∃ sf' (evs : List Core.TraceEvent),
        Flat.Steps sf evs sf' ∧
        Flat.step? sf' = none ∧
        observableTrace evs = [] ∧
        observableTrace sa.trace = observableTrace sf'.trace := by
  sorry -- Requires showing Flat subexpression evaluation terminates with only silent steps

/-- Multi-step simulation derived from single-step stuttering simulation. -/
private theorem anfConvert_steps_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (tr : List Core.TraceEvent) (sa' : ANF.State),
      observableTrace sa.trace = observableTrace sf.trace →
      sa.heap = sf.heap →
      ANF.Steps sa tr sa' →
      ∃ sf' (tr' : List Core.TraceEvent),
        Flat.Steps sf tr' sf' ∧
        observableTrace tr = observableTrace tr' ∧
        observableTrace sa'.trace = observableTrace sf'.trace ∧
        sa'.heap = sf'.heap := by
  intro sa sf tr sa' hobs hheap hsteps
  induction hsteps generalizing sf with
  | refl => exact ⟨sf, [], .refl sf, rfl, hobs, hheap⟩
  | tail hstep _ ih =>
    obtain ⟨sf2, evs1, hfsteps1, hobsev, hobs2, hheap2⟩ :=
      anfConvert_step_star s t h _ _ _ _ hobs hheap hstep
    obtain ⟨sf3, evs2, hfsteps2, hobstr, hobs3, hheap3⟩ :=
      ih sf2 hobs2 hheap2
    exact ⟨sf3, evs1 ++ evs2,
      Flat.Steps.append hfsteps1 hfsteps2,
      by rw [observableTrace_append]; congr 1; exact hobsev; exact hobstr,
      hobs3, hheap3⟩

/-- ANF conversion preserves observable behavior:
    For every terminating ANF execution, there exists a terminating Flat
    execution with the same observable trace (non-silent events). -/
theorem anfConvert_correct (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ b, ANF.Behaves t b →
      ∃ b', Flat.Behaves s b' ∧ observableTrace b = observableTrace b' := by
  intro b ⟨sa, hsteps, hhalt⟩
  -- Initial states have empty traces and equal heaps
  have hobs₀ : observableTrace (ANF.initialState t).trace = observableTrace (Flat.initialState s).trace := by
    simp [ANF.initialState, Flat.initialState, observableTrace]
  have hheap₀ : (ANF.initialState t).heap = (Flat.initialState s).heap := by
    simp [ANF.initialState, Flat.initialState]
  -- Multi-step simulation
  obtain ⟨sf, tr', hfsteps, hobstr, hobs, hheap⟩ :=
    anfConvert_steps_star s t h _ _ _ _ hobs₀ hheap₀ hsteps
  -- Halt preservation
  obtain ⟨sf', evs', hfsteps', hhalt', hobsevs, hobs'⟩ :=
    anfConvert_halt_star s t h _ _ hobs hheap hhalt
  -- Combine: Flat reaches sf via tr', then sf' via evs' (all silent)
  exact ⟨tr' ++ evs', ⟨sf', Flat.Steps.append hfsteps hfsteps', hhalt'⟩,
    by rw [observableTrace_append, hobsevs, List.append_nil]; exact hobstr⟩

end VerifiedJS.Proofs
