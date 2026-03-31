/-
  VerifiedJS — Lowering Correctness Proof
  JS.ANF → Wasm.IR semantic preservation.
-/

import VerifiedJS.Wasm.Lower
import VerifiedJS.Wasm.Semantics
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.Proofs

open VerifiedJS.Wasm

theorem runtimeIdx_getGlobal_fresh_from_arith :
    RuntimeIdx.getGlobal ≠ RuntimeIdx.binaryAdd ∧ RuntimeIdx.getGlobal ≠ RuntimeIdx.binaryNeq := by
  decide

theorem runtimeIdx_getGlobal_after_numeric_helpers :
    RuntimeIdx.binaryNeq < RuntimeIdx.getGlobal := by
  decide

/-- Lowering pass structural correctness milestone:
    successful lowering yields no Wasm start section (WASI uses _start export). -/
theorem lower_correct (s : ANF.Program) (t : Wasm.IR.IRModule)
    (h : Wasm.lower s = .ok t) :
    t.startFunc = none := by
  exact Wasm.lower_startFunc_none s t h

theorem lower_exports_correct (s : ANF.Program) (t : Wasm.IR.IRModule)
    (h : Wasm.lower s = .ok t) :
    ∃ mainIdx startIdx, t.exports = #[("main", mainIdx), ("_start", startIdx)] := by
  exact Wasm.lower_exports_shape s t h

theorem lower_memory_correct (s : ANF.Program) (t : Wasm.IR.IRModule)
    (h : Wasm.lower s = .ok t) :
    t.memories = #[{ lim := { min := 1, max := none } }] := by
  exact Wasm.lower_memory_shape s t h

/-! ### Behavioral Correctness: ANF.Behaves → IR.IRBehaves

The REAL correctness theorem for lowering: if the ANF program produces a
trace, the lowered IR module produces the corresponding IR trace.
ANF uses Core.TraceEvent; IR uses IR.TraceEvent. The mapping is via
IR.traceFromCore (log↦log, error↦error, silent↦silent). -/

/-- Lift a forward simulation through multi-step ANF execution to produce IR steps. -/
private theorem lower_sim_steps (s : ANF.Program) (t : Wasm.IR.IRModule)
    (h : Wasm.lower s = .ok t) :
    ∀ (sa : ANF.State) (ir : IR.IRExecState) (tr : List Core.TraceEvent) (sa' : ANF.State),
      IR.LowerSimRel s t sa ir → ANF.Steps sa tr sa' →
      ∃ ir', IR.IRSteps ir (IR.traceListFromCore tr) ir' ∧ IR.LowerSimRel s t sa' ir' := by
  intro sa ir tr sa' hrel hsteps
  induction hsteps generalizing ir with
  | refl => exact ⟨ir, by simp [IR.traceListFromCore]; exact IR.IRSteps.refl ir, hrel⟩
  | @tail s1 s2 s3 ct cts hstep hrest ih =>
    have hanf := hstep.1
    have hmapped : IR.anfStepMapped s1 = some (IR.traceFromCore ct, s2) := by
      simp [IR.anfStepMapped, hanf]
    obtain ⟨ir₂, ir_trace₂, hirsteps₂, hrel₂, hobs₂⟩ := IR.step_sim s t h s1 ir _ _ hrel hmapped
    obtain ⟨ir₃, hirsteps₃, hrel₃⟩ := ih hrel₂
    sorry

/-- Lowering preserves behavior: every ANF trace maps to an IR trace. -/
theorem lower_behavioral_correct (s : ANF.Program) (t : Wasm.IR.IRModule)
    (h : Wasm.lower s = .ok t) :
    ∀ trace, ANF.Behaves s trace →
      IR.IRBehaves t (IR.traceListFromCore trace) := by
  intro trace ⟨sf, hsteps, hhalt⟩
  obtain ⟨ir', hirsteps, hrel'⟩ := lower_sim_steps s t h _ _ _ _ (IR.LowerSimRel.init s t h (IR.lower_main_code_corr s t h) (IR.lower_main_var_scope s t h)) hsteps
  exact ⟨ir', hirsteps,
    IR.LowerSimRel.halt_sim s t _ _ hrel' ((IR.anfStepMapped_none_iff sf).mpr hhalt)⟩

end VerifiedJS.Proofs
