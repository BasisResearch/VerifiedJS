/-
  VerifiedJS — Emit Correctness Proof
  Wasm.IR → Wasm.AST semantic preservation.
-/

import VerifiedJS.Wasm.Emit
import VerifiedJS.Wasm.Semantics

namespace VerifiedJS.Proofs

open VerifiedJS.Wasm

/-- Emit preserves the start function field from IR to Wasm module. -/
theorem emit_preserves_start (m : IR.IRModule) (w : Module)
    (h : emit m = .ok w) :
    w.start = m.startFunc := by
  simp only [emit, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; rw [← h]; exact buildModule_start m _

/-- Emit always produces exactly one import (wasi fd_write). -/
theorem emit_single_import (m : IR.IRModule) (w : Module)
    (h : emit m = .ok w) :
    w.imports.size = 1 := by
  simp only [emit, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; rw [← h]; exact buildModule_imports_size m _

/-! ### Behavioral Correctness: IR.IRBehaves → Wasm.Behaves

The REAL correctness theorem for emit: if the IR module produces a trace,
the emitted Wasm module produces the corresponding Wasm trace.
IR uses IR.TraceEvent (log/error/silent/trap); Wasm uses Wasm.TraceEvent (silent/trap).
Observable events (log/error) become silent at the Wasm level because they are
implemented via host calls (fd_write). The mapping is via IR.traceListToWasm. -/

/-- Lift a forward simulation through multi-step IR execution to produce Wasm steps. -/
private theorem emit_sim_steps (s : IR.IRModule) (t : Wasm.Module)
    (h : emit s = .ok t) :
    ∀ (ir : IR.IRExecState) (w : ExecState) (tr : List IR.TraceEvent) (ir' : IR.IRExecState),
      IR.EmitSimRel s t ir w → IR.IRSteps ir tr ir' →
      ∃ w', Steps w (IR.traceListToWasm tr) w' ∧ IR.EmitSimRel s t ir' w' := by
  intro ir w tr ir' hrel hsteps
  induction hsteps generalizing w with
  | refl => exact ⟨w, .refl w, hrel⟩
  | tail hstep _ ih =>
    obtain ⟨hstep_eq⟩ := hstep
    obtain ⟨w₂, hwStep, hrel₂⟩ := IR.EmitSimRel.step_sim s t _ _ _ _ hrel hstep_eq
    obtain ⟨w₃, hwSteps, hrel₃⟩ := ih w₂ hrel₂
    exact ⟨w₃, .tail (.mk hwStep) hwSteps, hrel₃⟩

/-- Emit preserves behavior: every IR trace maps to a Wasm trace. -/
theorem emit_behavioral_correct (s : IR.IRModule) (t : Wasm.Module)
    (h : emit s = .ok t)
    (hmem_pos : 0 < s.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : MemType),
      s.memories[i]? = some mt → mt.lim.max = none) :
    ∀ trace, IR.IRBehaves s trace →
      Wasm.Behaves t (IR.traceListToWasm trace) := by
  intro trace ⟨sf, hsteps, hhalt⟩
  obtain ⟨w', hwsteps, hrel'⟩ := emit_sim_steps s t h _ _ _ _
    (IR.EmitSimRel.init s t h hmem_pos hmem_nomax) hsteps
  exact ⟨w', hwsteps, IR.EmitSimRel.halt_sim s t _ _ hrel' hhalt⟩

end VerifiedJS.Proofs
