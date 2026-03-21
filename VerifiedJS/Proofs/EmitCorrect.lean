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

/-- Emit preserves behavior: every IR trace maps to a Wasm trace. -/
theorem emit_behavioral_correct (s : IR.IRModule) (t : Wasm.Module)
    (h : emit s = .ok t) :
    ∀ trace, IR.IRBehaves s trace →
      Wasm.Behaves t (IR.traceListToWasm trace) := by
  sorry

end VerifiedJS.Proofs
