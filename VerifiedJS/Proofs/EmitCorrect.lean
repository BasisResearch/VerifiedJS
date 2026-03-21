/-
  VerifiedJS — Emit Correctness Proof
  Wasm.IR → Wasm.AST semantic preservation.
-/

import VerifiedJS.Wasm.Emit

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

-- TODO: State and prove full emit correctness (semantic preservation)
-- theorem emit_correct (s : Wasm.IR.IRModule) (t : Wasm.Module)
--     (h : Wasm.emit s = .ok t) :
--     ∀ trace, IR.Behaves s trace → Wasm.Behaves t trace

end VerifiedJS.Proofs
