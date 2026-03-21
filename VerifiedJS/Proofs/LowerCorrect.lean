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

/-- Lowering preserves behavior: every ANF trace maps to an IR trace. -/
theorem lower_behavioral_correct (s : ANF.Program) (t : Wasm.IR.IRModule)
    (h : Wasm.lower s = .ok t) :
    ∀ trace, ANF.Behaves s trace →
      IR.IRBehaves t (IR.traceListFromCore trace) := by
  sorry

end VerifiedJS.Proofs
