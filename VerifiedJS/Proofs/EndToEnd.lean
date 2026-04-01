/-
  VerifiedJS — End-to-End Correctness
  Composition of all pass theorems.

  Pipeline: Source → Core → Flat → ANF → IR → Wasm
  Each pass has a correctness theorem. This file composes them.
-/

import VerifiedJS.Proofs.ElaborateCorrect
import VerifiedJS.Proofs.ClosureConvertCorrect
import VerifiedJS.Proofs.ANFConvertCorrect
import VerifiedJS.Proofs.OptimizeCorrect
import VerifiedJS.Proofs.LowerCorrect
import VerifiedJS.Proofs.EmitCorrect

namespace VerifiedJS.Proofs

open VerifiedJS.Wasm

/-! ### Proof Chain Structure

The end-to-end correctness argument composes these per-pass theorems:

1. **ElaborateCorrect**: Source → Core (TODO: awaiting Source semantics)
2. **ClosureConvertCorrect**: Core.Behaves ← Flat.Behaves (backward sim)
3. **ANFConvertCorrect**: Flat.Behaves ← ANF.Behaves (observable trace, backward sim)
4. **OptimizeCorrect**: ANF.Behaves ↔ ANF.Behaves (identity, proved)
5. **LowerBehavioralCorrect**: ANF.Behaves → IR.IRBehaves (forward sim)
6. **EmitBehavioralCorrect**: IR.IRBehaves → Wasm.Behaves (forward sim)

Passes 2-3 use backward simulation (target behavior implies source behavior).
Passes 5-6 use forward simulation (source behavior implies target behavior).
The end-to-end theorem chains them: Wasm.Behaves ← ... ← Core.Behaves.
-/

/-- Partial end-to-end: Core → Wasm (forward + backward).
    Forward: ANF behavior → Wasm behavior (via lower + emit).
    Backward: ANF behavior → Core behavior (via ANF conversion + closure conversion).
    Precondition: the Core program never reaches forIn/forOf (unimplemented). -/
theorem flat_to_wasm_correct
    (flat : Flat.Program) (core : Core.Program)
    (anf : ANF.Program) (ir : IR.IRModule) (wasm : Wasm.Module)
    (hcc : Flat.closureConvert core = .ok flat)
    (hanf : ANF.convert flat = .ok anf)
    (hlower : Wasm.lower (ANF.optimize anf) = .ok ir)
    (hemit : emit ir = .ok wasm)
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState core) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f))
    (h_wf : noCallFrameReturn core.body = true)
    (h_addr_wf : ExprAddrWF core.body 1)
    (hwf_flat : ExprWellFormed flat.main (Flat.initialState flat).env)
    (hmem_pos : 0 < ir.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : Wasm.MemType),
      ir.memories[i]? = some mt → mt.lim.max = none) :
    ∀ anfTrace, ANF.Behaves anf anfTrace →
      -- Forward: ANF → Wasm behavioral preservation
      Wasm.Behaves wasm (IR.traceListToWasm (IR.traceListFromCore anfTrace)) ∧
      -- Backward: ANF → Core trace correspondence
      ∃ coreTrace, Core.Behaves core coreTrace ∧
        observableTrace anfTrace = observableTrace coreTrace := by
  intro anfTrace hanfb
  constructor
  · -- Forward: ANF → optimize → lower → emit → Wasm
    exact emit_behavioral_correct ir wasm hemit hmem_pos hmem_nomax _
      (lower_behavioral_correct _ ir hlower _
        ((optimize_correct anf anfTrace).mpr hanfb))
  · -- Backward: ANF → Flat → Core
    obtain ⟨flatTrace, hflatb, hobs⟩ := anfConvert_correct flat anf hanf hwf_flat anfTrace hanfb
    obtain ⟨coreTrace, hcoreb, heq⟩ := closureConvert_correct core flat hcc h_wf h_addr_wf hnofor flatTrace hflatb
    exact ⟨coreTrace, hcoreb, by rw [hobs, heq]⟩

end VerifiedJS.Proofs
