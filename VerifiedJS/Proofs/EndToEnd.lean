/-
  VerifiedJS — End-to-End Correctness
  Composition of all pass theorems.
  NO SORRYS ALLOWED after Phase 2.
-/

import VerifiedJS.Proofs.ElaborateCorrect
import VerifiedJS.Proofs.ClosureConvertCorrect
import VerifiedJS.Proofs.ANFConvertCorrect
import VerifiedJS.Proofs.OptimizeCorrect
import VerifiedJS.Proofs.LowerCorrect
import VerifiedJS.Proofs.EmitCorrect

namespace VerifiedJS.Proofs

-- TODO: Compose all pass correctness theorems into end-to-end proof
-- theorem endToEnd (js : Source.Program) (wasm : Wasm.Module)
--     (h : compile js = .ok wasm) :
--     ∀ b, Wasm.Behaves wasm b → ∃ b', Source.Behaves js b' ∧ b = b'

end VerifiedJS.Proofs
