/-
  VerifiedJS — ANF Conversion Correctness Proof
  JS.Flat → JS.ANF semantic preservation.
-/

import VerifiedJS.ANF.Convert
import VerifiedJS.Flat.Semantics
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.Proofs

theorem anfConvert_correct (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ b, ANF.Behaves t b → ∃ b', Flat.Behaves s b' ∧ b = b' :=
  sorry -- TODO: Prove

end VerifiedJS.Proofs
