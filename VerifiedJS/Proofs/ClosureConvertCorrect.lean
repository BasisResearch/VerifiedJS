/-
  VerifiedJS — Closure Conversion Correctness Proof
  JS.Core → JS.Flat semantic preservation.
-/

import VerifiedJS.Flat.ClosureConvert
import VerifiedJS.Core.Semantics
import VerifiedJS.Flat.Semantics

namespace VerifiedJS.Proofs

theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
  sorry -- TODO: Prove

end VerifiedJS.Proofs
