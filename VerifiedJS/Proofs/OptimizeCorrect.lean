/-
  VerifiedJS — Optimization Pass Correctness
  Identity pass — trivially correct.
-/

import VerifiedJS.ANF.Optimize
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.Proofs

theorem optimize_correct (p : ANF.Program) :
    ∀ b, ANF.Behaves (ANF.optimize p) b ↔ ANF.Behaves p b := by
  intro b; constructor <;> (intro h; exact h)

end VerifiedJS.Proofs
