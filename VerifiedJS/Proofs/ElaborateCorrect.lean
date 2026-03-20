/-
  VerifiedJS — Elaboration Correctness Proof
  JS.AST → JS.Core semantic preservation.
-/

import VerifiedJS.Core.Elaborate
import VerifiedJS.Core.Semantics

namespace VerifiedJS.Proofs

-- TODO: State and prove elaboration correctness after Source/Core semantics are defined
-- theorem elaborate_correct (s : Source.Program) (t : Core.Program)
--     (h : Core.elaborate s = .ok t) :
--     ∀ b, Core.Behaves t b → ∃ b', Source.Behaves s b' ∧ BehaviorRefines b b'

end VerifiedJS.Proofs
