/-
  VerifiedJS — Elaboration Correctness Proof
  JS.AST → JS.Core semantic preservation.
-/

import VerifiedJS.Core.Elaborate
import VerifiedJS.Core.Semantics

namespace VerifiedJS.Proofs

open VerifiedJS.Core in
/-- Elaboration correctness: if elaboration succeeds producing Core program t,
    then any Core behavior of t is also a Source behavior of s.
    This follows directly from Source.Behaves being defined as
    ∃ coreProg, elaborate s = .ok coreProg ∧ Core.Behaves coreProg b. -/
theorem elaborate_correct (s : Source.Program) (t : Core.Program)
    (h : Core.elaborate s = .ok t) :
    ∀ b, Core.Behaves t b → Source.Behaves s b := by
  intro b hb
  exact ⟨t, h, hb⟩

end VerifiedJS.Proofs
