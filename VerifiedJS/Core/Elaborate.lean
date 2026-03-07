/-
  VerifiedJS — Elaboration: JS.AST → JS.Core
  Desugars classes, destructuring, for-in/for-of, etc. into Core primitives.
  SPEC: §14.6 (Class Definitions), §13.15.5 (Destructuring), §13.7 (Iteration)
-/

import VerifiedJS.Source.AST
import VerifiedJS.Core.Syntax

namespace VerifiedJS.Core

/-- Elaborate a full JS AST program into Core IL -/
def elaborate (prog : Source.Program) : Except String Program :=
  sorry -- TODO: Implement elaboration pass

end VerifiedJS.Core
