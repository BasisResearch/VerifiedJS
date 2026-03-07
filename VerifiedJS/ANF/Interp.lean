/-
  VerifiedJS — ANF IL Reference Interpreter
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.ANF

def interp (prog : Program) (fuel : Nat := 1000000) : IO (List Core.TraceEvent) :=
  sorry -- TODO: Implement

end VerifiedJS.ANF
