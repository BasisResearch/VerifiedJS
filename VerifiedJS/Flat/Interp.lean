/-
  VerifiedJS — Flat IL Reference Interpreter
-/

import VerifiedJS.Flat.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.Flat

def interp (prog : Program) (fuel : Nat := 1000000) : IO (List Core.TraceEvent) :=
  sorry -- TODO: Implement

end VerifiedJS.Flat
