/-
  VerifiedJS — Closure Conversion: JS.Core → JS.Flat
  Converts closures to (function_index, environment_pointer) pairs.
-/

import VerifiedJS.Core.Syntax
import VerifiedJS.Flat.Syntax

namespace VerifiedJS.Flat

/-- Convert a Core program to Flat by closure conversion -/
def closureConvert (prog : Core.Program) : Except String Program :=
  sorry -- TODO: Implement closure conversion

end VerifiedJS.Flat
