/-
  VerifiedJS — ANF Conversion: JS.Flat → JS.ANF
  Converts to A-normal form: names all subexpressions.
-/

import VerifiedJS.Flat.Syntax
import VerifiedJS.ANF.Syntax

namespace VerifiedJS.ANF

/-- Convert a Flat program to ANF -/
def convert (prog : Flat.Program) : Except String Program :=
  sorry -- TODO: Implement ANF conversion

end VerifiedJS.ANF
