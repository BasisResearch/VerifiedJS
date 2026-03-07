/-
  VerifiedJS — Wasm Reference Interpreter
-/

import VerifiedJS.Wasm.Syntax
import VerifiedJS.Wasm.Semantics

namespace VerifiedJS.Wasm

def interp (m : Module) (fuel : Nat := 1000000) : IO Unit :=
  sorry -- TODO: Implement Wasm interpreter

end VerifiedJS.Wasm
