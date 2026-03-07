/-
  VerifiedJS — Wasm IR Reference Interpreter
-/

import VerifiedJS.Wasm.IR

namespace VerifiedJS.Wasm.IR

def interp (m : IRModule) (fuel : Nat := 1000000) : IO Unit :=
  sorry -- TODO: Implement

end VerifiedJS.Wasm.IR
