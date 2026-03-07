/-
  VerifiedJS — Wasm IR → Wasm AST
-/

import VerifiedJS.Wasm.IR
import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

/-- Emit a Wasm AST module from Wasm IR -/
def emit (m : IR.IRModule) : Except String Module :=
  sorry -- TODO: Implement

end VerifiedJS.Wasm
