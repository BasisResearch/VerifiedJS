/-
  VerifiedJS — Lowering: JS.ANF → Wasm.IR
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Wasm.IR

namespace VerifiedJS.Wasm

/-- Lower an ANF program to Wasm IR -/
def lower (prog : ANF.Program) : Except String IR.IRModule :=
  sorry -- TODO: Implement lowering pass

end VerifiedJS.Wasm
