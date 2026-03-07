/-
  VerifiedJS — Wasm Binary Encoding
  Outside the verified TCB — validated by wasm-tools + Valex-style checker.
-/

import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

/-- Encode a Wasm module to binary format -/
def encodeBinary (m : Module) : ByteArray :=
  sorry -- TODO: Implement Wasm binary encoder

/-- Write a Wasm module to a .wasm file -/
def writeWasm (m : Module) (path : String) : IO Unit :=
  sorry -- TODO: Implement

end VerifiedJS.Wasm
