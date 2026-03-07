/-
  VerifiedJS — Wasm Type Checking / Validation
  SPEC: WebAssembly 1.0 §3 (Validation)
-/

import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

/-- Validate a Wasm module -/
def validate (m : Module) : Except String Unit :=
  sorry -- TODO: Implement type-checking rules

end VerifiedJS.Wasm
