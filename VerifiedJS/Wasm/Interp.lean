/-
  VerifiedJS — Wasm Reference Interpreter
-/

import VerifiedJS.Wasm.Syntax
import VerifiedJS.Wasm.Semantics

namespace VerifiedJS.Wasm

def interp (m : Module) (fuel : Nat := 1000000) : IO Unit := do
  let mut state := initialState m
  let mut remaining := fuel
  while remaining > 0 do
    match step? state with
    | none => return ()
    | some (ev, state') =>
      match ev with
      | .trap msg => throw (IO.userError s!"wasm trap: {msg}")
      | .silent => pure ()
      state := state'
      remaining := remaining - 1
  throw (IO.userError "wasm interpreter: fuel exhausted")

end VerifiedJS.Wasm
