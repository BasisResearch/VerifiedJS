/-
  VerifiedJS — Flat IL Reference Interpreter
-/

import VerifiedJS.Flat.Syntax
import VerifiedJS.Flat.Semantics

namespace VerifiedJS.Flat

/-- Maximum evaluation steps to prevent infinite loops. -/
def maxSteps : Nat := 1000000

/-- Interpret a Flat program via deterministic small-step execution. -/
def interp (prog : Program) (fuel : Nat := maxSteps) : IO (List Core.TraceEvent) :=
  let rec run (remaining : Nat) (s : State) (acc : List Core.TraceEvent) : List Core.TraceEvent :=
    match remaining with
    | 0 => acc ++ [.error "Interpreter fuel exhausted"]
    | n + 1 =>
        match step? s with
        | none => acc
        | some (t, s') => run n s' (acc ++ [t])
  pure <| run fuel (initialState prog) []

end VerifiedJS.Flat
