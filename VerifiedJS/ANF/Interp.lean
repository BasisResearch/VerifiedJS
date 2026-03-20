/-
  VerifiedJS — ANF IL Reference Interpreter
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.ANF

/-- Maximum evaluation steps to prevent infinite loops. -/
def maxSteps : Nat := 1000000

/-- Interpret an ANF program via deterministic small-step execution. -/
def interp (prog : Program) (fuel : Nat := maxSteps) : IO (List Core.TraceEvent) :=
  let rec run (remaining : Nat) (s : State) (acc : List Core.TraceEvent) : List Core.TraceEvent :=
    match remaining with
    | 0 => acc ++ [.error "Interpreter fuel exhausted"]
    | n + 1 =>
        match step? s with
        | none => acc
        | some (t, s') => run n s' (acc ++ [t])
  pure <| run fuel (initialState prog) []

end VerifiedJS.ANF
