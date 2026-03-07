/-
  VerifiedJS — Core IL Reference Interpreter
  Executable interpreter for testing and debugging.
-/

import VerifiedJS.Core.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.Core

/-- Interpreter result -/
inductive InterpResult where
  | value (v : Value)
  | throw_ (v : Value)
  | return_ (v : Value)
  | break_ (label : Option String)
  | continue_ (label : Option String)
  deriving Repr

/-- Maximum evaluation steps to prevent infinite loops -/
def maxSteps : Nat := 1000000

/-- Interpret a Core expression -/
def interp (prog : Program) (fuel : Nat := maxSteps) : IO (List TraceEvent) :=
  sorry -- TODO: Implement reference interpreter

end VerifiedJS.Core
