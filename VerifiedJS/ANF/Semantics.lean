/-
  VerifiedJS — ANF IL Semantics
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Flat.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.ANF

structure State where
  expr : Expr
  env : List (String × Flat.Value)
  heap : Core.Heap
  trace : List Core.TraceEvent

inductive Step : State → Core.TraceEvent → State → Prop where
  -- TODO: Define reduction rules
  | placeholder (s : State) : Step s .silent s

def Behaves (p : Program) (b : List Core.TraceEvent) : Prop :=
  sorry -- TODO: Define

end VerifiedJS.ANF
