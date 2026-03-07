/-
  VerifiedJS — Core IL Semantics
  Small-step LTS as an inductive relation.
  SPEC: §8 (Executable Code and Execution Contexts), §9 (Ordinary Object Internal Methods)
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.Core

/-- Observable trace events -/
inductive TraceEvent where
  | log (s : String)        -- console.log output
  | error (s : String)      -- thrown error
  | silent                   -- no observable effect
  deriving Repr, BEq

/-- Execution environment — variable bindings -/
structure Env where
  bindings : List (String × Value)
  parent : Option Env
  deriving Repr

/-- Heap — maps addresses to objects -/
structure Heap where
  objects : Array (List (String × Value))
  nextAddr : Nat
  deriving Repr

/-- Execution state -/
structure State where
  expr : Expr
  env : Env
  heap : Heap
  trace : List TraceEvent
  deriving Repr

/-- Small-step reduction relation
    Step s t s' means state s steps to s' producing trace event t -/
inductive Step : State → TraceEvent → State → Prop where
  -- TODO: Define reduction rules per ECMA-262 §12–§13
  | placeholder : Step ⟨.this, ⟨[], none⟩, ⟨#[], 0⟩, []⟩ .silent ⟨.this, ⟨[], none⟩, ⟨#[], 0⟩, []⟩

/-- A program behaves with behavior b if it reduces to a terminal state with trace b -/
def Behaves (p : Program) (b : List TraceEvent) : Prop :=
  sorry -- TODO: Define in terms of Step*

end VerifiedJS.Core
