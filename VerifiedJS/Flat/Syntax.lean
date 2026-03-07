/-
  VerifiedJS — Flat IL Syntax
  First-order: closures → structs + function indices.
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.Flat

/-- Function index in the global function table -/
abbrev FuncIdx := Nat

/-- Environment pointer (heap address of closure environment) -/
abbrev EnvPtr := Nat

/-- Flat values — closures are represented as (function_index, environment_pointer) -/
inductive Value where
  | null | undefined
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | object (addr : Nat)
  | closure (funcIdx : FuncIdx) (envPtr : EnvPtr)
  deriving Repr, BEq

/-- Flat expressions — first-order, no nested closures -/
inductive Expr where
  | lit (v : Value)
  | var (name : String)
  | «let» (name : String) (init : Expr) (body : Expr)
  | assign (name : String) (value : Expr)
  | «if» (cond : Expr) (then_ : Expr) (else_ : Expr)
  | seq (a b : Expr)
  | call (funcIdx : Expr) (envPtr : Expr) (args : List Expr)
  | getProp (obj : Expr) (prop : String)
  | setProp (obj : Expr) (prop : String) (value : Expr)
  | getEnv (envPtr : Expr) (idx : Nat)
  | makeEnv (values : List Expr)
  | makeClosure (funcIdx : FuncIdx) (env : Expr)
  | objectLit (props : List (String × Expr))
  | arrayLit (elems : List Expr)
  | throw (arg : Expr)
  | tryCatch (body : Expr) (catchParam : String) (catchBody : Expr) (finally_ : Option Expr)
  | while_ (cond : Expr) (body : Expr)
  | «return» (arg : Option Expr)
  | unary (op : Core.UnaryOp) (arg : Expr)
  | binary (op : Core.BinOp) (lhs rhs : Expr)
  deriving Repr

/-- A flat function definition -/
structure FuncDef where
  name : String
  params : List String
  envParam : String
  body : Expr
  deriving Repr

/-- A Flat program -/
structure Program where
  functions : Array FuncDef
  main : Expr
  deriving Repr

end VerifiedJS.Flat
