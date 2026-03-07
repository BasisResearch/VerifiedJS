/-
  VerifiedJS — ANF IL Syntax
  A-normal form: all subexpressions are named, side effects sequenced.
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.ANF

/-- ANF values — trivial expressions that don't need to be named -/
inductive Trivial where
  | var (name : String)
  | litNull | litUndefined
  | litBool (b : Bool)
  | litNum (n : Float)
  | litStr (s : String)
  deriving Repr, BEq

mutual

/-- ANF expressions — complex operations where all args are trivial -/
inductive Expr where
  | trivial (t : Trivial)
  | «let» (name : String) (rhs : ComplexExpr) (body : Expr)
  | «if» (cond : Trivial) (then_ : Expr) (else_ : Expr)
  | seq (a b : Expr)
  | while_ (cond : Expr) (body : Expr)
  | throw (arg : Trivial)
  | tryCatch (body : Expr) (catchParam : String) (catchBody : Expr) (finally_ : Option Expr)
  | «return» (arg : Option Trivial)
  | labeled (label : String) (body : Expr)
  | «break» (label : Option String)
  | «continue» (label : Option String)

/-- Complex expressions — operations that produce a value and must be let-bound -/
inductive ComplexExpr where
  | trivial (t : Trivial)
  | call (callee : Trivial) (env : Trivial) (args : List Trivial)
  | getProp (obj : Trivial) (prop : String)
  | setProp (obj : Trivial) (prop : String) (value : Trivial)
  | getEnv (env : Trivial) (idx : Nat)
  | makeEnv (values : List Trivial)
  | makeClosure (funcIdx : Nat) (env : Trivial)
  | objectLit (props : List (String × Trivial))
  | arrayLit (elems : List Trivial)
  | unary (op : Core.UnaryOp) (arg : Trivial)
  | binary (op : Core.BinOp) (lhs rhs : Trivial)

end

/-- ANF function definition -/
structure FuncDef where
  name : String
  params : List String
  envParam : String
  body : Expr

/-- ANF program -/
structure Program where
  functions : Array FuncDef
  main : Expr

end VerifiedJS.ANF
