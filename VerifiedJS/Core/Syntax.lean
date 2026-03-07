/-
  VerifiedJS — Core IL Syntax
  Desugared subset: destructuring/for-in/classes → primitives.
  SPEC: Desugared form of §8 (Executable Code), §9 (Ordinary Objects)
-/

namespace VerifiedJS.Core

/-- Core unary operators (after desugaring) -/
inductive UnaryOp where
  | neg | pos | bitNot | logNot | void
  deriving Repr, BEq

/-- Core binary operators (after desugaring) -/
inductive BinOp where
  | add | sub | mul | div | mod | exp
  | eq | neq | strictEq | strictNeq
  | lt | gt | le | ge
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  | logAnd | logOr
  | instanceof | «in»
  deriving Repr, BEq

/-- Core values — subset of JS values after desugaring -/
inductive Value where
  | null
  | undefined
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | object (addr : Nat) -- heap address
  | function (idx : Nat) -- function table index
  deriving Repr, BEq

/-- Core expressions — all desugared to primitives -/
inductive Expr where
  | lit (v : Value)
  | var (name : String)
  | «let» (name : String) (init : Expr) (body : Expr)
  | assign (name : String) (value : Expr)
  | «if» (cond : Expr) (then_ : Expr) (else_ : Expr)
  | seq (a b : Expr)
  | call (callee : Expr) (args : List Expr)
  | newObj (callee : Expr) (args : List Expr)
  | getProp (obj : Expr) (prop : String)
  | setProp (obj : Expr) (prop : String) (value : Expr)
  | getIndex (obj : Expr) (idx : Expr)
  | setIndex (obj : Expr) (idx : Expr) (value : Expr)
  | deleteProp (obj : Expr) (prop : String)
  | typeof (arg : Expr)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinOp) (lhs rhs : Expr)
  | objectLit (props : List (String × Expr))
  | arrayLit (elems : List Expr)
  | functionDef (name : Option String) (params : List String) (body : Expr)
    (isAsync : Bool) (isGenerator : Bool)
  | throw (arg : Expr)
  | tryCatch (body : Expr) (catchParam : String) (catchBody : Expr) (finally_ : Option Expr)
  | while_ (cond : Expr) (body : Expr)
  | «break» (label : Option String)
  | «continue» (label : Option String)
  | «return» (arg : Option Expr)
  | labeled (label : String) (body : Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (arg : Expr)
  | this
  deriving Repr

/-- A Core program is a list of top-level expressions -/
structure Program where
  body : Expr
  functions : Array (String × List String × Expr)
  deriving Repr

end VerifiedJS.Core
