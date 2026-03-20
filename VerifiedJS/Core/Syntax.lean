/-
  VerifiedJS — Core IL Syntax
  Desugared subset: destructuring/for-in/classes → primitives.
  SPEC: Desugared form of §8 (Executable Code), §9 (Ordinary Objects)
-/

namespace VerifiedJS.Core

/-- ECMA-262 §6.1 language values in Core. -/
abbrev VarName := String

/-- ECMA-262 §6.1.7 property keys (string-normalized in Core). -/
abbrev PropName := String

/-- ECMA-262 §13.13 Labels (used by break/continue). -/
abbrev LabelName := String

/-- ECMA-262 §10.2 function identity (global function table index in Core). -/
abbrev FuncIdx := Nat

/-- ECMA-262 §13.5, §13.4, §13.5 Runtime Semantics: unary operators. -/
inductive UnaryOp where
  | neg | pos | bitNot | logNot | void
  deriving Repr, BEq

/-- ECMA-262 §13.8-§13.11, §13.15 Runtime Semantics: binary operators. -/
inductive BinOp where
  | add | sub | mul | div | mod | exp
  | eq | neq | strictEq | strictNeq
  | lt | gt | le | ge
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  | logAnd | logOr
  | instanceof | «in»
  deriving Repr, BEq

/-- ECMA-262 §6.1 language values after Core desugaring. -/
inductive Value where
  | null
  | undefined
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | object (addr : Nat) -- heap address
  | function (idx : FuncIdx) -- function table index
  deriving Repr, BEq

/--
ECMA-262 §13 Runtime Semantics: Evaluation (desugared Core expression language).
Control forms and effects are expression-based to simplify small-step semantics.
-/
inductive Expr where
  | lit (v : Value)
  | var (name : VarName)
  | «let» (name : VarName) (init : Expr) (body : Expr)
  | assign (name : VarName) (value : Expr)
  | «if» (cond : Expr) (then_ : Expr) (else_ : Expr)
  | seq (a b : Expr)
  | call (callee : Expr) (args : List Expr)
  | newObj (callee : Expr) (args : List Expr)
  | getProp (obj : Expr) (prop : PropName)
  | setProp (obj : Expr) (prop : PropName) (value : Expr)
  | getIndex (obj : Expr) (idx : Expr)
  | setIndex (obj : Expr) (idx : Expr) (value : Expr)
  | deleteProp (obj : Expr) (prop : PropName)
  | typeof (arg : Expr)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinOp) (lhs rhs : Expr)
  | objectLit (props : List (PropName × Expr))
  | arrayLit (elems : List Expr)
  | functionDef (name : Option VarName) (params : List VarName) (body : Expr)
    (isAsync : Bool) (isGenerator : Bool)
  | throw (arg : Expr)
  | tryCatch (body : Expr) (catchParam : VarName) (catchBody : Expr) (finally_ : Option Expr)
  | while_ (cond : Expr) (body : Expr)
  /-- ECMA-262 §13.7.5 for-in iteration over object property keys. -/
  | forIn (binding : VarName) (obj : Expr) (body : Expr)
  /-- ECMA-262 §13.7.5.13 for-of iteration over iterable values. -/
  | forOf (binding : VarName) (iterable : Expr) (body : Expr)
  | «break» (label : Option LabelName)
  | «continue» (label : Option LabelName)
  | «return» (arg : Option Expr)
  | labeled (label : LabelName) (body : Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (arg : Expr)
  | this
  deriving Repr, BEq

mutual
/-- Expression depth for well-founded recursion in step?. -/
def Expr.depth : Expr → Nat
  | .lit _ => 0 | .var _ => 0 | .this => 0 | .«break» _ => 0 | .«continue» _ => 0
  | .«let» _ init body => Expr.depth init + Expr.depth body + 1
  | .assign _ value => Expr.depth value + 1
  | .«if» cond then_ else_ => Expr.depth cond + Expr.depth then_ + Expr.depth else_ + 1
  | .seq a b => Expr.depth a + Expr.depth b + 1
  | .call callee args => Expr.depth callee + Expr.listDepth args + 1
  | .newObj callee args => Expr.depth callee + Expr.listDepth args + 1
  | .getProp obj _ => Expr.depth obj + 1
  | .setProp obj _ value => Expr.depth obj + Expr.depth value + 1
  | .getIndex obj idx => Expr.depth obj + Expr.depth idx + 1
  | .setIndex obj idx value => Expr.depth obj + Expr.depth idx + Expr.depth value + 1
  | .deleteProp obj _ => Expr.depth obj + 1
  | .typeof arg => Expr.depth arg + 1
  | .unary _ arg => Expr.depth arg + 1
  | .binary _ lhs rhs => Expr.depth lhs + Expr.depth rhs + 1
  | .objectLit props => Expr.propListDepth props + 1
  | .arrayLit elems => Expr.listDepth elems + 1
  | .functionDef _ _ _ _ _ => 0
  | .throw arg => Expr.depth arg + 1
  | .tryCatch body _ catchBody (some fin) => Expr.depth body + Expr.depth catchBody + Expr.depth fin + 1
  | .tryCatch body _ catchBody none => Expr.depth body + Expr.depth catchBody + 1
  | .while_ cond body => Expr.depth cond + Expr.depth body + 1
  | .forIn _binding obj body => Expr.depth obj + Expr.depth body + 1
  | .forOf _binding iterable body => Expr.depth iterable + Expr.depth body + 1
  | .labeled _ body => Expr.depth body + 1
  | .«return» (some e) => Expr.depth e + 1
  | .«return» none => 0
  | .yield (some e) _ => Expr.depth e + 1
  | .yield none _ => 0
  | .await arg => Expr.depth arg + 1

/-- Sum of depths for expression lists. -/
def Expr.listDepth : List Expr → Nat
  | [] => 0
  | e :: rest => Expr.depth e + Expr.listDepth rest + 1

/-- Sum of depths for property-expression lists. -/
def Expr.propListDepth : List (PropName × Expr) → Nat
  | [] => 0
  | (_, e) :: rest => Expr.depth e + Expr.propListDepth rest + 1
end

theorem Expr.mem_listDepth_lt {e : Expr} {l : List Expr} (h : e ∈ l) :
    Expr.depth e < Expr.listDepth l := by
  induction l with
  | nil => simp at h
  | cons hd tl ih => simp [Expr.listDepth]; cases h with | head => omega | tail _ h => have := ih h; omega

/-- Find the first non-literal expression in a list. -/
def firstNonValueExpr : List Expr → Option (List Expr × Expr × List Expr)
  | [] => none
  | e :: rest =>
      match e with
      | .lit _ =>
          match firstNonValueExpr rest with
          | some (done, target, remaining) => some (e :: done, target, remaining)
          | none => none
      | _ => some ([], e, rest)

/-- Find the first non-literal property value in a list. -/
def firstNonValueProp : List (PropName × Expr) →
    Option (List (PropName × Expr) × PropName × Expr × List (PropName × Expr))
  | [] => none
  | (name, e) :: rest =>
      match e with
      | .lit _ =>
          match firstNonValueProp rest with
          | some (done, n, target, remaining) => some ((name, e) :: done, n, target, remaining)
          | none => none
      | _ => some ([], name, e, rest)

theorem firstNonValueExpr_depth {l : List Expr} {done target rest}
    (h : firstNonValueExpr l = some (done, target, rest)) :
    Expr.depth target < Expr.listDepth l := by
  induction l generalizing done target rest with
  | nil => simp [firstNonValueExpr] at h
  | cons e tl ih =>
    unfold firstNonValueExpr at h
    split at h
    · -- e = .lit _
      split at h
      · next heq => simp at h; obtain ⟨_, rfl, rfl⟩ := h; simp [Expr.listDepth]; have := ih heq; omega
      · simp at h
    · -- e is not a lit
      simp at h; obtain ⟨_, rfl, _⟩ := h; simp [Expr.listDepth]; omega

theorem firstNonValueProp_depth {l : List (PropName × Expr)} {done name target rest}
    (h : firstNonValueProp l = some (done, name, target, rest)) :
    Expr.depth target < Expr.propListDepth l := by
  induction l generalizing done name target rest with
  | nil => simp [firstNonValueProp] at h
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    unfold firstNonValueProp at h
    split at h
    · -- pe = .lit _
      split at h
      · next heq => simp at h; obtain ⟨_, _, rfl, rfl⟩ := h; simp [Expr.propListDepth]; have := ih heq; omega
      · simp at h
    · -- pe is not a lit
      simp at h; obtain ⟨_, _, rfl, _⟩ := h; simp [Expr.propListDepth]; omega

/-- Extract values from a list of expressions, returning none if any is not a value. -/
def allValues : List Expr → Option (List Value)
  | [] => some []
  | e :: rest =>
      match e with
      | .lit v =>
          match allValues rest with
          | some vs => some (v :: vs)
          | none => none
      | _ => none

/-- Build indexed property list from array elements. -/
def mkIndexedProps : Nat → List Expr → List (PropName × Value)
  | _, [] => []
  | i, e :: rest =>
      match e with
      | .lit v => (toString i, v) :: mkIndexedProps (i + 1) rest
      | _ => mkIndexedProps (i + 1) rest

/-- ECMA-262 §10.2 Function closure: captures lexical environment at definition site. -/
structure FuncClosure where
  name : Option VarName
  params : List VarName
  body : Expr
  capturedEnv : List (VarName × Value)
  deriving Repr, BEq

/-- ECMA-262 §10.2 function metadata captured in Core programs. -/
structure FuncDef where
  name : VarName
  params : List VarName
  body : Expr
  isAsync : Bool := false
  isGenerator : Bool := false
  deriving Repr, BEq

/-- ECMA-262 §16 Scripts and Modules (script body lowered to one Core expression). -/
structure Program where
  body : Expr
  functions : Array FuncDef
  deriving Repr, BEq

end VerifiedJS.Core
