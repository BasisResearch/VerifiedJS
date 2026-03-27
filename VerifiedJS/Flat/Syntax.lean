/-
  VerifiedJS — Flat IL Syntax
  First-order: closures → structs + function indices.
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.Flat

/-- ECMA-262 §6.2.5 language binding names reused from Core. -/
abbrev VarName := Core.VarName

/-- ECMA-262 §6.1.7 property key names reused from Core. -/
abbrev PropName := Core.PropName

/-- ECMA-262 §13.13 label names reused from Core. -/
abbrev LabelName := Core.LabelName

/-- Function index in the global function table. -/
abbrev FuncIdx := Nat

/-- Environment pointer (heap address of closure environment). -/
abbrev EnvPtr := Nat

/-- ECMA-262 §6.1 ECMAScript Language Types (Flat runtime representation). -/
inductive Value where
  | null
  | undefined
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | object (addr : Nat)
  | closure (funcIdx : FuncIdx) (envPtr : EnvPtr)
  deriving Repr, BEq

/--
ECMA-262 §13 Runtime Semantics: Evaluation (first-order Flat IL).
Closure conversion eliminates nested function values into closure pairs.
-/
inductive Expr where
  | lit (v : Value)
  | var (name : VarName)
  | «let» (name : VarName) (init : Expr) (body : Expr)
  | assign (name : VarName) (value : Expr)
  | «if» (cond : Expr) (then_ : Expr) (else_ : Expr)
  | seq (a b : Expr)
  | call (funcIdx : Expr) (envPtr : Expr) (args : List Expr)
  | newObj (funcIdx : Expr) (envPtr : Expr) (args : List Expr)
  | getProp (obj : Expr) (prop : PropName)
  | setProp (obj : Expr) (prop : PropName) (value : Expr)
  | getIndex (obj : Expr) (idx : Expr)
  | setIndex (obj : Expr) (idx : Expr) (value : Expr)
  | deleteProp (obj : Expr) (prop : PropName)
  | typeof (arg : Expr)
  | getEnv (envPtr : Expr) (idx : Nat)
  | makeEnv (values : List Expr)
  | makeClosure (funcIdx : FuncIdx) (env : Expr)
  | objectLit (props : List (PropName × Expr))
  | arrayLit (elems : List Expr)
  | throw (arg : Expr)
  | tryCatch (body : Expr) (catchParam : VarName) (catchBody : Expr) (finally_ : Option Expr)
  | while_ (cond : Expr) (body : Expr)
  | «break» (label : Option LabelName)
  | «continue» (label : Option LabelName)
  | labeled (label : LabelName) (body : Expr)
  | «return» (arg : Option Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (arg : Expr)
  | this
  | unary (op : Core.UnaryOp) (arg : Expr)
  | binary (op : Core.BinOp) (lhs rhs : Expr)
  deriving Repr, BEq, Inhabited

mutual
/-- Expression depth for well-founded recursion in step?. -/
def Expr.depth : Expr → Nat
  | .lit _ => 0 | .var _ => 0 | .this => 0 | .«break» _ => 0 | .«continue» _ => 0
  | .«let» _ init body => Expr.depth init + Expr.depth body + 1
  | .assign _ value => Expr.depth value + 1
  | .«if» cond then_ else_ => Expr.depth cond + Expr.depth then_ + Expr.depth else_ + 1
  | .seq a b => Expr.depth a + Expr.depth b + 1
  | .call f e args => Expr.depth f + Expr.depth e + Expr.listDepth args + 1
  | .newObj f e args => Expr.depth f + Expr.depth e + Expr.listDepth args + 1
  | .getProp obj _ => Expr.depth obj + 1
  | .setProp obj _ value => Expr.depth obj + Expr.depth value + 1
  | .getIndex obj idx => Expr.depth obj + Expr.depth idx + 1
  | .setIndex obj idx value => Expr.depth obj + Expr.depth idx + Expr.depth value + 1
  | .deleteProp obj _ => Expr.depth obj + 1
  | .typeof arg => Expr.depth arg + 1
  | .getEnv envPtr _ => Expr.depth envPtr + 1
  | .makeEnv values => Expr.listDepth values + 1
  | .makeClosure _ env => Expr.depth env + 1
  | .objectLit props => Expr.propListDepth props + 1
  | .arrayLit elems => Expr.listDepth elems + 1
  | .throw arg => Expr.depth arg + 1
  | .tryCatch body _ catchBody (some fin) => Expr.depth body + Expr.depth catchBody + Expr.depth fin + 1
  | .tryCatch body _ catchBody none => Expr.depth body + Expr.depth catchBody + 1
  | .while_ cond body => Expr.depth cond + Expr.depth body + 1
  | .labeled _ body => Expr.depth body + 1
  | .«return» (some e) => Expr.depth e + 1
  | .«return» none => 0
  | .yield (some e) _ => Expr.depth e + 1
  | .yield none _ => 0
  | .await arg => Expr.depth arg + 1
  | .unary _ arg => Expr.depth arg + 1
  | .binary _ lhs rhs => Expr.depth lhs + Expr.depth rhs + 1
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

/-- firstNonValueExpr returns targets that are NOT literals. -/
theorem firstNonValueExpr_target_not_lit {l : List Expr} {done target rest}
    (h : firstNonValueExpr l = some (done, target, rest)) :
    ∀ v, target ≠ .lit v := by
  induction l generalizing done target rest with
  | nil => simp [firstNonValueExpr] at h
  | cons e tl ih =>
    unfold firstNonValueExpr at h
    match e with
    | .lit _ =>
      match heq : firstNonValueExpr tl with
      | some (d, t, r) =>
        simp only [heq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, rfl⟩ := h
        exact ih heq
      | none => simp [heq] at h
    | .var _ | .«let» _ _ _ | .assign _ _ | .«if» _ _ _ | .seq _ _ | .call _ _ _
    | .newObj _ _ _ | .getProp _ _ | .setProp _ _ _ | .getIndex _ _ | .setIndex _ _ _
    | .deleteProp _ _ | .typeof _ | .getEnv _ _ | .makeEnv _ | .makeClosure _ _
    | .objectLit _ | .arrayLit _ | .throw _ | .tryCatch _ _ _ _ | .while_ _ _
    | .«break» _ | .«continue» _ | .labeled _ _ | .«return» _ | .yield _ _
    | .await _ | .this | .unary _ _ | .binary _ _ _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _⟩ := h
      intro v hv; exact absurd hv (by intro h; cases h)

/-- firstNonValueProp returns targets that are NOT literals. -/
theorem firstNonValueProp_target_not_lit {l : List (PropName × Expr)} {done name target rest}
    (h : firstNonValueProp l = some (done, name, target, rest)) :
    ∀ v, target ≠ .lit v := by
  induction l generalizing done name target rest with
  | nil => simp [firstNonValueProp] at h
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    unfold firstNonValueProp at h
    match pe with
    | .lit _ =>
      match heq : firstNonValueProp tl with
      | some (d, n, t, r) =>
        simp only [heq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, rfl⟩ := h
        exact ih heq
      | none => simp [heq] at h
    | .var _ | .«let» _ _ _ | .assign _ _ | .«if» _ _ _ | .seq _ _ | .call _ _ _
    | .newObj _ _ _ | .getProp _ _ | .setProp _ _ _ | .getIndex _ _ | .setIndex _ _ _
    | .deleteProp _ _ | .typeof _ | .getEnv _ _ | .makeEnv _ | .makeClosure _ _
    | .objectLit _ | .arrayLit _ | .throw _ | .tryCatch _ _ _ _ | .while_ _ _
    | .«break» _ | .«continue» _ | .labeled _ _ | .«return» _ | .yield _ _
    | .await _ | .this | .unary _ _ | .binary _ _ _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl, _⟩ := h
      intro v hv; exact absurd hv (by intro h; cases h)

/-- ECMA-262 §10.2 ECMAScript Function Objects (closure-converted form). -/
structure FuncDef where
  name : VarName
  params : List VarName
  envParam : VarName
  body : Expr
  deriving Repr, BEq

/-- Flat program: function table plus top-level entry expression. -/
structure Program where
  functions : Array FuncDef
  main : Expr
  deriving Repr, BEq

-- Depth lemmas for call, newObj, objectLit, arrayLit constructors
theorem Expr.depth_call_funcExpr (f e : Expr) (args : List Expr) :
    f.depth < (Expr.call f e args).depth := by simp [Expr.depth]; omega
theorem Expr.depth_call_envExpr (f e : Expr) (args : List Expr) :
    e.depth < (Expr.call f e args).depth := by simp [Expr.depth]; omega
theorem Expr.listDepth_le_call (f e : Expr) (args : List Expr) :
    Expr.listDepth args < (Expr.call f e args).depth := by simp [Expr.depth]; omega

theorem Expr.depth_newObj_funcExpr (f e : Expr) (args : List Expr) :
    f.depth < (Expr.newObj f e args).depth := by simp [Expr.depth]; omega
theorem Expr.depth_newObj_envExpr (f e : Expr) (args : List Expr) :
    e.depth < (Expr.newObj f e args).depth := by simp [Expr.depth]; omega
theorem Expr.listDepth_le_newObj (f e : Expr) (args : List Expr) :
    Expr.listDepth args < (Expr.newObj f e args).depth := by simp [Expr.depth]; omega

theorem Expr.propListDepth_le_objectLit (props : List (PropName × Expr)) :
    Expr.propListDepth props < (Expr.objectLit props).depth := by simp [Expr.depth]

theorem Expr.listDepth_le_arrayLit (elems : List Expr) :
    Expr.listDepth elems < (Expr.arrayLit elems).depth := by simp [Expr.depth]

end VerifiedJS.Flat
