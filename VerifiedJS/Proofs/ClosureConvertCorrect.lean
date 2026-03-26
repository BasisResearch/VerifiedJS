/-
  VerifiedJS — Closure Conversion Correctness Proof
  JS.Core → JS.Flat semantic preservation.
-/

import VerifiedJS.Flat.ClosureConvert
import VerifiedJS.Core.Semantics
import VerifiedJS.Flat.Semantics

set_option maxHeartbeats 800000

namespace VerifiedJS.Proofs

/-! ### Helper lemmas for list-based constructor cases in step?_none_implies_lit -/

/-- The target returned by firstNonValueExpr is never a literal. -/
private theorem firstNonValueExpr_not_lit {l : List Flat.Expr} {done target rest}
    (h : Flat.firstNonValueExpr l = some (done, target, rest)) :
    ∀ v, target ≠ .lit v := by
  induction l generalizing done target rest with
  | nil => simp [Flat.firstNonValueExpr] at h
  | cons e tl ih =>
    cases e with
    | lit w =>
      have hred : Flat.firstNonValueExpr (.lit w :: tl) =
          (match Flat.firstNonValueExpr tl with
           | some (d, t, r) => some (.lit w :: d, t, r) | none => none) := rfl
      rw [hred] at h
      cases heq : Flat.firstNonValueExpr tl with
      | none => simp [heq] at h
      | some val =>
        obtain ⟨d, t, r⟩ := val
        simp only [heq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, rfl⟩ := h; exact ih heq
    | _ =>
      -- For all non-lit constructors, firstNonValueExpr returns some ([], e, tl)
      -- The key: after cases, e IS the specific constructor, so rfl reduces the match
      all_goals (
        dsimp only [Flat.firstNonValueExpr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        intro v habs; exact Flat.Expr.noConfusion habs
      )

/-- The target returned by firstNonValueProp is never a literal. -/
private theorem firstNonValueProp_not_lit {l : List (Flat.PropName × Flat.Expr)} {done name target rest}
    (h : Flat.firstNonValueProp l = some (done, name, target, rest)) :
    ∀ v, target ≠ .lit v := by
  induction l generalizing done name target rest with
  | nil => simp [Flat.firstNonValueProp] at h
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    cases pe with
    | lit w =>
      have hred : Flat.firstNonValueProp (⟨pn, .lit w⟩ :: tl) =
          (match Flat.firstNonValueProp tl with
           | some (d, n, t, r) => some (⟨pn, .lit w⟩ :: d, n, t, r) | none => none) := rfl
      rw [hred] at h
      cases heq : Flat.firstNonValueProp tl with
      | none => simp [heq] at h
      | some val =>
        obtain ⟨d, n, t, r⟩ := val
        simp only [heq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, rfl⟩ := h; exact ih heq
    | _ =>
      all_goals (
        dsimp only [Flat.firstNonValueProp] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, _⟩ := h
        intro v habs; exact Flat.Expr.noConfusion habs
      )

/-- If firstNonValueExpr returns none, all elements are literals,
    so valuesFromExprList? returns some. -/
private theorem firstNonValueExpr_none_implies_values (l : List Flat.Expr) :
    Flat.firstNonValueExpr l = none → ∃ vs, Flat.valuesFromExprList? l = some vs := by
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons e tl ih =>
    intro h
    cases e with
    | lit v =>
      cases heq : Flat.firstNonValueExpr tl with
      | some val => simp [Flat.firstNonValueExpr, heq] at h
      | none =>
        obtain ⟨vs, hvs⟩ := ih heq
        exact ⟨v :: vs, by simp [Flat.valuesFromExprList?, Flat.exprValue?, hvs]⟩
    | _ => all_goals (simp [Flat.firstNonValueExpr] at h)

/-- If firstNonValueProp returns none, all property values are literals,
    so valuesFromExprList? on the values returns some. -/
private theorem firstNonValueProp_none_implies_values (l : List (Flat.PropName × Flat.Expr)) :
    Flat.firstNonValueProp l = none →
    ∃ vs, Flat.valuesFromExprList? (l.map Prod.snd) = some vs := by
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    intro h
    cases pe with
    | lit v =>
      cases heq : Flat.firstNonValueProp tl with
      | some val => simp [Flat.firstNonValueProp, heq] at h
      | none =>
        obtain ⟨vs, hvs⟩ := ih heq
        exact ⟨v :: vs, by simp [Flat.valuesFromExprList?, Flat.exprValue?, hvs]⟩
    | _ => all_goals (simp [Flat.firstNonValueProp] at h)

/-- Environment correspondence: bidirectional — every Flat binding has a corresponding
    Core binding and vice versa (modulo value conversion). -/
private def EnvCorr (cenv : Core.Env) (fenv : Flat.Env) : Prop :=
  (∀ name fv, fenv.lookup name = some fv →
    ∃ cv, cenv.lookup name = some cv ∧ fv = Flat.convertValue cv) ∧
  (∀ name cv, cenv.lookup name = some cv →
    ∃ fv, fenv.lookup name = some fv ∧ fv = Flat.convertValue cv)

/-- toBoolean commutes with convertValue. -/
private theorem toBoolean_convertValue (v : Core.Value) :
    Flat.toBoolean (Flat.convertValue v) = Core.toBoolean v := by
  cases v <;> simp [Flat.convertValue, Flat.toBoolean, Core.toBoolean]

/-- toNumber commutes with convertValue. -/
private theorem toNumber_convertValue (v : Core.Value) :
    Flat.toNumber (Flat.convertValue v) = Core.toNumber v := by
  cases v with
  | bool b => cases b <;> rfl
  | string s => rfl
  | _ => rfl

/-- evalUnary commutes with convertValue. -/
private theorem evalUnary_convertValue (op : Core.UnaryOp) (v : Core.Value) :
    Flat.evalUnary op (Flat.convertValue v) = Flat.convertValue (Core.evalUnary op v) := by
  cases op with
  | neg =>
    simp only [Core.evalUnary, Flat.evalUnary]
    rw [toNumber_convertValue]; simp [Flat.convertValue]
  | pos =>
    simp only [Core.evalUnary, Flat.evalUnary]
    rw [toNumber_convertValue]; simp [Flat.convertValue]
  | logNot =>
    simp only [Core.evalUnary, Flat.evalUnary]
    rw [toBoolean_convertValue]; simp [Flat.convertValue]
  | void => rfl
  | bitNot =>
    simp only [Core.evalUnary, Flat.evalUnary]
    rw [toNumber_convertValue]; simp [Flat.convertValue]

/-- valueToString commutes with convertValue. -/
private theorem valueToString_convertValue (v : Core.Value) :
    Flat.valueToString (Flat.convertValue v) = Core.valueToString v := by
  cases v with
  | bool b => cases b <;> rfl
  | string => rfl
  | number => rfl
  | null => rfl
  | undefined => rfl
  | object => rfl
  | function => rfl

/-- convertValue preserves BEq: (convertValue a == convertValue b) = (a == b). -/
private theorem convertValue_beq (a b : Core.Value) :
    (Flat.convertValue a == Flat.convertValue b) = (a == b) := by
  cases a <;> cases b <;> simp [Flat.convertValue] <;> (try rfl)
  -- function.function: (.closure idx₁ 0 == .closure idx₂ 0) = (.function idx₁ == .function idx₂)
  -- Both reduce to idx₁ == idx₂ but BEq instances differ structurally.
  · rename_i idx₁ idx₂
    change (idx₁ == idx₂ && (0 : Nat) == 0) = (idx₁ == idx₂)
    simp

set_option maxHeartbeats 4000000 in
private theorem abstractEq_convertValue (a b : Core.Value) :
    Flat.abstractEq (Flat.convertValue a) (Flat.convertValue b) = Core.abstractEq a b := by
  cases a <;> cases b <;> simp only [Flat.convertValue, Flat.abstractEq, Core.abstractEq] <;>
    first | rfl | (cases ‹Bool› <;> first | rfl | (cases ‹Bool› <;> rfl))

set_option maxHeartbeats 4000000 in
private theorem abstractLt_convertValue (a b : Core.Value) :
    Flat.abstractLt (Flat.convertValue a) (Flat.convertValue b) = Core.abstractLt a b := by
  cases a <;> cases b <;> simp only [Flat.convertValue, Flat.abstractLt, Core.abstractLt] <;>
    first | rfl | (cases ‹Bool› <;> first | rfl | (cases ‹Bool› <;> rfl))

/-- evalBinary commutes with convertValue for operators where Flat matches Core. -/
private theorem evalBinary_convertValue (op : Core.BinOp) (a b : Core.Value) :
    Flat.evalBinary op (Flat.convertValue a) (Flat.convertValue b) =
    Flat.convertValue (Core.evalBinary op a b) := by
  cases op with
  | sub =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | mul =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | div =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | logAnd =>
    simp only [Flat.evalBinary, Core.evalBinary]
    rw [toBoolean_convertValue]
    cases Core.toBoolean a <;> rfl
  | logOr =>
    simp only [Flat.evalBinary, Core.evalBinary]
    rw [toBoolean_convertValue]
    cases Core.toBoolean a <;> rfl
  | strictEq =>
    simp only [Core.evalBinary, Flat.evalBinary]
    congr 1; exact convertValue_beq a b
  | strictNeq =>
    simp only [Core.evalBinary, Flat.evalBinary, Flat.convertValue, bne]
    show Flat.Value.bool (!(Flat.convertValue a == Flat.convertValue b)) = Flat.Value.bool (!(a == b))
    rw [convertValue_beq]
  | add =>
    cases a <;> cases b <;> simp [Core.evalBinary, Flat.evalBinary, Flat.convertValue, toNumber_convertValue, valueToString_convertValue] <;> (try cases ‹Bool›) <;> (try cases ‹Bool›) <;> rfl
  | mod =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    split <;> simp_all [Flat.convertValue]
  | exp =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | bitAnd =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | bitOr =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | bitXor =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | shl =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | shr =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | ushr =>
    simp only [Core.evalBinary, Flat.evalBinary]
    rw [toNumber_convertValue, toNumber_convertValue]
    simp [Flat.convertValue]
  | eq =>
    simp only [Core.evalBinary, Flat.evalBinary, Flat.convertValue]
    congr 1; exact abstractEq_convertValue a b
  | neq =>
    simp only [Core.evalBinary, Flat.evalBinary, Flat.convertValue, bne]
    show Flat.Value.bool (!(Flat.abstractEq (Flat.convertValue a) (Flat.convertValue b))) = Flat.Value.bool (!(Core.abstractEq a b))
    congr 1; congr 1; exact abstractEq_convertValue a b
  | lt =>
    simp only [Core.evalBinary, Flat.evalBinary, Flat.convertValue]
    congr 1; exact abstractLt_convertValue a b
  | gt =>
    simp only [Core.evalBinary, Flat.evalBinary, Flat.convertValue]
    congr 1; exact abstractLt_convertValue b a
  | le =>
    simp only [Core.evalBinary, Flat.evalBinary, Flat.convertValue, bne]
    show Flat.Value.bool (!(Flat.abstractLt (Flat.convertValue b) (Flat.convertValue a))) = Flat.Value.bool (!(Core.abstractLt b a))
    congr 1; congr 1; exact abstractLt_convertValue b a
  | ge =>
    simp only [Core.evalBinary, Flat.evalBinary, Flat.convertValue, bne]
    show Flat.Value.bool (!(Flat.abstractLt (Flat.convertValue a) (Flat.convertValue b))) = Flat.Value.bool (!(Core.abstractLt a b))
    congr 1; congr 1; exact abstractLt_convertValue a b
  | instanceof =>
    cases a <;> cases b <;> simp [Core.evalBinary, Flat.evalBinary, Flat.convertValue]
  | «in» =>
    cases a <;> cases b <;> simp [Core.evalBinary, Flat.evalBinary, Flat.convertValue]

/-- Extending both envs preserves EnvCorr. -/
private theorem EnvCorr_extend {cenv : Core.Env} {fenv : Flat.Env}
    (h : EnvCorr cenv fenv) (name : String) (cv : Core.Value) :
    EnvCorr (Core.Env.extend cenv name cv) (Flat.Env.extend fenv name (Flat.convertValue cv)) := by
  constructor
  · -- Flat⊆Core direction
    intro n fv hlookup
    simp only [Flat.Env.extend, Flat.Env.lookup] at hlookup
    simp only [Core.Env.extend, Core.Env.lookup]
    -- Case split on whether n matches the new binding name
    by_cases heq : name == n
    · -- n = name: found the new binding
      simp [List.find?, heq] at hlookup ⊢
      exact hlookup.symm
    · -- n ≠ name: delegate to old env via h.1
      simp [List.find?, heq] at hlookup ⊢
      have hlookup' : fenv.lookup n = some fv := hlookup
      exact h.1 n fv hlookup'
  · -- Core⊆Flat direction
    intro n cv' hlookup
    simp only [Core.Env.extend, Core.Env.lookup] at hlookup
    simp only [Flat.Env.extend, Flat.Env.lookup]
    by_cases heq : name == n
    · simp [List.find?, heq] at hlookup ⊢
      rw [hlookup]
    · simp [List.find?, heq] at hlookup ⊢
      have hlookup' : cenv.lookup n = some cv' := hlookup
      obtain ⟨fv, hfenv, hfv⟩ := h.2 n cv' hlookup'
      subst hfv; exact hfenv

/-- Lookup after updateBindingList for the same name returns the new value (Flat). -/
private theorem Flat_lookup_updateBindingList_eq (xs : Flat.Env) (name : Flat.VarName) (v : Flat.Value)
    (h : xs.any (fun kv => kv.fst == name) = true) :
    Flat.Env.lookup (Flat.updateBindingList xs name v) name = some v := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    cases hn : (n == name)
    · simp only [Flat.updateBindingList, hn, ↓reduceIte, Flat.Env.lookup, List.find?, Bool.false_eq_true]
      have htl : tl.any (fun kv => kv.fst == name) = true := by
        simp only [List.any, hn, Bool.false_or] at h; exact h
      exact ih htl
    · simp only [Flat.updateBindingList, hn, ↓reduceIte, Flat.Env.lookup, List.find?, ↓reduceCtorEq]

/-- Lookup after updateBindingList for a different name is unchanged (Flat). -/
private theorem Flat_lookup_updateBindingList_ne (xs : Flat.Env) (name other : Flat.VarName) (v : Flat.Value)
    (hne : (other == name) = false) :
    Flat.Env.lookup (Flat.updateBindingList xs name v) other = Flat.Env.lookup xs other := by
  induction xs with
  | nil => simp [Flat.updateBindingList, Flat.Env.lookup]
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    cases hn : (n == name)
    · simp only [Flat.updateBindingList, hn, Bool.false_eq_true, ↓reduceIte, Flat.Env.lookup, List.find?]
      cases hno : (n == other)
      · exact ih
      · rfl
    · have hno : (n == other) = false := by
        have : n = name := by simpa using hn
        subst this; simp [Bool.beq_comm] at hne ⊢; exact hne
      simp only [Flat.updateBindingList, hn, ↓reduceIte, Flat.Env.lookup, List.find?, hno]

/-- Lookup after Flat.Env.assign for the same name. -/
private theorem Flat_lookup_assign_eq (env : Flat.Env) (name : Flat.VarName) (v : Flat.Value) :
    (env.assign name v).lookup name = some v := by
  simp only [Flat.Env.assign]
  split
  · exact Flat_lookup_updateBindingList_eq env name v (by assumption)
  · simp [Flat.Env.lookup, List.find?, beq_self_eq_true]

/-- Lookup after Flat.Env.assign for a different name. -/
private theorem Flat_lookup_assign_ne (env : Flat.Env) (name other : Flat.VarName) (v : Flat.Value)
    (hne : (other == name) = false) :
    (env.assign name v).lookup other = env.lookup other := by
  simp only [Flat.Env.assign]
  split
  · exact Flat_lookup_updateBindingList_ne env name other v hne
  · have hne' : (name == other) = false := by simp [Bool.beq_comm] at hne ⊢; exact hne
    simp only [Flat.Env.lookup, List.find?, hne', Bool.false_eq_true, ↓reduceIte]

private theorem Core_lookup_assign_eq (env : Core.Env) (name : String) (v : Core.Value) :
    (env.assign name v).lookup name = some v := by
  unfold Core.Env.assign
  split
  · exact Core.lookup_updateBindingList_eq env.bindings name v (by assumption)
  · simp [Core.Env.lookup, List.find?, beq_self_eq_true]

/-- Assigning the same name in both envs preserves EnvCorr. -/
private theorem EnvCorr_assign {cenv : Core.Env} {fenv : Flat.Env}
    (h : EnvCorr cenv fenv) (name : String) (cv : Core.Value) :
    EnvCorr (Core.Env.assign cenv name cv) (Flat.Env.assign fenv name (Flat.convertValue cv)) := by
  constructor
  · -- Flat⊆Core: if Flat.assign lookup finds fv, show Core.assign lookup finds cv with fv = convertValue cv
    intro n fv hlookup
    by_cases hname : n = name
    · subst hname
      rw [Flat_lookup_assign_eq] at hlookup
      simp at hlookup; subst hlookup
      exact ⟨cv, Core_lookup_assign_eq _ _ _, rfl⟩
    · have hne : (n == name) = false := by simp [beq_eq_false_iff_ne, hname]
      rw [Flat_lookup_assign_ne _ _ _ _ hne] at hlookup
      obtain ⟨cv', hcv', hfv⟩ := h.1 n fv hlookup
      exact ⟨cv', by rw [Core.Env.lookup_assign_ne _ _ _ _ hne]; exact hcv', hfv⟩
  · -- Core⊆Flat: symmetric
    intro n cv' hlookup
    by_cases hname : n = name
    · subst hname
      rw [Core_lookup_assign_eq] at hlookup
      cases hlookup
      exact ⟨Flat.convertValue cv, Flat_lookup_assign_eq _ _ _, rfl⟩
    · have hne : (n == name) = false := by simp [beq_eq_false_iff_ne, hname]
      rw [Core.Env.lookup_assign_ne _ _ _ _ hne] at hlookup
      obtain ⟨fv, hfv, hconv⟩ := h.2 n cv' hlookup
      exact ⟨fv, by rw [Flat_lookup_assign_ne _ _ _ _ hne]; exact hfv, hconv⟩

/-! ### Scope irrelevance: `scope` is a dead parameter in convertExpr.

  The `scope` parameter is threaded through `convertExpr` recursion but never
  consumed — every case either passes it to recursive calls unchanged, extends
  it (`.let`, `.tryCatch`), or replaces it entirely (`.functionDef` uses
  `params` as `innerScope`).  Therefore the output is independent of `scope`. -/

mutual
private theorem convertExpr_scope_irrelevant (e : Core.Expr)
    (scope1 scope2 : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    Flat.convertExpr e scope1 envVar envMap st = Flat.convertExpr e scope2 envVar envMap st := by
  cases e with
  | lit v => simp [Flat.convertExpr]
  | var n => simp [Flat.convertExpr]
  | this => simp [Flat.convertExpr]
  | «break» l => simp [Flat.convertExpr]
  | «continue» l => simp [Flat.convertExpr]
  | forIn _ _ _ => simp [Flat.convertExpr]
  | forOf _ _ _ => simp [Flat.convertExpr]
  | «let» name init body =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant init scope1 scope2]
    rw [convertExpr_scope_irrelevant body (name :: scope1) (name :: scope2)]
  | assign name value =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant value scope1 scope2]
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant cond scope1 scope2]
    rw [convertExpr_scope_irrelevant then_ scope1 scope2]
    rw [convertExpr_scope_irrelevant else_ scope1 scope2]
  | seq a b =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant a scope1 scope2]
    rw [convertExpr_scope_irrelevant b scope1 scope2]
  | call callee args =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant callee scope1 scope2]
    rw [convertExprList_scope_irrelevant args scope1 scope2]
  | newObj callee args =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant callee scope1 scope2]
    rw [convertExprList_scope_irrelevant args scope1 scope2]
  | getProp obj prop =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant obj scope1 scope2]
  | setProp obj prop value =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant obj scope1 scope2]
    rw [convertExpr_scope_irrelevant value scope1 scope2]
  | getIndex obj idx =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant obj scope1 scope2]
    rw [convertExpr_scope_irrelevant idx scope1 scope2]
  | setIndex obj idx value =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant obj scope1 scope2]
    rw [convertExpr_scope_irrelevant idx scope1 scope2]
    rw [convertExpr_scope_irrelevant value scope1 scope2]
  | deleteProp obj prop =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant obj scope1 scope2]
  | typeof arg =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant arg scope1 scope2]
  | unary op arg =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant arg scope1 scope2]
  | binary op lhs rhs =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant lhs scope1 scope2]
    rw [convertExpr_scope_irrelevant rhs scope1 scope2]
  | objectLit props =>
    simp only [Flat.convertExpr]
    rw [convertPropList_scope_irrelevant props scope1 scope2]
  | arrayLit elems =>
    simp only [Flat.convertExpr]
    rw [convertExprList_scope_irrelevant elems scope1 scope2]
  | functionDef fname params body isAsync isGenerator =>
    -- scope is NOT used: innerScope := params
    unfold Flat.convertExpr; rfl
  | throw arg =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant arg scope1 scope2]
  | tryCatch body catchParam catchBody finally_ =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant body scope1 scope2]
    rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope1) (catchParam :: scope2)]
    rw [convertOptExpr_scope_irrelevant finally_ scope1 scope2]
  | while_ cond body =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant cond scope1 scope2]
    rw [convertExpr_scope_irrelevant body scope1 scope2]
  | «return» arg =>
    simp only [Flat.convertExpr]
    rw [convertOptExpr_scope_irrelevant arg scope1 scope2]
  | labeled label body =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant body scope1 scope2]
  | yield arg delegate =>
    simp only [Flat.convertExpr]
    rw [convertOptExpr_scope_irrelevant arg scope1 scope2]
  | await arg =>
    simp only [Flat.convertExpr]
    rw [convertExpr_scope_irrelevant arg scope1 scope2]
  termination_by sizeOf e
  decreasing_by all_goals (try simp_wf) <;> omega

private theorem convertExprList_scope_irrelevant (es : List Core.Expr)
    (scope1 scope2 : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    Flat.convertExprList es scope1 envVar envMap st = Flat.convertExprList es scope2 envVar envMap st := by
  cases es with
  | nil => simp [Flat.convertExprList]
  | cons e rest =>
    simp only [Flat.convertExprList]
    rw [convertExpr_scope_irrelevant e scope1 scope2]
    rw [convertExprList_scope_irrelevant rest scope1 scope2]
  termination_by sizeOf es
  decreasing_by all_goals (try simp_wf) <;> omega

private theorem convertPropList_scope_irrelevant (ps : List (Core.PropName × Core.Expr))
    (scope1 scope2 : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    Flat.convertPropList ps scope1 envVar envMap st = Flat.convertPropList ps scope2 envVar envMap st := by
  cases ps with
  | nil => simp [Flat.convertPropList]
  | cons p rest =>
    obtain ⟨pn, pe⟩ := p
    simp only [Flat.convertPropList]
    rw [convertExpr_scope_irrelevant pe scope1 scope2]
    rw [convertPropList_scope_irrelevant rest scope1 scope2]
  termination_by sizeOf ps
  decreasing_by all_goals (try simp_wf) <;> omega

private theorem convertOptExpr_scope_irrelevant (oe : Option Core.Expr)
    (scope1 scope2 : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    Flat.convertOptExpr oe scope1 envVar envMap st = Flat.convertOptExpr oe scope2 envVar envMap st := by
  cases oe with
  | none => simp [Flat.convertOptExpr]
  | some e =>
    simp only [Flat.convertOptExpr]
    rw [convertExpr_scope_irrelevant e scope1 scope2]
  termination_by sizeOf oe
  decreasing_by all_goals simp_all <;> omega
end

mutual
/-- Returns true if the expression never uses "__call_frame_return__" as a tryCatch catchParam.
    Source programs from `elaborate` satisfy this predicate since "__call_frame_return__" is only
    introduced by the Core interpreter for call-frame returns. -/
def noCallFrameReturn : Core.Expr → Bool
  | .tryCatch body cp cb fin =>
    cp != "__call_frame_return__" &&
    noCallFrameReturn body && noCallFrameReturn cb &&
    match fin with | some f => noCallFrameReturn f | none => true
  | .seq a b => noCallFrameReturn a && noCallFrameReturn b
  | .«if» c t e => noCallFrameReturn c && noCallFrameReturn t && noCallFrameReturn e
  | .while_ c b => noCallFrameReturn c && noCallFrameReturn b
  | .«let» _ i b => noCallFrameReturn i && noCallFrameReturn b
  | .assign _ v => noCallFrameReturn v
  | .call c args => noCallFrameReturn c && listNoCallFrameReturn args
  | .newObj c args => noCallFrameReturn c && listNoCallFrameReturn args
  | .getProp o _ => noCallFrameReturn o
  | .setProp o _ v => noCallFrameReturn o && noCallFrameReturn v
  | .getIndex o i => noCallFrameReturn o && noCallFrameReturn i
  | .setIndex o i v => noCallFrameReturn o && noCallFrameReturn i && noCallFrameReturn v
  | .deleteProp o _ => noCallFrameReturn o
  | .typeof a => noCallFrameReturn a
  | .unary _ a => noCallFrameReturn a
  | .binary _ l r => noCallFrameReturn l && noCallFrameReturn r
  | .objectLit ps => propListNoCallFrameReturn ps
  | .arrayLit es => listNoCallFrameReturn es
  | .throw a => noCallFrameReturn a
  | .forIn _ o b => noCallFrameReturn o && noCallFrameReturn b
  | .forOf _ i b => noCallFrameReturn i && noCallFrameReturn b
  | .labeled _ b => noCallFrameReturn b
  | .«return» (some e) => noCallFrameReturn e
  | .yield (some e) _ => noCallFrameReturn e
  | .await a => noCallFrameReturn a
  | _ => true
def listNoCallFrameReturn : List Core.Expr → Bool
  | [] => true
  | e :: rest => noCallFrameReturn e && listNoCallFrameReturn rest
def propListNoCallFrameReturn : List (Core.PropName × Core.Expr) → Bool
  | [] => true
  | (_, e) :: rest => noCallFrameReturn e && propListNoCallFrameReturn rest
end

/-- Heap prefix relation: Core heap is a prefix of Flat heap.
    Flat may contain additional closure-environment objects. -/
private def HeapCorr (cheap fheap : Core.Heap) : Prop :=
  cheap.objects.size ≤ fheap.objects.size ∧
  ∀ addr, addr < cheap.objects.size → cheap.objects[addr]? = fheap.objects[addr]?

private theorem HeapCorr_refl (h : Core.Heap) : HeapCorr h h :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem HeapCorr_get {ch fh : Core.Heap} {addr : Nat} (hc : HeapCorr ch fh) (hlt : addr < ch.objects.size) :
    ch.objects[addr]? = fh.objects[addr]? := hc.2 addr hlt

/-- Both heaps push the same object at the same size: prefix relation is maintained.
    Requires equal sizes (exact prefix), which holds when no extra Flat env objects exist. -/
private theorem HeapCorr_alloc_both {ch fh : Core.Heap} (hc : HeapCorr ch fh)
    (hsize : ch.objects.size = fh.objects.size) (p : List (Core.PropName × Core.Value)) :
    HeapCorr { objects := ch.objects.push p, nextAddr := ch.nextAddr + 1 }
             { objects := fh.objects.push p, nextAddr := fh.nextAddr + 1 } := by
  constructor
  · simp only [Array.size_push]; omega
  · intro addr hlt
    simp [Array.size_push] at hlt
    rcases Nat.lt_or_ge addr ch.objects.size with h | h
    · simp only [Array.getElem?_push, show ¬(addr = ch.objects.size) from by omega,
                 show ¬(addr = fh.objects.size) from by omega, ite_false]
      exact hc.2 addr h
    · have haddr_eq : addr = ch.objects.size := by omega
      subst haddr_eq
      simp only [Array.getElem?_push, hsize, ite_true]

/-- Flat allocates an extra object (e.g. environment): prefix relation is maintained. -/
private theorem HeapCorr_alloc_right {ch fh : Core.Heap} (hc : HeapCorr ch fh)
    (p : List (Core.PropName × Core.Value)) :
    HeapCorr ch { objects := fh.objects.push p, nextAddr := fh.nextAddr + 1 } := by
  constructor
  · simp only [Array.size_push]; exact Nat.le_succ_of_le hc.1
  · intro addr hlt
    have hlt_fh : addr < fh.objects.size := Nat.lt_of_lt_of_le hlt hc.1
    simp only [Array.getElem?_push, show ¬(addr = fh.objects.size) from by omega]
    exact hc.2 addr hlt

/-- Map Core.Value object addresses through an injection (for heap correspondence). -/
private def mapHeapValue (f : Nat → Nat) : Core.Value → Core.Value
  | .object addr => .object (f addr)
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .function idx => .function idx

/-- Convert Core.Value to Flat.Value through a heap injection.
    Like Flat.convertValue but maps object addresses through f. -/
private def convertValueInj (f : Nat → Nat) : Core.Value → Flat.Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object (f addr)
  | .function idx => .closure idx 0

private theorem convertValueInj_id (v : Core.Value) :
    convertValueInj id v = Flat.convertValue v := by
  cases v <;> rfl

private theorem mapHeapValue_id (v : Core.Value) :
    mapHeapValue id v = v := by
  cases v <;> rfl

/-- CompCert-style heap injection: maps Core heap addresses to Flat heap addresses.
    STAGING: currently defined as HeapCorr (ignores injMap).
    Will be replaced with real injection when proof sites are updated. -/
private def HeapInj (_injMap : Nat → Nat) (ch fh : Core.Heap) : Prop := HeapCorr ch fh

/-- Environment correspondence through heap injection.
    STAGING: currently defined as EnvCorr (ignores injMap).
    Will be replaced with injection-aware correspondence when proof sites are updated. -/
private def EnvCorrInj (_injMap : Nat → Nat) (cenv : Core.Env) (fenv : Flat.Env) : Prop :=
  EnvCorr cenv fenv

private theorem HeapInj_id (h : Core.Heap) : HeapInj id h h := HeapCorr_refl h

private theorem HeapInj_alloc_both {ch fh : Core.Heap} {f : Nat → Nat}
    (hinj : HeapInj f ch fh) (hsize : ch.objects.size = fh.objects.size)
    (p : List (Core.PropName × Core.Value)) :
    HeapInj f { objects := ch.objects.push p, nextAddr := ch.nextAddr + 1 }
             { objects := fh.objects.push p, nextAddr := fh.nextAddr + 1 } :=
  HeapCorr_alloc_both hinj hsize p

private theorem HeapInj_alloc_right {ch fh : Core.Heap} {f : Nat → Nat}
    (hinj : HeapInj f ch fh) (p : List (Core.PropName × Core.Value)) :
    HeapInj f ch { objects := fh.objects.push p, nextAddr := fh.nextAddr + 1 } :=
  HeapCorr_alloc_right hinj p

private theorem EnvCorrInj_extend {cenv : Core.Env} {fenv : Flat.Env} {f : Nat → Nat}
    (h : EnvCorrInj f cenv fenv) (name : String) (cv : Core.Value) :
    EnvCorrInj f (Core.Env.extend cenv name cv)
      (Flat.Env.extend fenv name (Flat.convertValue cv)) :=
  EnvCorr_extend h name cv

private theorem EnvCorrInj_assign {cenv : Core.Env} {fenv : Flat.Env} {f : Nat → Nat}
    (h : EnvCorrInj f cenv fenv) (name : String) (cv : Core.Value) :
    EnvCorrInj f (Core.Env.assign cenv name cv)
      (Flat.Env.assign fenv name (Flat.convertValue cv)) :=
  EnvCorr_assign h name cv

private theorem HeapInj_get {ch fh : Core.Heap} {f : Nat → Nat} {addr : Nat}
    (hinj : HeapInj f ch fh) (hlt : addr < ch.objects.size) :
    ch.objects[addr]? = fh.objects[addr]? := HeapCorr_get hinj hlt

/-- All object addresses in a Core value are valid heap addresses. -/
private def ValueAddrWF (v : Core.Value) (heapSize : Nat) : Prop :=
  match v with
  | .object addr => addr < heapSize
  | _ => True

/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
def ExprAddrWF : Core.Expr → Nat → Prop
  | .lit v, n => ValueAddrWF v n
  | .var _, _ => True
  | .«let» _ init body, n => ExprAddrWF init n ∧ ExprAddrWF body n
  | .assign _ value, n => ExprAddrWF value n
  | .«if» cond t e, n => ExprAddrWF cond n ∧ ExprAddrWF t n ∧ ExprAddrWF e n
  | .seq a b, n => ExprAddrWF a n ∧ ExprAddrWF b n
  | .call _ _, _ => True
  | .newObj _ _, _ => True
  | .getProp e _, n => ExprAddrWF e n
  | .setProp o _ v, n => ExprAddrWF o n ∧ ExprAddrWF v n
  | .getIndex e1 e2, n => ExprAddrWF e1 n ∧ ExprAddrWF e2 n
  | .setIndex o i v, n => ExprAddrWF o n ∧ ExprAddrWF i n ∧ ExprAddrWF v n
  | .deleteProp e _, n => ExprAddrWF e n
  | .typeof e, n => ExprAddrWF e n
  | .unary _ e, n => ExprAddrWF e n
  | .binary _ l r, n => ExprAddrWF l n ∧ ExprAddrWF r n
  | .objectLit _, _ => True
  | .arrayLit _, _ => True
  | .functionDef _ _ body _ _, n => ExprAddrWF body n
  | .throw e, n => ExprAddrWF e n
  | .tryCatch b _ c none, n => ExprAddrWF b n ∧ ExprAddrWF c n
  | .tryCatch b _ c (some fe), n => ExprAddrWF b n ∧ ExprAddrWF c n ∧ ExprAddrWF fe n
  | .while_ c b, n => ExprAddrWF c n ∧ ExprAddrWF b n
  | .forIn _ o b, n => ExprAddrWF o n ∧ ExprAddrWF b n
  | .forOf _ i b, n => ExprAddrWF i n ∧ ExprAddrWF b n
  | .«break» _, _ => True
  | .«continue» _, _ => True
  | .«return» none, _ => True
  | .«return» (some e), n => ExprAddrWF e n
  | .labeled _ b, n => ExprAddrWF b n
  | .yield none _, _ => True
  | .yield (some e) _, n => ExprAddrWF e n
  | .await e, n => ExprAddrWF e n
  | .this, _ => True

private theorem ValueAddrWF_mono {v : Core.Value} {n m : Nat}
    (h : ValueAddrWF v n) (hle : n ≤ m) : ValueAddrWF v m := by
  cases v <;> simp [ValueAddrWF] at * <;> omega

private theorem ExprAddrWF_mono : (e : Core.Expr) → {n m : Nat} →
    ExprAddrWF e n → (n ≤ m) → ExprAddrWF e m
  | .lit v, _, _, h, hle => ValueAddrWF_mono h hle
  | .var _, _, _, _, _ => trivial
  | .call _ _, _, _, _, _ => trivial
  | .newObj _ _, _, _, _, _ => trivial
  | .objectLit _, _, _, _, _ => trivial
  | .arrayLit _, _, _, _, _ => trivial
  | .break _, _, _, _, _ => trivial
  | .continue _, _, _, _, _ => trivial
  | .return none, _, _, _, _ => trivial
  | .yield none _, _, _, _, _ => trivial
  | .this, _, _, _, _ => trivial
  | .«let» _ init body, _, _, h, hle => ⟨ExprAddrWF_mono init h.1 hle, ExprAddrWF_mono body h.2 hle⟩
  | .assign _ value, _, _, h, hle => ExprAddrWF_mono value h hle
  | .«if» cond t el, _, _, h, hle => ⟨ExprAddrWF_mono cond h.1 hle, ExprAddrWF_mono t h.2.1 hle, ExprAddrWF_mono el h.2.2 hle⟩
  | .seq a b, _, _, h, hle => ⟨ExprAddrWF_mono a h.1 hle, ExprAddrWF_mono b h.2 hle⟩
  | .getProp obj _, _, _, h, hle => ExprAddrWF_mono obj h hle
  | .setProp o _ v, _, _, h, hle => ⟨ExprAddrWF_mono o h.1 hle, ExprAddrWF_mono v h.2 hle⟩
  | .getIndex e1 e2, _, _, h, hle => ⟨ExprAddrWF_mono e1 h.1 hle, ExprAddrWF_mono e2 h.2 hle⟩
  | .setIndex o i v, _, _, h, hle => ⟨ExprAddrWF_mono o h.1 hle, ExprAddrWF_mono i h.2.1 hle, ExprAddrWF_mono v h.2.2 hle⟩
  | .deleteProp obj _, _, _, h, hle => ExprAddrWF_mono obj h hle
  | .typeof arg, _, _, h, hle => ExprAddrWF_mono arg h hle
  | .unary _ arg, _, _, h, hle => ExprAddrWF_mono arg h hle
  | .binary _ l r, _, _, h, hle => ⟨ExprAddrWF_mono l h.1 hle, ExprAddrWF_mono r h.2 hle⟩
  | .functionDef _ _ body _ _, _, _, h, hle => ExprAddrWF_mono body h hle
  | .throw arg, _, _, h, hle => ExprAddrWF_mono arg h hle
  | .tryCatch b _ c none, _, _, h, hle => ⟨ExprAddrWF_mono b h.1 hle, ExprAddrWF_mono c h.2 hle⟩
  | .tryCatch b _ c (some fe), _, _, h, hle => ⟨ExprAddrWF_mono b h.1 hle, ExprAddrWF_mono c h.2.1 hle, ExprAddrWF_mono fe h.2.2 hle⟩
  | .while_ c b, _, _, h, hle => ⟨ExprAddrWF_mono c h.1 hle, ExprAddrWF_mono b h.2 hle⟩
  | .forIn _ o b, _, _, h, hle => ⟨ExprAddrWF_mono o h.1 hle, ExprAddrWF_mono b h.2 hle⟩
  | .forOf _ i b, _, _, h, hle => ⟨ExprAddrWF_mono i h.1 hle, ExprAddrWF_mono b h.2 hle⟩
  | .return (some arg), _, _, h, hle => ExprAddrWF_mono arg h hle
  | .yield (some arg) _, _, _, h, hle => ExprAddrWF_mono arg h hle
  | .labeled _ b, _, _, h, hle => ExprAddrWF_mono b h hle
  | .await arg, _, _, h, hle => ExprAddrWF_mono arg h hle
  termination_by e => sizeOf e
  decreasing_by all_goals (try simp_wf) <;> omega

private def EnvAddrWF (env : Core.Env) (heapSize : Nat) : Prop :=
  ∀ name v, env.lookup name = some v → ValueAddrWF v heapSize

private def HeapValuesWF (heap : Core.Heap) : Prop :=
  ∀ addr, addr < heap.objects.size →
    ∀ props, heap.objects[addr]? = some props →
      ∀ kv, kv ∈ props → ValueAddrWF kv.2 heap.objects.size

private theorem size_set! {α : Type} (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by
  simp only [Array.set!, Array.setIfInBounds]
  split
  · exact Array.size_set ..
  · rfl

private theorem HeapValuesWF_set_at {heap : Core.Heap} {addr : Nat}
    {newProps : List (Core.PropName × Core.Value)}
    (h : HeapValuesWF heap)
    (hnew : ∀ kv, kv ∈ newProps → ValueAddrWF kv.2 heap.objects.size) :
    HeapValuesWF { heap with objects := heap.objects.set! addr newProps } := by
  intro addr' haddr' props' hprops' kv hkv
  simp only [size_set!] at haddr' ⊢
  simp only [Array.set!, Array.setIfInBounds] at hprops'
  split at hprops'
  · next h_bound =>
    rw [Array.getElem?_set h_bound] at hprops'
    split at hprops'
    · simp only [Option.some.injEq] at hprops'; rw [← hprops'] at hkv; exact hnew kv hkv
    · exact h addr' haddr' props' hprops' kv hkv
  · exact h addr' haddr' props' hprops' kv hkv

private theorem EnvAddrWF_mono {env : Core.Env} {n m : Nat}
    (h : EnvAddrWF env n) (hle : n ≤ m) : EnvAddrWF env m :=
  fun name v hlookup => ValueAddrWF_mono (h name v hlookup) hle

private theorem EnvAddrWF_extend {env : Core.Env} {n : Nat}
    (h : EnvAddrWF env n) (name : String) (v : Core.Value)
    (hv : ValueAddrWF v n) : EnvAddrWF (env.extend name v) n := by
  intro n' v' hlookup
  by_cases heq : n' = name
  · subst heq
    rw [Core.Env.lookup_extend_same] at hlookup
    exact Option.some.inj hlookup ▸ hv
  · rw [Core.Env.lookup_extend_other env name n' v (Ne.symm heq)] at hlookup
    exact h n' v' hlookup

private theorem EnvAddrWF_assign {env : Core.Env} {n : Nat}
    (h : EnvAddrWF env n) (name : String) (v : Core.Value)
    (hv : ValueAddrWF v n) : EnvAddrWF (env.assign name v) n := by
  intro n' v' hlookup
  by_cases heq : n' = name
  · subst heq
    cases hex : env.bindings.any (fun kv => kv.fst == n') with
    | true => rw [Core.Env.lookup_assign_eq env n' v hex] at hlookup; exact Option.some.inj hlookup ▸ hv
    | false => rw [Core.Env.lookup_assign_new env n' v hex] at hlookup; exact Option.some.inj hlookup ▸ hv
  · have hne : (n' == name) = false := by
      exact Bool.eq_false_iff.mpr (fun h => heq (beq_iff_eq.mp h))
    rw [Core.Env.lookup_assign_ne env name n' v hne] at hlookup
    exact h n' v' hlookup

private theorem EnvAddrWF_empty (n : Nat) : EnvAddrWF Core.Env.empty n := by
  intro name v h; simp [Core.Env.empty, Core.Env.lookup] at h

/-- Simulation relation for closure conversion: Flat and Core states
    have matching traces, environment correspondence, and expression
    correspondence through the conversion. -/
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  (∃ injMap, HeapInj injMap sc.heap sf.heap ∧ EnvCorrInj injMap sc.env sf.env) ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧
  EnvAddrWF sc.env sc.heap.objects.size ∧
  HeapValuesWF sc.heap ∧
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st

private theorem closureConvert_init_related
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1) :
    CC_SimRel s t (Flat.initialState t) (Core.initialState s) := by
  unfold CC_SimRel Flat.initialState Core.initialState
  refine ⟨rfl, ⟨id, HeapInj_id _, ?_⟩, h_wf, ?_, ?_, ?_, ?_⟩
  · -- EnvCorrInj id: both envs have exactly one binding: "console" → .object 0
    show EnvCorr _ _
    have h_empty : EnvCorr Core.Env.empty Flat.Env.empty := by
      constructor <;> intro _ _ h <;> simp [Core.Env.empty, Core.Env.lookup, Flat.Env.empty, Flat.Env.lookup] at h
    exact EnvCorr_extend h_empty "console" (.object 0)
  · -- ExprAddrWF: source programs don't contain .object addresses
    exact h_addr_wf
  · -- EnvAddrWF: initial env has "console" → .object 0, heap has 1 object
    exact EnvAddrWF_extend (EnvAddrWF_empty 1) "console" (.object 0) (by simp [ValueAddrWF])
  · -- HeapValuesWF: initial heap has console object with log function
    intro addr haddr props hprops kv hkv; dsimp at *; simp_all [ValueAddrWF]; rw [← hprops] at hkv; simp at hkv; subst hkv; trivial
  · unfold Flat.closureConvert at h
    simp only [Except.ok.injEq] at h
    let st2 := (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).fst.foldl
      (fun s f => (s.addFunc f).2) (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).2
    refine ⟨[], "__env_main", [], st2,
      (Flat.convertExpr s.body [] "__env_main" [] st2).2, ?_⟩
    rw [← h]

private theorem coreToFlatValue_eq_convertValue (v : Core.Value) :
    Flat.coreToFlatValue v = Flat.convertValue v := by
  cases v <;> rfl

private theorem flatToCoreValue_convertValue (v : Core.Value) :
    Flat.flatToCoreValue (Flat.convertValue v) = v := by
  cases v <;> rfl

private theorem heapObjectAt?_eq (h : Core.Heap) (addr : Nat) :
    Flat.heapObjectAt? h addr = h.objects[addr]? := by
  unfold Flat.heapObjectAt?
  split
  · rename_i hlt; simp [hlt]
  · rename_i hge; simp [hge]

private theorem convertExpr_not_value (e : Core.Expr)
    (h : Core.exprValue? e = none)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none := by
  cases e with
  | forIn => sorry /- forIn converts to .lit .undefined (stub); theorem false -/
  | forOf => sorry /- forOf converts to .lit .undefined (stub); theorem false -/
  | _ => simp [Core.exprValue?] at h <;> unfold Flat.convertExpr <;>
    (try { simp [Flat.exprValue?]; done }) <;>
    (try { split <;> simp [Flat.exprValue?]; done })

-- Helper lemmas for Core.step? on simple expressions (Core.step? is too large for simp in context)
private theorem Core_step?_this_found (s : Core.State) (v : Core.Value)
    (h : s.env.lookup "this" = some v) :
    Core.step? { s with expr := .this } =
      some (.silent, { expr := .lit v, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, h]

private theorem Core_step?_this_not_found (s : Core.State)
    (h : s.env.lookup "this" = none) :
    Core.step? { s with expr := .this } =
      some (.silent, { expr := .lit .undefined, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, h]

private theorem Flat_step?_lit (s : Flat.State) (v : Flat.Value) :
    Flat.step? { s with expr := .lit v } = none := by
  simp [Flat.step?]

-- Flat.step? explicit field lemmas (step?_this_found uses private pushTrace)
private theorem Flat_step?_this_found_explicit (s : Flat.State) (v : Flat.Value)
    (h : s.env.lookup "this" = some v) :
    Flat.step? { s with expr := .this } =
      some (.silent, { expr := .lit v, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]; rfl

private theorem Flat_step?_this_not_found_explicit (s : Flat.State)
    (h : s.env.lookup "this" = none) :
    Flat.step? { s with expr := .this } =
      some (.silent, { expr := .lit .undefined, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]; rfl

private theorem Flat_step?_var_found_explicit (s : Flat.State) (name : String) (v : Flat.Value)
    (h : s.env.lookup name = some v) :
    Flat.step? { s with expr := .var name } =
      some (.silent, { expr := .lit v, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]; rfl

private theorem Flat_step?_var_not_found_explicit (s : Flat.State) (name : String)
    (h : s.env.lookup name = none) :
    Flat.step? { s with expr := .var name } =
      some (.error ("ReferenceError: " ++ name),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("ReferenceError: " ++ name)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]; rfl

private theorem Core_step?_var_found (s : Core.State) (name : String) (v : Core.Value)
    (h : s.env.lookup name = some v) :
    Core.step? { s with expr := .var name } =
      some (.silent, { expr := .lit v, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, h]

private theorem Core_step?_var_not_found (s : Core.State) (name : String)
    (h : s.env.lookup name = none) :
    Core.step? { s with expr := .var name } =
      some (.error ("ReferenceError: " ++ name),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("ReferenceError: " ++ name)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, h]

private theorem closureConvert_step_simulation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State),
      CC_SimRel s t sf sc → Flat.Step sf ev sf' →
      ∃ sc', Core.Step sc ev sc' ∧ CC_SimRel s t sf' sc' := by
  -- STAGING: proof temporarily sorry'd during HeapInj refactor.
  -- CC_SimRel now bundles ∃ injMap, HeapInj injMap ... ∧ EnvCorrInj injMap ...
  -- The suffices and all ~30 case proofs need injMap threading.
  -- Previous proof (in git history) had 6 sorry cases; will be restored with HeapInj types.
  suffices ∀ (n : Nat) (envVar : String) (envMap : Flat.EnvMapping) (injMap : Nat → Nat)
      (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State),
      sc.expr.depth = n → sf.trace = sc.trace →
      HeapInj injMap sc.heap sf.heap → EnvCorrInj injMap sc.env sf.env →
      EnvAddrWF sc.env sc.heap.objects.size →
      HeapValuesWF sc.heap →
      noCallFrameReturn sc.expr = true →
      ExprAddrWF sc.expr sc.heap.objects.size →
      (∃ (scope : List String) (st st' : Flat.CCState),
        (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st) →
      Flat.Step sf ev sf' →
      ∃ (injMap' : Nat → Nat) (sc' : Core.State), Core.Step sc ev sc' ∧ sf'.trace = sc'.trace ∧
        HeapInj injMap' sc'.heap sf'.heap ∧ EnvCorrInj injMap' sc'.env sf'.env ∧
        EnvAddrWF sc'.env sc'.heap.objects.size ∧
        HeapValuesWF sc'.heap ∧
        noCallFrameReturn sc'.expr = true ∧
        ExprAddrWF sc'.expr sc'.heap.objects.size ∧
        (∃ (scope : List String) (st st' : Flat.CCState),
          (sf'.expr, st') = Flat.convertExpr sc'.expr scope envVar envMap st) by
    intro sf sc ev sf' ⟨htrace, ⟨injMap, hinj, henv⟩, hncfr, hexprwf, henvwf, hheapvwf, scope, envVar, envMap, st, st', hconv⟩ hstep
    obtain ⟨injMap', sc', hcstep, htrace', hinj', henv', henvwf', hheapvwf', hncfr', hexprwf', scope', st_a, st_a', hconv'⟩ :=
      this sc.expr.depth envVar envMap injMap sf sc ev sf' rfl htrace hinj henv henvwf hheapvwf hncfr hexprwf ⟨scope, st, st', hconv⟩ hstep
    exact ⟨sc', hcstep, htrace', ⟨injMap', hinj', henv'⟩, hncfr', hexprwf', henvwf', hheapvwf', scope', envVar, envMap, st_a, st_a', hconv'⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_depth =>
  intro envVar envMap injMap sf sc ev sf' hd htrace hinj henvCorr henvwf hheapvwf hncfr hexprwf ⟨scope, st, st', hconv⟩ ⟨hstep⟩
  -- Case-split on sc.expr to determine sf.expr via convertExpr
  -- Then unfold Flat.step? to analyze the step, construct Core.step? result
  cases hsc : sc.expr with
  | lit v =>
    -- convertExpr (.lit v) = (.lit (convertValue v), st), so sf.expr = .lit (convertValue v)
    -- But Flat.step? of .lit is none → contradicts hstep
    rw [hsc] at hconv
    simp [Flat.convertExpr] at hconv
    have hlit := hconv.1
    have hsf_eta : sf = { sf with expr := .lit (Flat.convertValue v) } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_lit] at hstep
    exact absurd hstep (fun h => nomatch h)
  | var name =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    -- Case split on whether the variable is captured
    cases hlookupEnv : Flat.lookupEnv envMap name with
    | some idx =>
      -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
      simp [hlookupEnv] at hconv
      sorry
    | none =>
      -- Non-captured variable: convertExpr gives .var name (same as Core)
      simp [hlookupEnv] at hconv
      obtain ⟨hfexpr, _⟩ := hconv
      have hsf_eta : sf = { sf with expr := .var name } := by cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Get EnvCorr
      have hec : EnvCorr sc.env sf.env := henvCorr
      obtain ⟨hfwd, hbwd⟩ := hec
      cases hflookup : sf.env.lookup name with
      | some fv =>
        rw [Flat_step?_var_found_explicit _ _ _ hflookup] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        obtain ⟨cv, hclookup, hfvcv⟩ := hfwd name fv hflookup
        let sc' : Core.State := ⟨.lit cv, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hsc' : sc = { sc with expr := .var name } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_var_found _ _ _ hclookup
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF]; exact henvwf name cv hclookup
        · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, hfvcv]⟩
      | none =>
        rw [Flat_step?_var_not_found_explicit _ _ hflookup] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        have hclookup : sc.env.lookup name = none := by
          cases hcl : sc.env.lookup name with
          | none => rfl
          | some cv =>
            obtain ⟨fv', hfl, _⟩ := hbwd name cv hcl
            simp [hflookup] at hfl
        let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap, sc.trace ++ [.error ("ReferenceError: " ++ name)], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hsc' : sc = { sc with expr := .var name } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_var_not_found _ _ hclookup
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF, ValueAddrWF]
        · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, Flat.convertValue]⟩
  | «this» =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, _⟩ := hconv
    have hsf_eta : sf = { sf with expr := .this } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    -- Get EnvCorr
    have hec : EnvCorr sc.env sf.env := henvCorr
    obtain ⟨hfwd, hbwd⟩ := hec
    cases hflookup : sf.env.lookup "this" with
    | some fv =>
      rw [Flat_step?_this_found_explicit _ _ hflookup] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      obtain ⟨cv, hclookup, hfvcv⟩ := hfwd "this" fv hflookup
      let sc' : Core.State := ⟨.lit cv, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hsc' : sc = { sc with expr := .this } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_this_found _ _ hclookup
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF]; exact henvwf "this" cv hclookup
      · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, hfvcv]⟩
    | none =>
      rw [Flat_step?_this_not_found_explicit _ hflookup] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      have hclookup : sc.env.lookup "this" = none := by
        cases hcl : sc.env.lookup "this" with
        | none => rfl
        | some cv =>
          obtain ⟨fv', hfl, _⟩ := hbwd "this" cv hcl
          simp [hflookup] at hfl
      let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hsc' : sc = { sc with expr := .this } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_this_not_found _ hclookup
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF, ValueAddrWF]
      · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, Flat.convertValue]⟩
  | «let» name init body => sorry
  | assign name rhs => sorry
  | «if» cond then_ else_ => sorry
  | seq a b => sorry
  | unary op arg => sorry
  | binary op lhs rhs => sorry
  | call f args => sorry
  | newObj f args => sorry
  | getProp obj prop => sorry
  | setProp obj prop value => sorry
  | getIndex obj idx => sorry
  | setIndex obj idx value => sorry
  | deleteProp obj prop => sorry
  | typeof arg => sorry
  | objectLit props => sorry
  | arrayLit elems => sorry
  | functionDef fname params body isAsync isGen => sorry
  | throw val => sorry
  | tryCatch body catchParam catchBody finally_ => sorry
  | while_ cond body => sorry
  | forIn binding obj body => sorry
  | forOf binding iterable body => sorry
  | «break» label =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«break» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    -- Flat step: break label => error "break:" ++ label.getD ""
    have hfs : Flat.step? { sf with expr := .«break» label } =
        some (.error ("break:" ++ (label.getD "")),
          { expr := .lit .undefined, env := sf.env, heap := sf.heap,
            trace := sf.trace ++ [.error ("break:" ++ (label.getD ""))],
            funcs := sf.funcs, callStack := sf.callStack }) := by
      simp [Flat.step?]; rfl
    rw [hfs] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    -- Core step: break label => error (match label ...)
    -- Show the label strings match
    have hlabel_eq : (match label with | some s => "break:" ++ s | none => "break:") =
        "break:" ++ label.getD "" := by
      cases label <;> simp [Option.getD]
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("break:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Core.step? sc = some (.error ("break:" ++ label.getD ""), sc')
      have hsc' : sc = { sc with expr := .«break» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; simp [Core.step?, Core.pushTrace, hlabel_eq]
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, Flat.convertValue]⟩
  | «continue» label =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«continue» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    have hfs : Flat.step? { sf with expr := .«continue» label } =
        some (.error ("continue:" ++ (label.getD "")),
          { expr := .lit .undefined, env := sf.env, heap := sf.heap,
            trace := sf.trace ++ [.error ("continue:" ++ (label.getD ""))],
            funcs := sf.funcs, callStack := sf.callStack }) := by
      simp [Flat.step?]; rfl
    rw [hfs] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    have hlabel_eq : (match label with | some s => "continue:" ++ s | none => "continue:") =
        "continue:" ++ label.getD "" := by
      cases label <;> simp [Option.getD]
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("continue:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Core.step? sc = some (.error ("continue:" ++ label.getD ""), sc')
      have hsc' : sc = { sc with expr := .«continue» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; simp [Core.step?, Core.pushTrace, hlabel_eq]
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨scope, st, st, by simp [sc', Flat.convertExpr, Flat.convertValue]⟩
  | «return» val => sorry
  | labeled label body =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst'⟩ := hconv
    -- sf.expr = .labeled label body' where (body', st1) = convertExpr body ...
    have hsf_eta : sf = { sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).fst } := by
      cases sf; simp_all
    rw [hsf_eta] at hstep
    have hfs : Flat.step? { sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).fst } =
        some (.silent, { expr := (Flat.convertExpr body scope envVar envMap st).fst,
          env := sf.env, heap := sf.heap,
          trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
      simp [Flat.step?]; rfl
    rw [hfs] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State := ⟨body, sc.env, sc.heap,
      sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Core.step? sc = some (.silent, sc')
      have hsc' : sc = { sc with expr := .labeled label body } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; simp [Core.step?, Core.pushTrace]
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · show noCallFrameReturn sc'.expr = true
      simp [sc']; exact hncfr
    · show ExprAddrWF sc'.expr sc'.heap.objects.size
      simp [sc']; exact hexprwf
    · exact ⟨scope, st, (Flat.convertExpr body scope envVar envMap st).snd, by simp [sc']⟩
  | yield arg delegate => sorry
  | await arg => sorry
/-! ### step?_none_implies_lit -/

/-- The only Flat expression where step? returns none is a literal value. -/
private theorem step?_none_implies_lit_aux :
    ∀ (n : Nat) (s : Flat.State),
      s.expr.depth ≤ n → Flat.step? s = none → ∃ v, s.expr = .lit v := by
  intro n
  induction n with
  | zero =>
    intro ⟨fexpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ hd h
    cases fexpr with
    | lit v => exact ⟨v, rfl⟩
    | var _ => exfalso; unfold Flat.step? at h; split at h <;> simp at h
    | this => exfalso; unfold Flat.step? at h; split at h <;> simp at h
    | «break» _ => exfalso; simp [Flat.step?] at h
    | «continue» _ => exfalso; simp [Flat.step?] at h
    | «return» arg =>
      cases arg with
      | none => exfalso; simp [Flat.step?] at h
      | some => exfalso; simp [Flat.Expr.depth] at hd
    | yield arg _ =>
      cases arg with
      | none => exfalso; simp [Flat.step?] at h
      | some => exfalso; simp [Flat.Expr.depth] at hd
    | tryCatch _ _ _ f => exfalso; cases f <;> simp [Flat.Expr.depth] at hd
    | _ => exfalso; simp [Flat.Expr.depth] at hd
  | succ k ih =>
    intro ⟨fexpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ hd h
    cases fexpr with
    | lit v => exact ⟨v, rfl⟩
    | var _ => exfalso; unfold Flat.step? at h; split at h <;> simp at h
    | this => exfalso; unfold Flat.step? at h; split at h <;> simp at h
    | «break» _ => exfalso; simp [Flat.step?] at h
    | «continue» _ => exfalso; simp [Flat.step?] at h
    | while_ _ _ => exfalso; simp [Flat.step?] at h
    | labeled _ _ => exfalso; simp [Flat.step?] at h
    | seq a b =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨a, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | «let» _name init _body =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨init, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | assign _name value =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨value, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | «if» cond _then_ _else_ =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨cond, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | unary _op arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | typeof arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | throw arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | await arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    -- Multi-branch exprValue? constructors: case split on exprValue? first,
    -- then unfold step? and use the known exprValue? result to simplify.
    | getProp obj _prop =>
      exfalso
      cases hev : Flat.exprValue? obj with
      | some v =>
        unfold Flat.step? at h; simp only [hev] at h
        split at h <;> contradiction
      | none =>
        cases hstep : Flat.step? ⟨obj, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | deleteProp obj _prop =>
      exfalso
      cases hev : Flat.exprValue? obj with
      | some v =>
        unfold Flat.step? at h; simp only [hev] at h
        split at h <;> contradiction
      | none =>
        cases hstep : Flat.step? ⟨obj, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | makeClosure _idx envExpr =>
      exfalso
      cases hev : Flat.exprValue? envExpr with
      | some v =>
        unfold Flat.step? at h; simp only [hev] at h
        split at h <;> contradiction
      | none =>
        cases hstep : Flat.step? ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | getEnv envExpr _idx =>
      exfalso
      cases hev : Flat.exprValue? envExpr with
      | some v =>
        unfold Flat.step? at h; simp only [hev] at h
        repeat (first | contradiction | split at h)
      | none =>
        cases hstep : Flat.step? ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | «return» arg =>
      cases arg with
      | none => exfalso; simp [Flat.step?] at h
      | some e =>
        exfalso
        cases hev : Flat.exprValue? e with
        | some v =>
          unfold Flat.step? at h; simp only [hev] at h; contradiction
        | none =>
          cases hstep : Flat.step? ⟨e, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
          | none =>
            have ⟨v, hv⟩ := ih ⟨e, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | yield arg _delegate =>
      cases arg with
      | none => exfalso; simp [Flat.step?] at h
      | some e =>
        exfalso
        cases hev : Flat.exprValue? e with
        | some v =>
          unfold Flat.step? at h; simp only [hev] at h; contradiction
        | none =>
          cases hstep : Flat.step? ⟨e, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
          | none =>
            have ⟨v, hv⟩ := ih ⟨e, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | binary _op lhs rhs =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevl =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨lhs, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevl; simp [Flat.exprValue?] at hevl
      next _ =>
        split at h
        next hevr =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨rhs, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hevr; simp [Flat.exprValue?] at hevr
        next => simp at h
    | setProp obj _prop value =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevo =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevo; simp [Flat.exprValue?] at hevo
      next _ =>
        split at h
        next => simp at h
        next hevv =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨value, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hevv; simp [Flat.exprValue?] at hevv
      next => simp at h
    | getIndex obj idx =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevo =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevo; simp [Flat.exprValue?] at hevo
      next _ =>
        split at h
        next => simp at h
        next hevi =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨idx, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hevi; simp [Flat.exprValue?] at hevi
      next => simp at h
    | setIndex obj idx value =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevo =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevo; simp [Flat.exprValue?] at hevo
      next _ =>
        split at h
        next hevi =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨idx, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hevi; simp [Flat.exprValue?] at hevi
        next _ =>
          split at h
          next => simp at h
          next hevv =>
            split at h
            next => simp at h
            next hstep =>
              have ⟨v, hv⟩ := ih ⟨value, fenv, fheap, ftrace, ffuncs, fcallStack⟩
                (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
              simp at hv; rw [hv] at hevv; simp [Flat.exprValue?] at hevv
      next => simp at h
    | tryCatch body _catchParam _catchBody _finally_ =>
      exfalso; unfold Flat.step? at h
      split at h
      next =>
        split at h <;> simp at h
      next hev =>
        split at h
        next => simp at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨body, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by cases _finally_ <;> simp [Flat.Expr.depth] at hd ⊢ <;> omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    -- List-based constructors: derive contradiction via IH + key lemmas.
    -- For each: valuesFromExprList? = some → step? some (contradiction).
    --   valuesFromExprList? = none ∧ firstNonValueExpr = none → contradiction via key lemma.
    --   valuesFromExprList? = none ∧ firstNonValueExpr = some (_, target, _) ∧ step? target = none
    --     → IH says target is lit, contradicts firstNonValueExpr_not_lit.
    --   valuesFromExprList? = none ∧ firstNonValueExpr = some ∧ step? target = some → step? some (contradiction).
    | call funcExpr envExpr args =>
      exfalso
      cases hevf : Flat.exprValue? funcExpr with
      | none =>
        cases hstepf : Flat.step? ⟨funcExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hevf, hstepf] at h; exact absurd h (by simp)
        | none =>
          have ⟨v, hv⟩ := ih ⟨funcExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepf
          simp at hv; rw [hv] at hevf; simp [Flat.exprValue?] at hevf
      | some vf =>
        cases heve : Flat.exprValue? envExpr with
        | none =>
          cases hstepe : Flat.step? ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hevf, heve, hstepe] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepe
            simp at hv; rw [hv] at heve; simp [Flat.exprValue?] at heve
        | some ve =>
          cases hvals : Flat.valuesFromExprList? args with
          | some vs =>
            unfold Flat.step? at h; simp only [hevf, heve, hvals] at h; exact absurd h (by simp)
          | none =>
            cases hf : Flat.firstNonValueExpr args with
            | none =>
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values args hf
              simp [hvs] at hvals
            | some val =>
              obtain ⟨done, target, remaining⟩ := val
              cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
              | some r =>
                unfold Flat.step? at h; simp only [hevf, heve, hvals] at h
                rw [show Flat.firstNonValueExpr args = some (done, target, remaining) from hf] at h
                simp only [hstept] at h; exact absurd h (by simp)
              | none =>
                have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩
                  (by simp [Flat.Expr.depth] at hd ⊢
                      have := Flat.firstNonValueExpr_depth hf; omega) hstept
                exact absurd hv (firstNonValueExpr_not_lit hf v)
    | newObj funcExpr envExpr args =>
      exfalso
      cases hevf : Flat.exprValue? funcExpr with
      | none =>
        cases hstepf : Flat.step? ⟨funcExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hevf, hstepf] at h; exact absurd h (by simp)
        | none =>
          have ⟨v, hv⟩ := ih ⟨funcExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepf
          simp at hv; rw [hv] at hevf; simp [Flat.exprValue?] at hevf
      | some vf =>
        cases heve : Flat.exprValue? envExpr with
        | none =>
          cases hstepe : Flat.step? ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hevf, heve, hstepe] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepe
            simp at hv; rw [hv] at heve; simp [Flat.exprValue?] at heve
        | some ve =>
          cases hvals : Flat.valuesFromExprList? args with
          | some vs =>
            unfold Flat.step? at h; simp only [hevf, heve, hvals] at h; exact absurd h (by simp)
          | none =>
            cases hf : Flat.firstNonValueExpr args with
            | none =>
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values args hf
              simp [hvs] at hvals
            | some val =>
              obtain ⟨done, target, remaining⟩ := val
              cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
              | some r =>
                unfold Flat.step? at h; simp only [hevf, heve, hvals] at h
                rw [show Flat.firstNonValueExpr args = some (done, target, remaining) from hf] at h
                simp only [hstept] at h; exact absurd h (by simp)
              | none =>
                have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩
                  (by simp [Flat.Expr.depth] at hd ⊢
                      have := Flat.firstNonValueExpr_depth hf; omega) hstept
                exact absurd hv (firstNonValueExpr_not_lit hf v)
    | makeEnv values =>
      exfalso
      cases hvals : Flat.valuesFromExprList? values with
      | some vs =>
        unfold Flat.step? at h; simp only [hvals] at h; exact absurd h (by simp)
      | none =>
        cases hf : Flat.firstNonValueExpr values with
        | none =>
          have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values values hf
          simp [hvs] at hvals
        | some val =>
          obtain ⟨done, target, remaining⟩ := val
          cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hvals] at h
            rw [show Flat.firstNonValueExpr values = some (done, target, remaining) from hf] at h
            simp only [hstept] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢
                  have := Flat.firstNonValueExpr_depth hf; omega) hstept
            exact absurd hv (firstNonValueExpr_not_lit hf v)
    | objectLit props =>
      exfalso
      cases hvals : Flat.valuesFromExprList? (props.map Prod.snd) with
      | some vs =>
        unfold Flat.step? at h; simp only [hvals] at h; exact absurd h (by simp)
      | none =>
        cases hf : Flat.firstNonValueProp props with
        | none =>
          have ⟨vs, hvs⟩ := firstNonValueProp_none_implies_values props hf
          simp [hvs] at hvals
        | some val =>
          obtain ⟨done, propName, target, remaining⟩ := val
          cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hvals] at h
            rw [show Flat.firstNonValueProp props = some (done, propName, target, remaining) from hf] at h
            simp only [hstept] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢
                  have := Flat.firstNonValueProp_depth hf; omega) hstept
            exact absurd hv (firstNonValueProp_not_lit hf v)
    | arrayLit elems =>
      exfalso
      cases hvals : Flat.valuesFromExprList? elems with
      | some vs =>
        unfold Flat.step? at h; simp only [hvals] at h; exact absurd h (by simp)
      | none =>
        cases hf : Flat.firstNonValueExpr elems with
        | none =>
          have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values elems hf
          simp [hvs] at hvals
        | some val =>
          obtain ⟨done, target, remaining⟩ := val
          cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hvals] at h
            rw [show Flat.firstNonValueExpr elems = some (done, target, remaining) from hf] at h
            simp only [hstept] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢
                  have := Flat.firstNonValueExpr_depth hf; omega) hstept
            exact absurd hv (firstNonValueExpr_not_lit hf v)

private theorem step?_none_implies_lit (s : Flat.State) (h : Flat.step? s = none) :
    ∃ v, s.expr = .lit v :=
  step?_none_implies_lit_aux s.expr.depth s (Nat.le_refl _) h

/-- Halt preservation with precondition excluding forIn/forOf
    (unimplemented in closure conversion — stubbed to .lit .undefined). -/
private theorem closureConvert_halt_preservation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ sf sc, CC_SimRel s t sf sc → Flat.step? sf = none →
      (∀ (b : String) (o f : Core.Expr), sc.expr ≠ .forIn b o f) →
      (∀ (b : String) (i f : Core.Expr), sc.expr ≠ .forOf b i f) →
      Core.step? sc = none := by
  intro sf sc ⟨htrace, _, _hncfr, _hexprwf, _henvwf, _hheapvwf, scope, envVar, envMap, st, st', hconv⟩ hhalt hnoForIn hnoForOf
  obtain ⟨v, hlit⟩ := step?_none_implies_lit sf hhalt
  rw [hlit] at hconv
  cases hsc : sc.expr with
  | lit w =>
    have hsc' : sc = { sc with expr := .lit w } := by cases sc; simp_all
    rw [hsc']; simp [Core.step?]
  | var name =>
    exfalso; rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    split at hconv <;> simp [Prod.mk.injEq] at hconv
  | forIn b o f => exact absurd hsc (hnoForIn b o f)
  | forOf b i f => exact absurd hsc (hnoForOf b i f)
  | functionDef _ _ _ _ _ =>
    exfalso; rw [hsc] at hconv; unfold Flat.convertExpr at hconv
    simp [Prod.mk.injEq] at hconv
  | _ =>
    all_goals (exfalso; rw [hsc] at hconv; simp [Flat.convertExpr, Prod.mk.injEq] at hconv)

private theorem closureConvert_steps_simulation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ (sf : Flat.State) (sc : Core.State) (tr : List Core.TraceEvent) (sf' : Flat.State),
      CC_SimRel s t sf sc → Flat.Steps sf tr sf' →
      ∃ sc', Core.Steps sc tr sc' ∧ CC_SimRel s t sf' sc' := by
  intro sf sc tr sf' hrel hsteps
  induction hsteps generalizing sc with
  | refl => exact ⟨sc, .refl sc, hrel⟩
  | tail hstep _ ih =>
    obtain ⟨sc2, hcstep, hrel2⟩ := closureConvert_step_simulation s t h _ _ _ _ hrel hstep
    obtain ⟨sc3, hcsteps, hrel3⟩ := ih sc2 hrel2
    exact ⟨sc3, .tail hcstep hcsteps, hrel3⟩

private theorem closureConvert_trace_reflection
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → Core.Behaves s b := by
  intro b ⟨sf, hsteps, hhalt⟩
  have hinit := closureConvert_init_related s t h h_wf h_addr_wf
  obtain ⟨sc, hcsteps, hrel⟩ :=
    closureConvert_steps_simulation s t h _ _ _ _ hinit hsteps
  have hnoFor := hnofor sc _ hcsteps
  exact ⟨sc, hcsteps,
    closureConvert_halt_preservation s t h _ _ hrel hhalt hnoFor.1 hnoFor.2⟩

/-- Closure conversion preserves behavior, assuming the source program
    never reaches a forIn/forOf expression (unimplemented in closure conversion)
    and the source body contains no "__call_frame_return__" catch parameters. -/
theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact closureConvert_trace_reflection s t h h_wf h_addr_wf hnofor b hb

end VerifiedJS.Proofs
