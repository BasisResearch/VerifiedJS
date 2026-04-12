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

/-- If Flat.exprValue? e = none (e is not .lit), then firstNonValueExpr picks e immediately. -/
private theorem Flat_firstNonValueExpr_cons_not_value
    {e : Flat.Expr} (rest : List Flat.Expr)
    (h : Flat.exprValue? e = none) :
    Flat.firstNonValueExpr (e :: rest) = some ([], e, rest) := by
  cases e with
  | lit v => simp [Flat.exprValue?] at h
  | _ => rfl

/-- If Flat.exprValue? e = none, then firstNonValueProp picks (name, e) immediately. -/
private theorem Flat_firstNonValueProp_cons_not_value
    (name : Flat.PropName) {e : Flat.Expr} (rest : List (Flat.PropName × Flat.Expr))
    (h : Flat.exprValue? e = none) :
    Flat.firstNonValueProp ((name, e) :: rest) = some ([], name, e, rest) := by
  cases e with
  | lit v => simp [Flat.exprValue?] at h
  | _ => rfl

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

/-! ### CCState determination: convertExpr output depends only on nextId and funcs.size.

  Two `CCState`s that agree on `nextId` and `funcs.size` produce the same
  output expression from `convertExpr`, and the resulting states again agree
  on `nextId` and `funcs.size`.  This is the key lemma needed for the
  CCState-threading sorry cases: after an inner sub-expression steps, the
  second sub-expression's conversion result is unchanged because only
  `nextId` and `funcs.size` matter. -/

private abbrev CCStateAgree (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId = st2.nextId ∧ st1.funcs.size = st2.funcs.size

/-- Weak version of CCStateAgree: first state's counters are ≤ second's. -/
private abbrev CCStateAgreeWeak (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId ≤ st2.nextId ∧ st1.funcs.size ≤ st2.funcs.size

mutual
private theorem convertExpr_state_determined (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hid : st1.nextId = st2.nextId) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertExpr e scope envVar envMap st1).fst = (Flat.convertExpr e scope envVar envMap st2).fst ∧
    CCStateAgree (Flat.convertExpr e scope envVar envMap st1).snd (Flat.convertExpr e scope envVar envMap st2).snd := by
  cases e with
  | lit v => simp [Flat.convertExpr, CCStateAgree, hid, hsz]
  | var n =>
    simp only [Flat.convertExpr]
    cases Flat.lookupEnv envMap n <;> simp [CCStateAgree, hid, hsz]
  | this => simp [Flat.convertExpr, CCStateAgree, hid, hsz]
  | «break» l => simp [Flat.convertExpr, CCStateAgree, hid, hsz]
  | «continue» l => simp [Flat.convertExpr, CCStateAgree, hid, hsz]
  | forIn _ _ _ => simp [Flat.convertExpr, CCStateAgree, hid, hsz]
  | forOf _ _ _ => simp [Flat.convertExpr, CCStateAgree, hid, hsz]
  | «let» name init body =>
    simp only [Flat.convertExpr]
    have hi := convertExpr_state_determined init scope envVar envMap st1 st2 hid hsz
    have hb := convertExpr_state_determined body (name :: scope) envVar envMap _ _ hi.2.1 hi.2.2
    exact ⟨by rw [hi.1, hb.1], hb.2⟩
  | assign name value =>
    simp only [Flat.convertExpr]
    have hv := convertExpr_state_determined value scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [hv.1], hv.2⟩
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_determined cond scope envVar envMap st1 st2 hid hsz
    have ht := convertExpr_state_determined then_ scope envVar envMap _ _ hc.2.1 hc.2.2
    have he := convertExpr_state_determined else_ scope envVar envMap _ _ ht.2.1 ht.2.2
    exact ⟨by rw [hc.1, ht.1, he.1], he.2⟩
  | seq a b =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_state_determined a scope envVar envMap st1 st2 hid hsz
    have hb := convertExpr_state_determined b scope envVar envMap _ _ ha.2.1 ha.2.2
    exact ⟨by rw [ha.1, hb.1], hb.2⟩
  | call callee args =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_determined callee scope envVar envMap st1 st2 hid hsz
    have ha := convertExprList_state_determined args scope envVar envMap _ _ hc.2.1 hc.2.2
    exact ⟨by rw [hc.1, ha.1], ha.2⟩
  | newObj callee args =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_determined callee scope envVar envMap st1 st2 hid hsz
    have ha := convertExprList_state_determined args scope envVar envMap _ _ hc.2.1 hc.2.2
    exact ⟨by rw [hc.1, ha.1], ha.2⟩
  | getProp obj prop =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_determined obj scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ho.1], ho.2⟩
  | setProp obj prop value =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_determined obj scope envVar envMap st1 st2 hid hsz
    have hv := convertExpr_state_determined value scope envVar envMap _ _ ho.2.1 ho.2.2
    exact ⟨by rw [ho.1, hv.1], hv.2⟩
  | getIndex obj idx =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_determined obj scope envVar envMap st1 st2 hid hsz
    have hi := convertExpr_state_determined idx scope envVar envMap _ _ ho.2.1 ho.2.2
    exact ⟨by rw [ho.1, hi.1], hi.2⟩
  | setIndex obj idx value =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_determined obj scope envVar envMap st1 st2 hid hsz
    have hi := convertExpr_state_determined idx scope envVar envMap _ _ ho.2.1 ho.2.2
    have hv := convertExpr_state_determined value scope envVar envMap _ _ hi.2.1 hi.2.2
    exact ⟨by rw [ho.1, hi.1, hv.1], hv.2⟩
  | deleteProp obj prop =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_determined obj scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ho.1], ho.2⟩
  | typeof arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_state_determined arg scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | unary op arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_state_determined arg scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | binary op lhs rhs =>
    simp only [Flat.convertExpr]
    have hl := convertExpr_state_determined lhs scope envVar envMap st1 st2 hid hsz
    have hr := convertExpr_state_determined rhs scope envVar envMap _ _ hl.2.1 hl.2.2
    exact ⟨by rw [hl.1, hr.1], hr.2⟩
  | objectLit props =>
    simp only [Flat.convertExpr]
    have hp := convertPropList_state_determined props scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [hp.1], hp.2⟩
  | arrayLit elems =>
    simp only [Flat.convertExpr]
    have he := convertExprList_state_determined elems scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [he.1], he.2⟩
  | functionDef fname params body _isAsync _isGenerator =>
    -- freshVar/addFunc depend only on nextId/funcs.size. After unfold+simp[hid], nextId is aligned.
    unfold Flat.convertExpr
    simp only [Flat.CCState.freshVar, Flat.CCState.addFunc, hid]
    -- IH for body conversion: states { funcs := st1.funcs, nextId := st2.nextId + 1 } and
    -- { funcs := st2.funcs, nextId := st2.nextId + 1 } agree on nextId (rfl) and funcs.size (hsz).
    have ih := convertExpr_state_determined body params
      (toString "__env" ++ toString "_" ++ toString st2.nextId)
      (Flat.indexedMap
        (Flat.dedupStrings
          (match fname with
          | some n => List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))
          | none => List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
      { funcs := st1.funcs, nextId := st2.nextId + 1 }
      { funcs := st2.funcs, nextId := st2.nextId + 1 } rfl hsz
    obtain ⟨ih_fst, ih_id, ih_sz⟩ := ih
    refine ⟨?_, ih_id, ?_⟩
    · -- .fst: .makeClosure funcIdx envExpr — only funcIdx differs
      show Flat.Expr.makeClosure _ _ = Flat.Expr.makeClosure _ _
      exact congrArg (Flat.Expr.makeClosure · _) ih_sz
    · -- funcs.size: addFunc increments by 1
      show Array.size _ = Array.size _
      simp only [Array.size_push]
      exact congrArg (· + 1) ih_sz
  | throw arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_state_determined arg scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | tryCatch body catchParam catchBody finally_ =>
    simp only [Flat.convertExpr]
    have hb := convertExpr_state_determined body scope envVar envMap st1 st2 hid hsz
    have hc := convertExpr_state_determined catchBody (catchParam :: scope) envVar envMap _ _ hb.2.1 hb.2.2
    have hf := convertOptExpr_state_determined finally_ scope envVar envMap _ _ hc.2.1 hc.2.2
    exact ⟨by rw [hb.1, hc.1, hf.1], hf.2⟩
  | while_ cond body =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_determined cond scope envVar envMap st1 st2 hid hsz
    have hb := convertExpr_state_determined body scope envVar envMap _ _ hc.2.1 hc.2.2
    exact ⟨by rw [hc.1, hb.1], hb.2⟩
  | «return» arg =>
    simp only [Flat.convertExpr]
    have ha := convertOptExpr_state_determined arg scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | labeled label body =>
    simp only [Flat.convertExpr]
    have hb := convertExpr_state_determined body scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [hb.1], hb.2⟩
  | yield arg delegate =>
    simp only [Flat.convertExpr]
    have ha := convertOptExpr_state_determined arg scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | await arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_state_determined arg scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [ha.1], ha.2⟩
  termination_by sizeOf e
  decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_wf <;> omega

private theorem convertExprList_state_determined (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hid : st1.nextId = st2.nextId) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertExprList es scope envVar envMap st1).fst = (Flat.convertExprList es scope envVar envMap st2).fst ∧
    CCStateAgree (Flat.convertExprList es scope envVar envMap st1).snd (Flat.convertExprList es scope envVar envMap st2).snd := by
  cases es with
  | nil => simp [Flat.convertExprList, CCStateAgree, hid, hsz]
  | cons e rest =>
    simp only [Flat.convertExprList]
    have he := convertExpr_state_determined e scope envVar envMap st1 st2 hid hsz
    have hr := convertExprList_state_determined rest scope envVar envMap _ _ he.2.1 he.2.2
    exact ⟨by rw [he.1, hr.1], hr.2⟩
  termination_by sizeOf es
  decreasing_by all_goals (try simp_wf) <;> omega

private theorem convertPropList_state_determined (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hid : st1.nextId = st2.nextId) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertPropList ps scope envVar envMap st1).fst = (Flat.convertPropList ps scope envVar envMap st2).fst ∧
    CCStateAgree (Flat.convertPropList ps scope envVar envMap st1).snd (Flat.convertPropList ps scope envVar envMap st2).snd := by
  cases ps with
  | nil => simp [Flat.convertPropList, CCStateAgree, hid, hsz]
  | cons p rest =>
    obtain ⟨pn, pe⟩ := p
    simp only [Flat.convertPropList]
    have he := convertExpr_state_determined pe scope envVar envMap st1 st2 hid hsz
    have hr := convertPropList_state_determined rest scope envVar envMap _ _ he.2.1 he.2.2
    exact ⟨by rw [he.1, hr.1], hr.2⟩
  termination_by sizeOf ps
  decreasing_by all_goals (try simp_wf) <;> omega

private theorem convertOptExpr_state_determined (oe : Option Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hid : st1.nextId = st2.nextId) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertOptExpr oe scope envVar envMap st1).fst = (Flat.convertOptExpr oe scope envVar envMap st2).fst ∧
    CCStateAgree (Flat.convertOptExpr oe scope envVar envMap st1).snd (Flat.convertOptExpr oe scope envVar envMap st2).snd := by
  cases oe with
  | none => simp [Flat.convertOptExpr, CCStateAgree, hid, hsz]
  | some e =>
    simp only [Flat.convertOptExpr]
    have he := convertExpr_state_determined e scope envVar envMap st1 st2 hid hsz
    exact ⟨by rw [he.1], he.2⟩
  termination_by sizeOf oe
  decreasing_by all_goals simp_all <;> omega
end

/-! ### State monotonicity: convertExpr only increments nextId and appends to funcs -/

mutual
theorem convertExpr_state_mono (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    st.nextId ≤ (Flat.convertExpr e scope envVar envMap st).snd.nextId ∧
    st.funcs.size ≤ (Flat.convertExpr e scope envVar envMap st).snd.funcs.size := by
  cases e with
  | lit v => simp [Flat.convertExpr]
  | var n => simp only [Flat.convertExpr]; cases Flat.lookupEnv envMap n <;> simp
  | this => simp [Flat.convertExpr]
  | «break» l => simp [Flat.convertExpr]
  | «continue» l => simp [Flat.convertExpr]
  | forIn _ _ _ => simp [Flat.convertExpr]
  | forOf _ _ _ => simp [Flat.convertExpr]
  | «let» name init body =>
    simp only [Flat.convertExpr]
    have hi := convertExpr_state_mono init scope envVar envMap st
    have hb := convertExpr_state_mono body (name :: scope) envVar envMap
      (Flat.convertExpr init scope envVar envMap st).snd
    exact ⟨Nat.le_trans hi.1 hb.1, Nat.le_trans hi.2 hb.2⟩
  | assign name value =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono value scope envVar envMap st
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_mono cond scope envVar envMap st
    have ht := convertExpr_state_mono then_ scope envVar envMap
      (Flat.convertExpr cond scope envVar envMap st).snd
    have he := convertExpr_state_mono else_ scope envVar envMap
      (Flat.convertExpr then_ scope envVar envMap
        (Flat.convertExpr cond scope envVar envMap st).snd).snd
    exact ⟨Nat.le_trans (Nat.le_trans hc.1 ht.1) he.1,
           Nat.le_trans (Nat.le_trans hc.2 ht.2) he.2⟩
  | seq a b =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_state_mono a scope envVar envMap st
    have hb := convertExpr_state_mono b scope envVar envMap
      (Flat.convertExpr a scope envVar envMap st).snd
    exact ⟨Nat.le_trans ha.1 hb.1, Nat.le_trans ha.2 hb.2⟩
  | call callee args =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_mono callee scope envVar envMap st
    have ha := convertExprList_state_mono args scope envVar envMap
      (Flat.convertExpr callee scope envVar envMap st).snd
    exact ⟨Nat.le_trans hc.1 ha.1, Nat.le_trans hc.2 ha.2⟩
  | newObj callee args =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_mono callee scope envVar envMap st
    have ha := convertExprList_state_mono args scope envVar envMap
      (Flat.convertExpr callee scope envVar envMap st).snd
    exact ⟨Nat.le_trans hc.1 ha.1, Nat.le_trans hc.2 ha.2⟩
  | getProp obj prop =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono obj scope envVar envMap st
  | setProp obj prop value =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_mono obj scope envVar envMap st
    have hv := convertExpr_state_mono value scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st).snd
    exact ⟨Nat.le_trans ho.1 hv.1, Nat.le_trans ho.2 hv.2⟩
  | getIndex obj idx =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_mono obj scope envVar envMap st
    have hi := convertExpr_state_mono idx scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st).snd
    exact ⟨Nat.le_trans ho.1 hi.1, Nat.le_trans ho.2 hi.2⟩
  | setIndex obj idx value =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_state_mono obj scope envVar envMap st
    have hi := convertExpr_state_mono idx scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st).snd
    have hv := convertExpr_state_mono value scope envVar envMap
      (Flat.convertExpr idx scope envVar envMap
        (Flat.convertExpr obj scope envVar envMap st).snd).snd
    exact ⟨Nat.le_trans (Nat.le_trans ho.1 hi.1) hv.1,
           Nat.le_trans (Nat.le_trans ho.2 hi.2) hv.2⟩
  | deleteProp obj prop =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono obj scope envVar envMap st
  | typeof arg =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono arg scope envVar envMap st
  | unary op arg =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono arg scope envVar envMap st
  | binary op lhs rhs =>
    simp only [Flat.convertExpr]
    have hl := convertExpr_state_mono lhs scope envVar envMap st
    have hr := convertExpr_state_mono rhs scope envVar envMap
      (Flat.convertExpr lhs scope envVar envMap st).snd
    exact ⟨Nat.le_trans hl.1 hr.1, Nat.le_trans hl.2 hr.2⟩
  | objectLit props =>
    simp only [Flat.convertExpr]
    exact convertPropList_state_mono props scope envVar envMap st
  | arrayLit elems =>
    simp only [Flat.convertExpr]
    exact convertExprList_state_mono elems scope envVar envMap st
  | functionDef fname params body _isAsync _isGenerator =>
    unfold Flat.convertExpr
    simp only [Flat.CCState.freshVar, Flat.CCState.addFunc]
    have ih := convertExpr_state_mono body params
      (toString "__env" ++ toString "_" ++ toString st.nextId)
      (Flat.indexedMap
        (Flat.dedupStrings
          (match fname with
          | some n => List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))
          | none => List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
      { st with nextId := st.nextId + 1 }
    constructor
    · exact Nat.le_trans (Nat.le_succ _) ih.1
    · show st.funcs.size ≤ Array.size (Array.push _ _)
      simp only [Array.size_push]
      exact Nat.le_trans ih.2 (Nat.le_succ _)
  | throw arg =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono arg scope envVar envMap st
  | tryCatch body catchParam catchBody finally_ =>
    simp only [Flat.convertExpr]
    have hb := convertExpr_state_mono body scope envVar envMap st
    have hc := convertExpr_state_mono catchBody (catchParam :: scope) envVar envMap
      (Flat.convertExpr body scope envVar envMap st).snd
    have hf := convertOptExpr_state_mono finally_ scope envVar envMap
      (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap
        (Flat.convertExpr body scope envVar envMap st).snd).snd
    exact ⟨Nat.le_trans (Nat.le_trans hb.1 hc.1) hf.1,
           Nat.le_trans (Nat.le_trans hb.2 hc.2) hf.2⟩
  | while_ cond body =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_state_mono cond scope envVar envMap st
    have hb := convertExpr_state_mono body scope envVar envMap
      (Flat.convertExpr cond scope envVar envMap st).snd
    exact ⟨Nat.le_trans hc.1 hb.1, Nat.le_trans hc.2 hb.2⟩
  | «return» arg =>
    simp only [Flat.convertExpr]
    exact convertOptExpr_state_mono arg scope envVar envMap st
  | labeled label body =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono body scope envVar envMap st
  | yield arg delegate =>
    simp only [Flat.convertExpr]
    exact convertOptExpr_state_mono arg scope envVar envMap st
  | await arg =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_mono arg scope envVar envMap st
  termination_by sizeOf e
  decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_wf <;> omega

theorem convertExprList_state_mono (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    st.nextId ≤ (Flat.convertExprList es scope envVar envMap st).snd.nextId ∧
    st.funcs.size ≤ (Flat.convertExprList es scope envVar envMap st).snd.funcs.size := by
  cases es with
  | nil => simp [Flat.convertExprList]
  | cons e rest =>
    simp only [Flat.convertExprList]
    have he := convertExpr_state_mono e scope envVar envMap st
    have hr := convertExprList_state_mono rest scope envVar envMap
      (Flat.convertExpr e scope envVar envMap st).snd
    exact ⟨Nat.le_trans he.1 hr.1, Nat.le_trans he.2 hr.2⟩
  termination_by sizeOf es
  decreasing_by all_goals (try simp_wf) <;> omega

theorem convertPropList_state_mono (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    st.nextId ≤ (Flat.convertPropList ps scope envVar envMap st).snd.nextId ∧
    st.funcs.size ≤ (Flat.convertPropList ps scope envVar envMap st).snd.funcs.size := by
  cases ps with
  | nil => simp [Flat.convertPropList]
  | cons p rest =>
    obtain ⟨pn, pe⟩ := p
    simp only [Flat.convertPropList]
    have he := convertExpr_state_mono pe scope envVar envMap st
    have hr := convertPropList_state_mono rest scope envVar envMap
      (Flat.convertExpr pe scope envVar envMap st).snd
    exact ⟨Nat.le_trans he.1 hr.1, Nat.le_trans he.2 hr.2⟩
  termination_by sizeOf ps
  decreasing_by all_goals (try simp_wf) <;> omega

theorem convertOptExpr_state_mono (oe : Option Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    st.nextId ≤ (Flat.convertOptExpr oe scope envVar envMap st).snd.nextId ∧
    st.funcs.size ≤ (Flat.convertOptExpr oe scope envVar envMap st).snd.funcs.size := by
  cases oe with
  | none => simp [Flat.convertOptExpr]
  | some e =>
    simp only [Flat.convertOptExpr]
    exact convertExpr_state_mono e scope envVar envMap st
  termination_by sizeOf oe
  decreasing_by all_goals simp_all <;> omega
end

/-! ### Key insight: only functionDef cases modify CCState (nextId, funcs).
    convertExpr for all other expression forms threads state through unchanged.
    Formalized below as `convertExpr_state_id_no_functionDef`:
    if `noFunctionDef e`, then `(convertExpr e ... st).snd = st`. -/

/-! ### noFunctionDef predicate: expression contains no functionDef nodes -/

mutual
def noFunctionDef : Core.Expr → Bool
  | .functionDef _ _ _ _ _ => false
  | .seq a b => noFunctionDef a && noFunctionDef b
  | .«let» _ i b => noFunctionDef i && noFunctionDef b
  | .«if» c t e => noFunctionDef c && noFunctionDef t && noFunctionDef e
  | .while_ c b => noFunctionDef c && noFunctionDef b
  | .tryCatch b _ c f => noFunctionDef b && noFunctionDef c &&
      (match f with | some x => noFunctionDef x | none => true)
  | .call f args => noFunctionDef f && listNoFunctionDef args
  | .newObj f args => noFunctionDef f && listNoFunctionDef args
  | .objectLit ps => propListNoFunctionDef ps
  | .arrayLit es => listNoFunctionDef es
  | .assign _ v => noFunctionDef v
  | .getProp o _ => noFunctionDef o
  | .setProp o _ v => noFunctionDef o && noFunctionDef v
  | .getIndex o i => noFunctionDef o && noFunctionDef i
  | .setIndex o i v => noFunctionDef o && noFunctionDef i && noFunctionDef v
  | .deleteProp o _ => noFunctionDef o
  | .typeof a => noFunctionDef a
  | .unary _ a => noFunctionDef a
  | .binary _ l r => noFunctionDef l && noFunctionDef r
  | .throw a => noFunctionDef a
  | .forIn _ o b => noFunctionDef o && noFunctionDef b
  | .forOf _ i b => noFunctionDef i && noFunctionDef b
  | .labeled _ b => noFunctionDef b
  | .«return» arg => match arg with | some e => noFunctionDef e | none => true
  | .yield arg _ => match arg with | some e => noFunctionDef e | none => true
  | .await a => noFunctionDef a
  | _ => true
def listNoFunctionDef : List Core.Expr → Bool
  | [] => true
  | e :: rest => noFunctionDef e && listNoFunctionDef rest
def propListNoFunctionDef : List (Core.PropName × Core.Expr) → Bool
  | [] => true
  | (_, e) :: rest => noFunctionDef e && propListNoFunctionDef rest
end

/-! ### State identity theorem: noFunctionDef expressions leave CCState unchanged -/

mutual
private theorem convertExpr_state_id_no_functionDef (e : Core.Expr)
    (h : noFunctionDef e = true)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertExpr e scope envVar envMap st).snd = st := by
  cases e with
  | lit _ => simp [Flat.convertExpr]
  | var n => simp only [Flat.convertExpr]; cases Flat.lookupEnv envMap n <;> simp
  | this => simp [Flat.convertExpr]
  | «break» _ => simp [Flat.convertExpr]
  | «continue» _ => simp [Flat.convertExpr]
  | forIn _ _ _ => simp [Flat.convertExpr]
  | forOf _ _ _ => simp [Flat.convertExpr]
  | functionDef _ _ _ _ _ => simp [noFunctionDef] at h
  | «let» name init body =>
    simp only [Flat.convertExpr]
    have hn : noFunctionDef init = true ∧ noFunctionDef body = true := by
      simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have hi := convertExpr_state_id_no_functionDef init hn.1 scope envVar envMap st
    rw [hi]; exact convertExpr_state_id_no_functionDef body hn.2 (name :: scope) envVar envMap st
  | assign _ value =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_id_no_functionDef value (by simp [noFunctionDef] at h; exact h) scope envVar envMap st
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have hc := convertExpr_state_id_no_functionDef cond hn.1.1 scope envVar envMap st; rw [hc]
    have ht := convertExpr_state_id_no_functionDef then_ hn.1.2 scope envVar envMap st; rw [ht]
    exact convertExpr_state_id_no_functionDef else_ hn.2 scope envVar envMap st
  | seq a b =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have ha := convertExpr_state_id_no_functionDef a hn.1 scope envVar envMap st; rw [ha]
    exact convertExpr_state_id_no_functionDef b hn.2 scope envVar envMap st
  | call callee args =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have hc := convertExpr_state_id_no_functionDef callee hn.1 scope envVar envMap st; rw [hc]
    exact convertExprList_state_id_no_functionDef args hn.2 scope envVar envMap st
  | newObj callee args =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have hc := convertExpr_state_id_no_functionDef callee hn.1 scope envVar envMap st; rw [hc]
    exact convertExprList_state_id_no_functionDef args hn.2 scope envVar envMap st
  | getProp obj _ =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_id_no_functionDef obj (by simp [noFunctionDef] at h; exact h) scope envVar envMap st
  | setProp obj _ value =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have ho := convertExpr_state_id_no_functionDef obj hn.1 scope envVar envMap st; rw [ho]
    exact convertExpr_state_id_no_functionDef value hn.2 scope envVar envMap st
  | getIndex obj idx =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have ho := convertExpr_state_id_no_functionDef obj hn.1 scope envVar envMap st; rw [ho]
    exact convertExpr_state_id_no_functionDef idx hn.2 scope envVar envMap st
  | setIndex obj idx value =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have ho := convertExpr_state_id_no_functionDef obj hn.1.1 scope envVar envMap st; rw [ho]
    have hi := convertExpr_state_id_no_functionDef idx hn.1.2 scope envVar envMap st; rw [hi]
    exact convertExpr_state_id_no_functionDef value hn.2 scope envVar envMap st
  | deleteProp obj _ =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_id_no_functionDef obj (by simp [noFunctionDef] at h; exact h) scope envVar envMap st
  | typeof arg =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_id_no_functionDef arg (by simp [noFunctionDef] at h; exact h) scope envVar envMap st
  | unary _ arg =>
    simp only [Flat.convertExpr]
    exact convertExpr_state_id_no_functionDef arg (by simp [noFunctionDef] at h; exact h) scope envVar envMap st
  | binary _ lhs rhs =>
    simp only [Flat.convertExpr]
    have hn := by simp [noFunctionDef, Bool.and_eq_true] at h; exact h
    have hl := convertExpr_state_id_no_functionDef lhs hn.1 scope envVar envMap st; rw [hl]
    exact convertExpr_state_id_no_functionDef rhs hn.2 scope envVar envMap st
  | objectLit props =>
    simp only [Flat.convertExpr]
    exact convertPropList_state_id_no_functionDef props (by simp [noFunctionDef] at h; exact h) scope envVar envMap st
  | arrayLit elems =>
    simp only [Flat.convertExpr]
    exact convertExprList_state_id_no_functionDef elems (by simp [noFunctionDef] at h; exact h) scope envVar envMap st
  | throw arg =>
    simp only [Flat.convertExpr]
    have ha : noFunctionDef arg = true := by unfold noFunctionDef at h; exact h
    exact convertExpr_state_id_no_functionDef arg ha scope envVar envMap st
  | tryCatch body catchParam catchBody finally_ =>
    simp only [Flat.convertExpr]
    have hb : noFunctionDef body = true := by
      unfold noFunctionDef at h; simp [Bool.and_eq_true] at h; exact h.1.1
    have hc : noFunctionDef catchBody = true := by
      unfold noFunctionDef at h; simp [Bool.and_eq_true] at h; exact h.1.2
    have hb' := convertExpr_state_id_no_functionDef body hb scope envVar envMap st; rw [hb']
    have hc' := convertExpr_state_id_no_functionDef catchBody hc (catchParam :: scope) envVar envMap st; rw [hc']
    cases finally_ with
    | none => simp [Flat.convertOptExpr]
    | some fin =>
      simp only [Flat.convertOptExpr]
      have hfin : noFunctionDef fin = true := by
        unfold noFunctionDef at h; simp [Bool.and_eq_true] at h; exact h.2
      exact convertExpr_state_id_no_functionDef fin hfin scope envVar envMap st
  | while_ cond body =>
    simp only [Flat.convertExpr]
    have hc' : noFunctionDef cond = true := by unfold noFunctionDef at h; simp [Bool.and_eq_true] at h; exact h.1
    have hb' : noFunctionDef body = true := by unfold noFunctionDef at h; simp [Bool.and_eq_true] at h; exact h.2
    have hc := convertExpr_state_id_no_functionDef cond hc' scope envVar envMap st; rw [hc]
    exact convertExpr_state_id_no_functionDef body hb' scope envVar envMap st
  | «return» arg =>
    simp only [Flat.convertExpr]
    cases arg with
    | none => simp [Flat.convertOptExpr]
    | some e =>
      simp only [Flat.convertOptExpr]
      have he : noFunctionDef e = true := by unfold noFunctionDef at h; exact h
      exact convertExpr_state_id_no_functionDef e he scope envVar envMap st
  | labeled _ body =>
    simp only [Flat.convertExpr]
    have hb : noFunctionDef body = true := by unfold noFunctionDef at h; exact h
    exact convertExpr_state_id_no_functionDef body hb scope envVar envMap st
  | yield arg delegate =>
    simp only [Flat.convertExpr]
    cases arg with
    | none => simp [Flat.convertOptExpr]
    | some e =>
      simp only [Flat.convertOptExpr]
      have he : noFunctionDef e = true := by unfold noFunctionDef at h; exact h
      exact convertExpr_state_id_no_functionDef e he scope envVar envMap st
  | await arg =>
    simp only [Flat.convertExpr]
    have ha : noFunctionDef arg = true := by unfold noFunctionDef at h; exact h
    exact convertExpr_state_id_no_functionDef arg ha scope envVar envMap st
  termination_by sizeOf e
  decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_all <;> omega

private theorem convertExprList_state_id_no_functionDef (es : List Core.Expr)
    (h : listNoFunctionDef es = true)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertExprList es scope envVar envMap st).snd = st := by
  cases es with
  | nil => simp [Flat.convertExprList]
  | cons e rest =>
    simp only [Flat.convertExprList]
    have hn := by simp [listNoFunctionDef, Bool.and_eq_true] at h; exact h
    have he := convertExpr_state_id_no_functionDef e hn.1 scope envVar envMap st; rw [he]
    exact convertExprList_state_id_no_functionDef rest hn.2 scope envVar envMap st
  termination_by sizeOf es
  decreasing_by all_goals simp_all <;> omega

private theorem convertPropList_state_id_no_functionDef (ps : List (Core.PropName × Core.Expr))
    (h : propListNoFunctionDef ps = true)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertPropList ps scope envVar envMap st).snd = st := by
  cases ps with
  | nil => simp [Flat.convertPropList]
  | cons p rest =>
    obtain ⟨pn, pe⟩ := p
    simp only [Flat.convertPropList]
    have hn := by simp [propListNoFunctionDef, Bool.and_eq_true] at h; exact h
    have he := convertExpr_state_id_no_functionDef pe hn.1 scope envVar envMap st; rw [he]
    exact convertPropList_state_id_no_functionDef rest hn.2 scope envVar envMap st
  termination_by sizeOf ps
  decreasing_by simp_wf; simp only [Prod.mk.sizeOf_spec]; omega

private theorem convertOptExpr_state_id_no_functionDef (oe : Option Core.Expr)
    (h : (match oe with | some e => noFunctionDef e | none => true) = true)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertOptExpr oe scope envVar envMap st).snd = st := by
  cases oe with
  | none => simp [Flat.convertOptExpr]
  | some e =>
    simp only [Flat.convertOptExpr]
    exact convertExpr_state_id_no_functionDef e (by simp at h; exact h) scope envVar envMap st
  termination_by sizeOf oe
  decreasing_by all_goals simp_all <;> omega
end

/-! ### exprFuncCount: exact count of functionDef nodes processed by convertExpr.
    Both `nextId` and `funcs.size` grow by exactly `exprFuncCount e` when
    converting expression `e`. This precisely characterizes the CCState delta
    and is the foundation for position-based function indexing (Path A). -/

mutual
/-- Count functionDef nodes matching convertExpr's traversal pattern. -/
def exprFuncCount : Core.Expr → Nat
  | .lit _ => 0
  | .var _ => 0
  | .this => 0
  | .«let» _ init body => exprFuncCount init + exprFuncCount body
  | .assign _ value => exprFuncCount value
  | .«if» cond then_ else_ => exprFuncCount cond + exprFuncCount then_ + exprFuncCount else_
  | .seq a b => exprFuncCount a + exprFuncCount b
  | .call callee args => exprFuncCount callee + exprFuncCountList args
  | .newObj callee args => exprFuncCount callee + exprFuncCountList args
  | .getProp obj _ => exprFuncCount obj
  | .setProp obj _ value => exprFuncCount obj + exprFuncCount value
  | .getIndex obj idx => exprFuncCount obj + exprFuncCount idx
  | .setIndex obj idx value => exprFuncCount obj + exprFuncCount idx + exprFuncCount value
  | .deleteProp obj _ => exprFuncCount obj
  | .typeof arg => exprFuncCount arg
  | .unary _ arg => exprFuncCount arg
  | .binary _ lhs rhs => exprFuncCount lhs + exprFuncCount rhs
  | .objectLit props => exprFuncCountProps props
  | .arrayLit elems => exprFuncCountList elems
  | .functionDef _ _ body _ _ => exprFuncCount body + 1
  | .throw arg => exprFuncCount arg
  | .tryCatch body _ catchBody fin =>
    exprFuncCount body + exprFuncCount catchBody +
      match fin with | some e => exprFuncCount e | none => 0
  | .while_ cond body => exprFuncCount cond + exprFuncCount body
  | .forIn _ _ _ => 0
  | .forOf _ _ _ => 0
  | .«break» _ => 0
  | .«continue» _ => 0
  | .«return» arg => match arg with | some e => exprFuncCount e | none => 0
  | .labeled _ body => exprFuncCount body
  | .yield arg _ => match arg with | some e => exprFuncCount e | none => 0
  | .await arg => exprFuncCount arg
def exprFuncCountList : List Core.Expr → Nat
  | [] => 0
  | e :: rest => exprFuncCount e + exprFuncCountList rest
def exprFuncCountProps : List (Core.PropName × Core.Expr) → Nat
  | [] => 0
  | (_, e) :: rest => exprFuncCount e + exprFuncCountProps rest
end

/-! ### State delta theorem: convertExpr grows nextId and funcs.size by exactly exprFuncCount -/

mutual
private theorem convertExpr_state_delta (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertExpr e scope envVar envMap st).snd.nextId = st.nextId + exprFuncCount e ∧
    (Flat.convertExpr e scope envVar envMap st).snd.funcs.size = st.funcs.size + exprFuncCount e := by
  cases e with
  | lit _ => simp [Flat.convertExpr, exprFuncCount]
  | var n => simp only [Flat.convertExpr, exprFuncCount]; cases Flat.lookupEnv envMap n <;> simp
  | this => simp [Flat.convertExpr, exprFuncCount]
  | «break» _ => simp [Flat.convertExpr, exprFuncCount]
  | «continue» _ => simp [Flat.convertExpr, exprFuncCount]
  | forIn _ _ _ => simp [Flat.convertExpr, exprFuncCount]
  | forOf _ _ _ => simp [Flat.convertExpr, exprFuncCount]
  | «let» name init body =>
    simp only [Flat.convertExpr, exprFuncCount]
    have hi := convertExpr_state_delta init scope envVar envMap st
    have hb := convertExpr_state_delta body (name :: scope) envVar envMap
      (Flat.convertExpr init scope envVar envMap st).snd
    exact ⟨by rw [hb.1, hi.1]; omega, by rw [hb.2, hi.2]; omega⟩
  | assign _ value =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta value scope envVar envMap st
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr, exprFuncCount]
    have hc := convertExpr_state_delta cond scope envVar envMap st
    have ht := convertExpr_state_delta then_ scope envVar envMap
      (Flat.convertExpr cond scope envVar envMap st).snd
    have he := convertExpr_state_delta else_ scope envVar envMap
      (Flat.convertExpr then_ scope envVar envMap
        (Flat.convertExpr cond scope envVar envMap st).snd).snd
    exact ⟨by rw [he.1, ht.1, hc.1]; omega, by rw [he.2, ht.2, hc.2]; omega⟩
  | seq a b =>
    simp only [Flat.convertExpr, exprFuncCount]
    have ha := convertExpr_state_delta a scope envVar envMap st
    have hb := convertExpr_state_delta b scope envVar envMap
      (Flat.convertExpr a scope envVar envMap st).snd
    exact ⟨by rw [hb.1, ha.1]; omega, by rw [hb.2, ha.2]; omega⟩
  | call callee args =>
    simp only [Flat.convertExpr, exprFuncCount]
    have hc := convertExpr_state_delta callee scope envVar envMap st
    have ha := convertExprList_state_delta args scope envVar envMap
      (Flat.convertExpr callee scope envVar envMap st).snd
    exact ⟨by rw [ha.1, hc.1]; omega, by rw [ha.2, hc.2]; omega⟩
  | newObj callee args =>
    simp only [Flat.convertExpr, exprFuncCount]
    have hc := convertExpr_state_delta callee scope envVar envMap st
    have ha := convertExprList_state_delta args scope envVar envMap
      (Flat.convertExpr callee scope envVar envMap st).snd
    exact ⟨by rw [ha.1, hc.1]; omega, by rw [ha.2, hc.2]; omega⟩
  | getProp obj _ =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta obj scope envVar envMap st
  | setProp obj _ value =>
    simp only [Flat.convertExpr, exprFuncCount]
    have ho := convertExpr_state_delta obj scope envVar envMap st
    have hv := convertExpr_state_delta value scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st).snd
    exact ⟨by rw [hv.1, ho.1]; omega, by rw [hv.2, ho.2]; omega⟩
  | getIndex obj idx =>
    simp only [Flat.convertExpr, exprFuncCount]
    have ho := convertExpr_state_delta obj scope envVar envMap st
    have hi := convertExpr_state_delta idx scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st).snd
    exact ⟨by rw [hi.1, ho.1]; omega, by rw [hi.2, ho.2]; omega⟩
  | setIndex obj idx value =>
    simp only [Flat.convertExpr, exprFuncCount]
    have ho := convertExpr_state_delta obj scope envVar envMap st
    have hi := convertExpr_state_delta idx scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st).snd
    have hv := convertExpr_state_delta value scope envVar envMap
      (Flat.convertExpr idx scope envVar envMap
        (Flat.convertExpr obj scope envVar envMap st).snd).snd
    exact ⟨by rw [hv.1, hi.1, ho.1]; omega, by rw [hv.2, hi.2, ho.2]; omega⟩
  | deleteProp obj _ =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta obj scope envVar envMap st
  | typeof arg =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta arg scope envVar envMap st
  | unary _ arg =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta arg scope envVar envMap st
  | binary _ lhs rhs =>
    simp only [Flat.convertExpr, exprFuncCount]
    have hl := convertExpr_state_delta lhs scope envVar envMap st
    have hr := convertExpr_state_delta rhs scope envVar envMap
      (Flat.convertExpr lhs scope envVar envMap st).snd
    exact ⟨by rw [hr.1, hl.1]; omega, by rw [hr.2, hl.2]; omega⟩
  | objectLit props =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertPropList_state_delta props scope envVar envMap st
  | arrayLit elems =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExprList_state_delta elems scope envVar envMap st
  | functionDef fname params body _isAsync _isGenerator =>
    unfold Flat.convertExpr
    simp only [Flat.CCState.freshVar, Flat.CCState.addFunc, exprFuncCount]
    have ih := convertExpr_state_delta body params
      (toString "__env" ++ toString "_" ++ toString st.nextId)
      (Flat.indexedMap
        (Flat.dedupStrings
          (match fname with
          | some n => List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))
          | none => List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
      { st with nextId := st.nextId + 1 }
    exact ⟨ih.1.trans ((Nat.add_assoc st.nextId 1 (exprFuncCount body)).trans
              (congrArg (st.nextId + ·) (Nat.add_comm 1 (exprFuncCount body)))),
           by show Array.size (Array.push _ _) = _; simp only [Array.size_push]
              exact (congrArg (· + 1) ih.2).trans (Nat.add_assoc st.funcs.size (exprFuncCount body) 1)⟩
  | throw arg =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta arg scope envVar envMap st
  | tryCatch body catchParam catchBody finally_ =>
    cases finally_ with
    | none =>
      simp only [Flat.convertExpr, Flat.convertOptExpr, exprFuncCount]
      have hb := convertExpr_state_delta body scope envVar envMap st
      have hc := convertExpr_state_delta catchBody (catchParam :: scope) envVar envMap
        (Flat.convertExpr body scope envVar envMap st).snd
      exact ⟨by rw [hc.1, hb.1]; omega, by rw [hc.2, hb.2]; omega⟩
    | some fin =>
      simp only [Flat.convertExpr, Flat.convertOptExpr, exprFuncCount]
      have hb := convertExpr_state_delta body scope envVar envMap st
      have hc := convertExpr_state_delta catchBody (catchParam :: scope) envVar envMap
        (Flat.convertExpr body scope envVar envMap st).snd
      have hf := convertExpr_state_delta fin scope envVar envMap
        (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap
          (Flat.convertExpr body scope envVar envMap st).snd).snd
      exact ⟨by rw [hf.1, hc.1, hb.1]; omega, by rw [hf.2, hc.2, hb.2]; omega⟩
  | while_ cond body =>
    simp only [Flat.convertExpr, exprFuncCount]
    have hc := convertExpr_state_delta cond scope envVar envMap st
    have hb := convertExpr_state_delta body scope envVar envMap
      (Flat.convertExpr cond scope envVar envMap st).snd
    exact ⟨by rw [hb.1, hc.1]; omega, by rw [hb.2, hc.2]; omega⟩
  | «return» arg =>
    simp only [Flat.convertExpr]
    cases arg with
    | none => simp [Flat.convertOptExpr, exprFuncCount]
    | some e =>
      simp only [Flat.convertOptExpr, exprFuncCount]
      exact convertExpr_state_delta e scope envVar envMap st
  | labeled _ body =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta body scope envVar envMap st
  | yield arg delegate =>
    simp only [Flat.convertExpr]
    cases arg with
    | none => simp [Flat.convertOptExpr, exprFuncCount]
    | some e =>
      simp only [Flat.convertOptExpr, exprFuncCount]
      exact convertExpr_state_delta e scope envVar envMap st
  | await arg =>
    simp only [Flat.convertExpr, exprFuncCount]
    exact convertExpr_state_delta arg scope envVar envMap st
  termination_by sizeOf e
  decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_wf <;> omega

private theorem convertExprList_state_delta (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertExprList es scope envVar envMap st).snd.nextId = st.nextId + exprFuncCountList es ∧
    (Flat.convertExprList es scope envVar envMap st).snd.funcs.size = st.funcs.size + exprFuncCountList es := by
  cases es with
  | nil => simp [Flat.convertExprList, exprFuncCountList]
  | cons e rest =>
    simp only [Flat.convertExprList, exprFuncCountList]
    have he := convertExpr_state_delta e scope envVar envMap st
    have hr := convertExprList_state_delta rest scope envVar envMap
      (Flat.convertExpr e scope envVar envMap st).snd
    exact ⟨by rw [hr.1, he.1]; omega, by rw [hr.2, he.2]; omega⟩
  termination_by sizeOf es
  decreasing_by all_goals (try simp_wf) <;> omega

private theorem convertPropList_state_delta (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertPropList ps scope envVar envMap st).snd.nextId = st.nextId + exprFuncCountProps ps ∧
    (Flat.convertPropList ps scope envVar envMap st).snd.funcs.size = st.funcs.size + exprFuncCountProps ps := by
  cases ps with
  | nil => simp [Flat.convertPropList, exprFuncCountProps]
  | cons p rest =>
    obtain ⟨pn, pe⟩ := p
    simp only [Flat.convertPropList, exprFuncCountProps]
    have he := convertExpr_state_delta pe scope envVar envMap st
    have hr := convertPropList_state_delta rest scope envVar envMap
      (Flat.convertExpr pe scope envVar envMap st).snd
    exact ⟨by rw [hr.1, he.1]; omega, by rw [hr.2, he.2]; omega⟩
  termination_by sizeOf ps
  decreasing_by all_goals (try simp_wf) <;> simp_all <;> omega

private theorem convertOptExpr_state_delta (oe : Option Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertOptExpr oe scope envVar envMap st).snd.nextId =
      st.nextId + (match oe with | some e => exprFuncCount e | none => 0) ∧
    (Flat.convertOptExpr oe scope envVar envMap st).snd.funcs.size =
      st.funcs.size + (match oe with | some e => exprFuncCount e | none => 0) := by
  cases oe with
  | none => simp [Flat.convertOptExpr]
  | some e =>
    simp only [Flat.convertOptExpr]
    exact convertExpr_state_delta e scope envVar envMap st
  termination_by sizeOf oe
  decreasing_by all_goals simp_all <;> omega
end

/-- Corollary: nextId and funcs.size always advance by the same amount. -/
theorem convertExpr_nextId_funcs_size_sync (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertExpr e scope envVar envMap st).snd.nextId - st.nextId =
    (Flat.convertExpr e scope envVar envMap st).snd.funcs.size - st.funcs.size := by
  have hd := convertExpr_state_delta e scope envVar envMap st
  omega

/-! ### CCExprEquiv: structural equivalence of Flat expressions modulo function indices.

When `convertExpr` is applied to the same Core expression with two different CCState values
that differ by δ in `funcs.size`, the resulting Flat expressions are structurally identical
except that `makeClosure` function indices in the second expression are shifted by +δ.
`CCExprEquiv δ e1 e2` captures exactly this relationship. At δ = 0, it is structural equality.

This relation is the key ingredient for relaxing `CCStateAgree` (equality) to
`CCStateAgreeWeak` (≤) in the simulation invariant: branching constructs (if/while/tryCatch)
produce different output CCStates for taken vs. untaken branches, but the resulting
expressions are `CCExprEquiv` with an appropriate offset. -/

mutual
/-- Two Flat expressions are CC-equivalent with function index offset δ.
    `CCExprEquiv δ e1 e2` holds when e2 has the same structure as e1 but with all
    `makeClosure` function indices shifted by +δ. -/
private def CCExprEquiv (δ : Nat) : Flat.Expr → Flat.Expr → Prop
  | .lit v1, .lit v2 => v1 = v2
  | .var n1, .var n2 => n1 = n2
  | .this, .this => True
  | .«let» n1 i1 b1, .«let» n2 i2 b2 => n1 = n2 ∧ CCExprEquiv δ i1 i2 ∧ CCExprEquiv δ b1 b2
  | .assign n1 v1, .assign n2 v2 => n1 = n2 ∧ CCExprEquiv δ v1 v2
  | .«if» c1 t1 e1, .«if» c2 t2 e2 => CCExprEquiv δ c1 c2 ∧ CCExprEquiv δ t1 t2 ∧ CCExprEquiv δ e1 e2
  | .seq a1 b1, .seq a2 b2 => CCExprEquiv δ a1 a2 ∧ CCExprEquiv δ b1 b2
  | .call f1 e1 args1, .call f2 e2 args2 =>
      CCExprEquiv δ f1 f2 ∧ CCExprEquiv δ e1 e2 ∧ CCExprListEquiv δ args1 args2
  | .newObj f1 e1 args1, .newObj f2 e2 args2 =>
      CCExprEquiv δ f1 f2 ∧ CCExprEquiv δ e1 e2 ∧ CCExprListEquiv δ args1 args2
  | .getProp o1 p1, .getProp o2 p2 => p1 = p2 ∧ CCExprEquiv δ o1 o2
  | .setProp o1 p1 v1, .setProp o2 p2 v2 => p1 = p2 ∧ CCExprEquiv δ o1 o2 ∧ CCExprEquiv δ v1 v2
  | .getIndex o1 i1, .getIndex o2 i2 => CCExprEquiv δ o1 o2 ∧ CCExprEquiv δ i1 i2
  | .setIndex o1 i1 v1, .setIndex o2 i2 v2 =>
      CCExprEquiv δ o1 o2 ∧ CCExprEquiv δ i1 i2 ∧ CCExprEquiv δ v1 v2
  | .deleteProp o1 p1, .deleteProp o2 p2 => p1 = p2 ∧ CCExprEquiv δ o1 o2
  | .typeof a1, .typeof a2 => CCExprEquiv δ a1 a2
  | .getEnv e1 idx1, .getEnv e2 idx2 => idx1 = idx2 ∧ CCExprEquiv δ e1 e2
  | .makeEnv vs1, .makeEnv vs2 => CCExprListEquiv δ vs1 vs2
  | .makeClosure fi1 e1, .makeClosure fi2 e2 => fi1 + δ = fi2 ∧ CCExprEquiv δ e1 e2
  | .objectLit ps1, .objectLit ps2 => CCPropListEquiv δ ps1 ps2
  | .arrayLit es1, .arrayLit es2 => CCExprListEquiv δ es1 es2
  | .throw a1, .throw a2 => CCExprEquiv δ a1 a2
  | .tryCatch b1 cp1 cb1 f1, .tryCatch b2 cp2 cb2 f2 =>
      cp1 = cp2 ∧ CCExprEquiv δ b1 b2 ∧ CCExprEquiv δ cb1 cb2 ∧ CCOptExprEquiv δ f1 f2
  | .while_ c1 b1, .while_ c2 b2 => CCExprEquiv δ c1 c2 ∧ CCExprEquiv δ b1 b2
  | .«break» l1, .«break» l2 => l1 = l2
  | .«continue» l1, .«continue» l2 => l1 = l2
  | .labeled l1 b1, .labeled l2 b2 => l1 = l2 ∧ CCExprEquiv δ b1 b2
  | .«return» a1, .«return» a2 => CCOptExprEquiv δ a1 a2
  | .yield a1 d1, .yield a2 d2 => d1 = d2 ∧ CCOptExprEquiv δ a1 a2
  | .await a1, .await a2 => CCExprEquiv δ a1 a2
  | .unary op1 a1, .unary op2 a2 => op1 = op2 ∧ CCExprEquiv δ a1 a2
  | .binary op1 l1 r1, .binary op2 l2 r2 => op1 = op2 ∧ CCExprEquiv δ l1 l2 ∧ CCExprEquiv δ r1 r2
  | _, _ => False
private def CCExprListEquiv (δ : Nat) : List Flat.Expr → List Flat.Expr → Prop
  | [], [] => True
  | e1 :: r1, e2 :: r2 => CCExprEquiv δ e1 e2 ∧ CCExprListEquiv δ r1 r2
  | _, _ => False
private def CCPropListEquiv (δ : Nat) : List (Flat.PropName × Flat.Expr) → List (Flat.PropName × Flat.Expr) → Prop
  | [], [] => True
  | (p1, e1) :: r1, (p2, e2) :: r2 => p1 = p2 ∧ CCExprEquiv δ e1 e2 ∧ CCPropListEquiv δ r1 r2
  | _, _ => False
private def CCOptExprEquiv (δ : Nat) : Option Flat.Expr → Option Flat.Expr → Prop
  | none, none => True
  | some e1, some e2 => CCExprEquiv δ e1 e2
  | _, _ => False
end

/-! #### CCExprEquiv reflexivity: at δ = 0, any expression is equivalent to itself. -/

mutual
private theorem CCExprEquiv_refl (e : Flat.Expr) : CCExprEquiv 0 e e := by
  cases e with
  | lit _ => unfold CCExprEquiv; rfl
  | var _ => unfold CCExprEquiv; rfl
  | this => unfold CCExprEquiv; trivial
  | «let» n i b => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl i, CCExprEquiv_refl b⟩
  | assign n v => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl v⟩
  | «if» c t e => unfold CCExprEquiv; exact ⟨CCExprEquiv_refl c, CCExprEquiv_refl t, CCExprEquiv_refl e⟩
  | seq a b => unfold CCExprEquiv; exact ⟨CCExprEquiv_refl a, CCExprEquiv_refl b⟩
  | call f e args => unfold CCExprEquiv; exact ⟨CCExprEquiv_refl f, CCExprEquiv_refl e, CCExprListEquiv_refl args⟩
  | newObj f e args => unfold CCExprEquiv; exact ⟨CCExprEquiv_refl f, CCExprEquiv_refl e, CCExprListEquiv_refl args⟩
  | getProp o p => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl o⟩
  | setProp o p v => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl o, CCExprEquiv_refl v⟩
  | getIndex o i => unfold CCExprEquiv; exact ⟨CCExprEquiv_refl o, CCExprEquiv_refl i⟩
  | setIndex o i v => unfold CCExprEquiv; exact ⟨CCExprEquiv_refl o, CCExprEquiv_refl i, CCExprEquiv_refl v⟩
  | deleteProp o p => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl o⟩
  | typeof a => unfold CCExprEquiv; exact CCExprEquiv_refl a
  | getEnv e idx => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl e⟩
  | makeEnv vs => unfold CCExprEquiv; exact CCExprListEquiv_refl vs
  | makeClosure fi e => unfold CCExprEquiv; exact ⟨Nat.add_zero fi, CCExprEquiv_refl e⟩
  | objectLit ps => unfold CCExprEquiv; exact CCPropListEquiv_refl ps
  | arrayLit es => unfold CCExprEquiv; exact CCExprListEquiv_refl es
  | throw a => unfold CCExprEquiv; exact CCExprEquiv_refl a
  | tryCatch b cp cb f => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl b, CCExprEquiv_refl cb, CCOptExprEquiv_refl f⟩
  | while_ c b => unfold CCExprEquiv; exact ⟨CCExprEquiv_refl c, CCExprEquiv_refl b⟩
  | «break» l => unfold CCExprEquiv; rfl
  | «continue» l => unfold CCExprEquiv; rfl
  | labeled l b => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl b⟩
  | «return» a => unfold CCExprEquiv; exact CCOptExprEquiv_refl a
  | yield a d => unfold CCExprEquiv; exact ⟨rfl, CCOptExprEquiv_refl a⟩
  | await a => unfold CCExprEquiv; exact CCExprEquiv_refl a
  | unary op a => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl a⟩
  | binary op l r => unfold CCExprEquiv; exact ⟨rfl, CCExprEquiv_refl l, CCExprEquiv_refl r⟩
private theorem CCExprListEquiv_refl (es : List Flat.Expr) : CCExprListEquiv 0 es es := by
  cases es with
  | nil => unfold CCExprListEquiv; trivial
  | cons e rest => unfold CCExprListEquiv; exact ⟨CCExprEquiv_refl e, CCExprListEquiv_refl rest⟩
private theorem CCPropListEquiv_refl (ps : List (Flat.PropName × Flat.Expr)) : CCPropListEquiv 0 ps ps := by
  cases ps with
  | nil => unfold CCPropListEquiv; trivial
  | cons p rest => unfold CCPropListEquiv; exact ⟨rfl, CCExprEquiv_refl p.2, CCPropListEquiv_refl rest⟩
private theorem CCOptExprEquiv_refl (oe : Option Flat.Expr) : CCOptExprEquiv 0 oe oe := by
  cases oe with
  | none => unfold CCOptExprEquiv; trivial
  | some e => unfold CCOptExprEquiv; exact CCExprEquiv_refl e
end

/-! #### convertExpr produces identical outer expressions when funcs.size agrees.
    Since the outer expression depends only on `funcs.size` (not `nextId`),
    equal `funcs.size` implies equal expressions AND equal output `funcs.size`.
    This is proved directly by structural induction, following the pattern of
    `convertExpr_state_determined` but only requiring funcs.size agreement.
    Key insight: `freshVar` (which depends on nextId) only affects FuncDef bodies
    (which go into the funcs list), never the outer expression tree. The outer
    expression depends solely on `funcs.size` (through `makeClosure` indices). -/

mutual
private theorem convertExpr_expr_eq_of_funcs_size (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertExpr e scope envVar envMap st1).fst =
    (Flat.convertExpr e scope envVar envMap st2).fst ∧
    (Flat.convertExpr e scope envVar envMap st1).snd.funcs.size =
    (Flat.convertExpr e scope envVar envMap st2).snd.funcs.size := by
  cases e with
  | lit v => simp [Flat.convertExpr, hsz]
  | var n =>
    simp only [Flat.convertExpr]
    cases Flat.lookupEnv envMap n <;> simp [hsz]
  | this => simp [Flat.convertExpr, hsz]
  | «break» l => simp [Flat.convertExpr, hsz]
  | «continue» l => simp [Flat.convertExpr, hsz]
  | forIn _ _ _ => simp [Flat.convertExpr, hsz]
  | forOf _ _ _ => simp [Flat.convertExpr, hsz]
  | «let» name init body =>
    simp only [Flat.convertExpr]
    have hi := convertExpr_expr_eq_of_funcs_size init scope envVar envMap st1 st2 hsz
    have hb := convertExpr_expr_eq_of_funcs_size body (name :: scope) envVar envMap _ _ hi.2
    exact ⟨by rw [hi.1, hb.1], hb.2⟩
  | assign name value =>
    simp only [Flat.convertExpr]
    have hv := convertExpr_expr_eq_of_funcs_size value scope envVar envMap st1 st2 hsz
    exact ⟨by rw [hv.1], hv.2⟩
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_expr_eq_of_funcs_size cond scope envVar envMap st1 st2 hsz
    have ht := convertExpr_expr_eq_of_funcs_size then_ scope envVar envMap _ _ hc.2
    have he := convertExpr_expr_eq_of_funcs_size else_ scope envVar envMap _ _ ht.2
    exact ⟨by rw [hc.1, ht.1, he.1], he.2⟩
  | seq a b =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_expr_eq_of_funcs_size a scope envVar envMap st1 st2 hsz
    have hb := convertExpr_expr_eq_of_funcs_size b scope envVar envMap _ _ ha.2
    exact ⟨by rw [ha.1, hb.1], hb.2⟩
  | call callee args =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_expr_eq_of_funcs_size callee scope envVar envMap st1 st2 hsz
    have ha := convertExprList_expr_eq_of_funcs_size args scope envVar envMap _ _ hc.2
    exact ⟨by rw [hc.1, ha.1], ha.2⟩
  | newObj callee args =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_expr_eq_of_funcs_size callee scope envVar envMap st1 st2 hsz
    have ha := convertExprList_expr_eq_of_funcs_size args scope envVar envMap _ _ hc.2
    exact ⟨by rw [hc.1, ha.1], ha.2⟩
  | getProp obj prop =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_expr_eq_of_funcs_size obj scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ho.1], ho.2⟩
  | setProp obj prop value =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_expr_eq_of_funcs_size obj scope envVar envMap st1 st2 hsz
    have hv := convertExpr_expr_eq_of_funcs_size value scope envVar envMap _ _ ho.2
    exact ⟨by rw [ho.1, hv.1], hv.2⟩
  | getIndex obj idx =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_expr_eq_of_funcs_size obj scope envVar envMap st1 st2 hsz
    have hi := convertExpr_expr_eq_of_funcs_size idx scope envVar envMap _ _ ho.2
    exact ⟨by rw [ho.1, hi.1], hi.2⟩
  | setIndex obj idx value =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_expr_eq_of_funcs_size obj scope envVar envMap st1 st2 hsz
    have hi := convertExpr_expr_eq_of_funcs_size idx scope envVar envMap _ _ ho.2
    have hv := convertExpr_expr_eq_of_funcs_size value scope envVar envMap _ _ hi.2
    exact ⟨by rw [ho.1, hi.1, hv.1], hv.2⟩
  | deleteProp obj prop =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_expr_eq_of_funcs_size obj scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ho.1], ho.2⟩
  | typeof arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_expr_eq_of_funcs_size arg scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | unary op arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_expr_eq_of_funcs_size arg scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | binary op lhs rhs =>
    simp only [Flat.convertExpr]
    have hl := convertExpr_expr_eq_of_funcs_size lhs scope envVar envMap st1 st2 hsz
    have hr := convertExpr_expr_eq_of_funcs_size rhs scope envVar envMap _ _ hl.2
    exact ⟨by rw [hl.1, hr.1], hr.2⟩
  | objectLit props =>
    simp only [Flat.convertExpr]
    have hp := convertPropList_expr_eq_of_funcs_size props scope envVar envMap st1 st2 hsz
    exact ⟨by rw [hp.1], hp.2⟩
  | arrayLit elems =>
    simp only [Flat.convertExpr]
    have he := convertExprList_expr_eq_of_funcs_size elems scope envVar envMap st1 st2 hsz
    exact ⟨by rw [he.1], he.2⟩
  | functionDef fname params body _isAsync _isGenerator =>
    -- The outer expression is .makeClosure funcIdx envExpr.
    -- funcIdx = output.funcs.size after body conversion, which depends only on input funcs.size.
    -- envExpr depends only on parent scope/envMap, not on nextId.
    -- The body is converted with possibly different envVar (from freshVar depending on nextId),
    -- but this only affects the FuncDef body, not the outer expression.
    unfold Flat.convertExpr
    simp only [Flat.CCState.freshVar, Flat.CCState.addFunc]
    -- Body conversion may use different envVar names (from different nextId), but output funcs.size
    -- is determined by input funcs.size + exprFuncCount(body).
    have hd1 := convertExpr_state_delta body params
      (toString "__env" ++ toString "_" ++ toString st1.nextId)
      (Flat.indexedMap (Flat.dedupStrings
        (match fname with
        | some n => List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))
        | none => List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
      { funcs := st1.funcs, nextId := st1.nextId + 1 }
    have hd2 := convertExpr_state_delta body params
      (toString "__env" ++ toString "_" ++ toString st2.nextId)
      (Flat.indexedMap (Flat.dedupStrings
        (match fname with
        | some n => List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))
        | none => List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
      { funcs := st2.funcs, nextId := st2.nextId + 1 }
    have hsz_out : (Flat.convertExpr body params
        (toString "__env" ++ toString "_" ++ toString st1.nextId)
        (Flat.indexedMap (Flat.dedupStrings
          (match fname with
          | some n => List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))
          | none => List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
        { funcs := st1.funcs, nextId := st1.nextId + 1 }).snd.funcs.size =
        (Flat.convertExpr body params
        (toString "__env" ++ toString "_" ++ toString st2.nextId)
        (Flat.indexedMap (Flat.dedupStrings
          (match fname with
          | some n => List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))
          | none => List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
        { funcs := st2.funcs, nextId := st2.nextId + 1 }).snd.funcs.size := by
      rw [hd1.2, hd2.2]; simp [hsz]
    refine ⟨?_, ?_⟩
    · -- .fst: .makeClosure funcIdx envExpr — funcIdx depends only on output funcs.size
      show Flat.Expr.makeClosure _ _ = Flat.Expr.makeClosure _ _
      exact congrArg (Flat.Expr.makeClosure · _) hsz_out
    · -- funcs.size: addFunc increments by 1
      show Array.size _ = Array.size _
      simp only [Array.size_push]
      exact congrArg (· + 1) hsz_out
  | throw arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_expr_eq_of_funcs_size arg scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | tryCatch body catchParam catchBody finally_ =>
    simp only [Flat.convertExpr]
    have hb := convertExpr_expr_eq_of_funcs_size body scope envVar envMap st1 st2 hsz
    have hc := convertExpr_expr_eq_of_funcs_size catchBody (catchParam :: scope) envVar envMap _ _ hb.2
    have hf := convertOptExpr_expr_eq_of_funcs_size finally_ scope envVar envMap _ _ hc.2
    exact ⟨by rw [hb.1, hc.1, hf.1], hf.2⟩
  | while_ cond body =>
    simp only [Flat.convertExpr]
    have hc := convertExpr_expr_eq_of_funcs_size cond scope envVar envMap st1 st2 hsz
    have hb := convertExpr_expr_eq_of_funcs_size body scope envVar envMap _ _ hc.2
    exact ⟨by rw [hc.1, hb.1], hb.2⟩
  | «return» arg =>
    simp only [Flat.convertExpr]
    have ha := convertOptExpr_expr_eq_of_funcs_size arg scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | labeled label body =>
    simp only [Flat.convertExpr]
    have hb := convertExpr_expr_eq_of_funcs_size body scope envVar envMap st1 st2 hsz
    exact ⟨by rw [hb.1], hb.2⟩
  | yield arg delegate =>
    simp only [Flat.convertExpr]
    have ha := convertOptExpr_expr_eq_of_funcs_size arg scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ha.1], ha.2⟩
  | await arg =>
    simp only [Flat.convertExpr]
    have ha := convertExpr_expr_eq_of_funcs_size arg scope envVar envMap st1 st2 hsz
    exact ⟨by rw [ha.1], ha.2⟩
  termination_by sizeOf e
  decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_wf <;> omega

private theorem convertExprList_expr_eq_of_funcs_size (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertExprList es scope envVar envMap st1).fst =
    (Flat.convertExprList es scope envVar envMap st2).fst ∧
    (Flat.convertExprList es scope envVar envMap st1).snd.funcs.size =
    (Flat.convertExprList es scope envVar envMap st2).snd.funcs.size := by
  cases es with
  | nil => simp [Flat.convertExprList, hsz]
  | cons e rest =>
    simp only [Flat.convertExprList]
    have he := convertExpr_expr_eq_of_funcs_size e scope envVar envMap st1 st2 hsz
    have hr := convertExprList_expr_eq_of_funcs_size rest scope envVar envMap _ _ he.2
    exact ⟨by rw [he.1, hr.1], hr.2⟩

private theorem convertPropList_expr_eq_of_funcs_size (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertPropList ps scope envVar envMap st1).fst =
    (Flat.convertPropList ps scope envVar envMap st2).fst ∧
    (Flat.convertPropList ps scope envVar envMap st1).snd.funcs.size =
    (Flat.convertPropList ps scope envVar envMap st2).snd.funcs.size := by
  cases ps with
  | nil => exact ⟨rfl, hsz⟩
  | cons p rest =>
    simp only [Flat.convertPropList]
    have he := convertExpr_expr_eq_of_funcs_size p.2 scope envVar envMap st1 st2 hsz
    have hr := convertPropList_expr_eq_of_funcs_size rest scope envVar envMap _ _ he.2
    exact ⟨by rw [he.1, hr.1], hr.2⟩

private theorem convertOptExpr_expr_eq_of_funcs_size (oe : Option Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (hsz : st1.funcs.size = st2.funcs.size) :
    (Flat.convertOptExpr oe scope envVar envMap st1).fst =
    (Flat.convertOptExpr oe scope envVar envMap st2).fst ∧
    (Flat.convertOptExpr oe scope envVar envMap st1).snd.funcs.size =
    (Flat.convertOptExpr oe scope envVar envMap st2).snd.funcs.size := by
  cases oe with
  | none => exact ⟨rfl, hsz⟩
  | some e =>
    simp only [Flat.convertOptExpr]
    have h := convertExpr_expr_eq_of_funcs_size e scope envVar envMap st1 st2 hsz
    exact ⟨congrArg some h.1, h.2⟩
end

/-! #### Equality implies CCExprEquiv: if two expressions are equal, they are CCExprEquiv for any δ.
    (Only meaningful for non-makeClosure expressions; makeClosure with different fi requires fi1+δ=fi2.) -/

private theorem eq_implies_CCExprEquiv_zero {e1 e2 : Flat.Expr} (h : e1 = e2) :
    CCExprEquiv 0 e1 e2 := by subst h; exact CCExprEquiv_refl e1

/-! #### convertExpr_CCExprEquiv: converting the same Core expression with two CCStates that
    agree (CCStateAgree) produces identical expressions (hence CCExprEquiv at any δ).
    This follows directly from convertExpr_state_determined. -/

private theorem convertExpr_CCExprEquiv_of_agree (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState)
    (hid : st1.nextId = st2.nextId) (hsz : st1.funcs.size = st2.funcs.size) :
    CCExprEquiv 0
      (Flat.convertExpr e scope envVar envMap st1).fst
      (Flat.convertExpr e scope envVar envMap st2).fst := by
  have hdet := convertExpr_state_determined e scope envVar envMap st1 st2 hid hsz
  rw [hdet.1]; exact CCExprEquiv_refl _

/-! #### CCExprEquiv δ when funcs.size differs by δ (nextId may differ freely).

When two CCStates have `funcs.size` differing by δ, `convertExpr` produces expressions
that are `CCExprEquiv δ`: structurally identical except `makeClosure` function indices
are shifted by +δ. No constraint on `nextId` is needed: `freshVar`-generated variable
names (which depend on `nextId`) only appear inside FuncDef bodies added to the function
list, never in the outer expression tree. The outer expression depends solely on
`funcs.size` (through `makeClosure` indices) and the provided scope/envVar/envMap. -/

/-- Helper: CCExprEquiv δ e e holds for any δ when e contains no makeClosure nodes. -/
private theorem CCExprEquiv_var_self (n : String) (δ : Nat) :
    CCExprEquiv δ (.var n) (.var n) := by simp [CCExprEquiv]

private theorem CCExprEquiv_getEnv_var_self (envVar : String) (idx : Nat) (δ : Nat) :
    CCExprEquiv δ (.getEnv (.var envVar) idx) (.getEnv (.var envVar) idx) := by
  simp [CCExprEquiv]

/-- Helper: CCExprListEquiv δ holds reflexively for lists of .var/.getEnv expressions
    (the form of captured-variable expressions in closure conversion). -/
private theorem CCExprListEquiv_envExprs_refl (captured : List String)
    (envMap : Flat.EnvMapping) (envVar : String) (δ : Nat) :
    CCExprListEquiv δ
      (captured.map (fun v =>
        match Flat.lookupEnv envMap v with
        | some idx => .getEnv (.var envVar) idx
        | none => .var v))
      (captured.map (fun v =>
        match Flat.lookupEnv envMap v with
        | some idx => .getEnv (.var envVar) idx
        | none => .var v)) := by
  induction captured with
  | nil => simp only [List.map]; unfold CCExprListEquiv; trivial
  | cons v rest ih =>
    simp only [List.map]; unfold CCExprListEquiv
    refine ⟨?_, ih⟩
    split
    · -- some idx case: .getEnv (.var envVar) idx
      exact CCExprEquiv_getEnv_var_self envVar _ δ
    · -- none case: .var v
      exact CCExprEquiv_var_self _ δ

mutual
/-- Converting the same Core expression with two CCStates that differ by δ on `funcs.size`
    produces `CCExprEquiv δ` Flat expressions. No constraint on `nextId` is needed because
    the outer expression depends only on `funcs.size`: `freshVar`-generated names (from nextId)
    only appear inside FuncDefs, not in the outer expression tree. -/
private theorem convertExpr_CCExprEquiv_shifted (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (δ : Nat)
    (hsz : st2.funcs.size = st1.funcs.size + δ) :
    CCExprEquiv δ
      (Flat.convertExpr e scope envVar envMap st1).fst
      (Flat.convertExpr e scope envVar envMap st2).fst := by
  cases e with
  | lit v => simp [Flat.convertExpr, CCExprEquiv]
  | var n =>
    simp only [Flat.convertExpr]
    cases Flat.lookupEnv envMap n <;> simp [CCExprEquiv]
  | this => simp [Flat.convertExpr, CCExprEquiv]
  | «break» l => simp [Flat.convertExpr, CCExprEquiv]
  | «continue» l => simp [Flat.convertExpr, CCExprEquiv]
  | forIn _ _ _ => simp [Flat.convertExpr, CCExprEquiv]
  | forOf _ _ _ => simp [Flat.convertExpr, CCExprEquiv]
  | «let» name init body =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta init scope envVar envMap st1
    have hd2 := convertExpr_state_delta init scope envVar envMap st2
    have hi := convertExpr_CCExprEquiv_shifted init scope envVar envMap st1 st2 δ hsz
    have hb := convertExpr_CCExprEquiv_shifted body (name :: scope) envVar envMap
      (Flat.convertExpr init scope envVar envMap st1).snd
      (Flat.convertExpr init scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨trivial, hi, hb⟩
  | assign name value =>
    simp only [Flat.convertExpr]
    have hv := convertExpr_CCExprEquiv_shifted value scope envVar envMap st1 st2 δ hsz
    simp only [CCExprEquiv]; exact ⟨trivial, hv⟩
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr]
    have hd1c := convertExpr_state_delta cond scope envVar envMap st1
    have hd2c := convertExpr_state_delta cond scope envVar envMap st2
    have hc := convertExpr_CCExprEquiv_shifted cond scope envVar envMap st1 st2 δ hsz
    have hsz_c : (Flat.convertExpr cond scope envVar envMap st2).snd.funcs.size =
        (Flat.convertExpr cond scope envVar envMap st1).snd.funcs.size + δ := by rw [hd2c.2, hd1c.2]; omega
    have hd1t := convertExpr_state_delta then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st1).snd
    have hd2t := convertExpr_state_delta then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st2).snd
    have ht := convertExpr_CCExprEquiv_shifted then_ scope envVar envMap
      (Flat.convertExpr cond scope envVar envMap st1).snd
      (Flat.convertExpr cond scope envVar envMap st2).snd δ hsz_c
    have hsz_t : (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st2).snd).snd.funcs.size =
        (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st1).snd).snd.funcs.size + δ := by
      rw [hd2t.2, hd1t.2]; omega
    have he := convertExpr_CCExprEquiv_shifted else_ scope envVar envMap
      (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st1).snd).snd
      (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st2).snd).snd δ hsz_t
    simp only [CCExprEquiv]; exact ⟨hc, ht, he⟩
  | seq a b =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta a scope envVar envMap st1
    have hd2 := convertExpr_state_delta a scope envVar envMap st2
    have ha := convertExpr_CCExprEquiv_shifted a scope envVar envMap st1 st2 δ hsz
    have hb := convertExpr_CCExprEquiv_shifted b scope envVar envMap
      (Flat.convertExpr a scope envVar envMap st1).snd
      (Flat.convertExpr a scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨ha, hb⟩
  | call callee args =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta callee scope envVar envMap st1
    have hd2 := convertExpr_state_delta callee scope envVar envMap st2
    have hc := convertExpr_CCExprEquiv_shifted callee scope envVar envMap st1 st2 δ hsz
    have ha := convertExprList_CCExprEquiv_shifted args scope envVar envMap
      (Flat.convertExpr callee scope envVar envMap st1).snd
      (Flat.convertExpr callee scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨hc, trivial, ha⟩
  | newObj callee args =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta callee scope envVar envMap st1
    have hd2 := convertExpr_state_delta callee scope envVar envMap st2
    have hc := convertExpr_CCExprEquiv_shifted callee scope envVar envMap st1 st2 δ hsz
    have ha := convertExprList_CCExprEquiv_shifted args scope envVar envMap
      (Flat.convertExpr callee scope envVar envMap st1).snd
      (Flat.convertExpr callee scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨hc, trivial, ha⟩
  | getProp obj prop =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_CCExprEquiv_shifted obj scope envVar envMap st1 st2 δ hsz
    simp only [CCExprEquiv]; exact ⟨trivial, ho⟩
  | setProp obj prop value =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta obj scope envVar envMap st1
    have hd2 := convertExpr_state_delta obj scope envVar envMap st2
    have ho := convertExpr_CCExprEquiv_shifted obj scope envVar envMap st1 st2 δ hsz
    have hv := convertExpr_CCExprEquiv_shifted value scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st1).snd
      (Flat.convertExpr obj scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨trivial, ho, hv⟩
  | getIndex obj idx =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta obj scope envVar envMap st1
    have hd2 := convertExpr_state_delta obj scope envVar envMap st2
    have ho := convertExpr_CCExprEquiv_shifted obj scope envVar envMap st1 st2 δ hsz
    have hi := convertExpr_CCExprEquiv_shifted idx scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st1).snd
      (Flat.convertExpr obj scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨ho, hi⟩
  | setIndex obj idx value =>
    simp only [Flat.convertExpr]
    have hd1o := convertExpr_state_delta obj scope envVar envMap st1
    have hd2o := convertExpr_state_delta obj scope envVar envMap st2
    have ho := convertExpr_CCExprEquiv_shifted obj scope envVar envMap st1 st2 δ hsz
    have hsz_o : (Flat.convertExpr obj scope envVar envMap st2).snd.funcs.size =
        (Flat.convertExpr obj scope envVar envMap st1).snd.funcs.size + δ := by rw [hd2o.2, hd1o.2]; omega
    have hd1i := convertExpr_state_delta idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st1).snd
    have hd2i := convertExpr_state_delta idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st2).snd
    have hi := convertExpr_CCExprEquiv_shifted idx scope envVar envMap
      (Flat.convertExpr obj scope envVar envMap st1).snd
      (Flat.convertExpr obj scope envVar envMap st2).snd δ hsz_o
    have hv := convertExpr_CCExprEquiv_shifted value scope envVar envMap
      (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st1).snd).snd
      (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st2).snd).snd δ
      (by rw [hd2i.2, hd1i.2]; omega)
    simp only [CCExprEquiv]; exact ⟨ho, hi, hv⟩
  | deleteProp obj prop =>
    simp only [Flat.convertExpr]
    have ho := convertExpr_CCExprEquiv_shifted obj scope envVar envMap st1 st2 δ hsz
    simp only [CCExprEquiv]; exact ⟨trivial, ho⟩
  | typeof arg =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact convertExpr_CCExprEquiv_shifted arg scope envVar envMap st1 st2 δ hsz
  | unary op arg =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact ⟨trivial, convertExpr_CCExprEquiv_shifted arg scope envVar envMap st1 st2 δ hsz⟩
  | binary op lhs rhs =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta lhs scope envVar envMap st1
    have hd2 := convertExpr_state_delta lhs scope envVar envMap st2
    have hl := convertExpr_CCExprEquiv_shifted lhs scope envVar envMap st1 st2 δ hsz
    have hr := convertExpr_CCExprEquiv_shifted rhs scope envVar envMap
      (Flat.convertExpr lhs scope envVar envMap st1).snd
      (Flat.convertExpr lhs scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨trivial, hl, hr⟩
  | objectLit props =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact convertPropList_CCExprEquiv_shifted props scope envVar envMap st1 st2 δ hsz
  | arrayLit elems =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact convertExprList_CCExprEquiv_shifted elems scope envVar envMap st1 st2 δ hsz
  | functionDef fname params body _isAsync _isGenerator =>
    -- Case split on fname to avoid Lean 4 match contamination with local hypotheses
    -- NOTE: hid (nextId equality) is NOT needed here. The outer expression .makeClosure funcIdx envExpr
    -- depends only on funcs.size (through funcIdx) and the outer envMap/envVar (through envExpr).
    -- The inner envVar name (from freshVar, which uses nextId) only appears inside the FuncDef,
    -- not in the outer expression. So we use convertExpr_state_delta independently for each state.
    cases fname with
    | some n =>
      unfold Flat.convertExpr
      simp only [Flat.CCState.freshVar, Flat.CCState.addFunc, CCExprEquiv]
      constructor
      · have hd1 := convertExpr_state_delta body params
          (toString "__env" ++ toString "_" ++ toString st1.nextId)
          (Flat.indexedMap (Flat.dedupStrings (List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))) []) 0)
          { funcs := st1.funcs, nextId := st1.nextId + 1 }
        have hd2 := convertExpr_state_delta body params
          (toString "__env" ++ toString "_" ++ toString st2.nextId)
          (Flat.indexedMap (Flat.dedupStrings (List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))) []) 0)
          { funcs := st2.funcs, nextId := st2.nextId + 1 }
        have h1 := hd1.2; have h2 := hd2.2; clear hd1 hd2
        rw [h1, h2]; clear h1 h2; simp [hsz, Nat.add_comm, Nat.add_assoc]
      · exact CCExprListEquiv_envExprs_refl
          (Flat.dedupStrings (List.filter (fun x => x != n) (List.filter (fun v => !List.elem v params) (Flat.freeVars body))) [])
          envMap envVar δ
    | none =>
      unfold Flat.convertExpr
      simp only [Flat.CCState.freshVar, Flat.CCState.addFunc, CCExprEquiv]
      constructor
      · have hd1 := convertExpr_state_delta body params
          (toString "__env" ++ toString "_" ++ toString st1.nextId)
          (Flat.indexedMap (Flat.dedupStrings (List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
          { funcs := st1.funcs, nextId := st1.nextId + 1 }
        have hd2 := convertExpr_state_delta body params
          (toString "__env" ++ toString "_" ++ toString st2.nextId)
          (Flat.indexedMap (Flat.dedupStrings (List.filter (fun v => !List.elem v params) (Flat.freeVars body)) []) 0)
          { funcs := st2.funcs, nextId := st2.nextId + 1 }
        have h1 := hd1.2; have h2 := hd2.2; clear hd1 hd2
        rw [h1, h2]; clear h1 h2; simp [hsz, Nat.add_comm, Nat.add_assoc]
      · exact CCExprListEquiv_envExprs_refl
          (Flat.dedupStrings (List.filter (fun v => !List.elem v params) (Flat.freeVars body)) [])
          envMap envVar δ
  | throw arg =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact convertExpr_CCExprEquiv_shifted arg scope envVar envMap st1 st2 δ hsz
  | tryCatch body catchParam catchBody finally_ =>
    simp only [Flat.convertExpr]
    have hd1b := convertExpr_state_delta body scope envVar envMap st1
    have hd2b := convertExpr_state_delta body scope envVar envMap st2
    have hb := convertExpr_CCExprEquiv_shifted body scope envVar envMap st1 st2 δ hsz
    have hsz_b : (Flat.convertExpr body scope envVar envMap st2).snd.funcs.size =
        (Flat.convertExpr body scope envVar envMap st1).snd.funcs.size + δ := by rw [hd2b.2, hd1b.2]; omega
    have hd1c := convertExpr_state_delta catchBody (catchParam :: scope) envVar envMap
      (Flat.convertExpr body scope envVar envMap st1).snd
    have hd2c := convertExpr_state_delta catchBody (catchParam :: scope) envVar envMap
      (Flat.convertExpr body scope envVar envMap st2).snd
    have hc := convertExpr_CCExprEquiv_shifted catchBody (catchParam :: scope) envVar envMap
      (Flat.convertExpr body scope envVar envMap st1).snd
      (Flat.convertExpr body scope envVar envMap st2).snd δ hsz_b
    have hf := convertOptExpr_CCExprEquiv_shifted finally_ scope envVar envMap
      (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap (Flat.convertExpr body scope envVar envMap st1).snd).snd
      (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap (Flat.convertExpr body scope envVar envMap st2).snd).snd δ
      (by rw [hd2c.2, hd1c.2]; omega)
    simp only [CCExprEquiv]; exact ⟨trivial, hb, hc, hf⟩
  | while_ cond body =>
    simp only [Flat.convertExpr]
    have hd1 := convertExpr_state_delta cond scope envVar envMap st1
    have hd2 := convertExpr_state_delta cond scope envVar envMap st2
    have hc := convertExpr_CCExprEquiv_shifted cond scope envVar envMap st1 st2 δ hsz
    have hb := convertExpr_CCExprEquiv_shifted body scope envVar envMap
      (Flat.convertExpr cond scope envVar envMap st1).snd
      (Flat.convertExpr cond scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprEquiv]; exact ⟨hc, hb⟩
  | «return» arg =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact convertOptExpr_CCExprEquiv_shifted arg scope envVar envMap st1 st2 δ hsz
  | labeled label body =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact ⟨trivial, convertExpr_CCExprEquiv_shifted body scope envVar envMap st1 st2 δ hsz⟩
  | yield arg delegate =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact ⟨trivial, convertOptExpr_CCExprEquiv_shifted arg scope envVar envMap st1 st2 δ hsz⟩
  | await arg =>
    simp only [Flat.convertExpr, CCExprEquiv]
    exact convertExpr_CCExprEquiv_shifted arg scope envVar envMap st1 st2 δ hsz
  termination_by sizeOf e
  decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_wf <;> omega

private theorem convertExprList_CCExprEquiv_shifted (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (δ : Nat)
    (hsz : st2.funcs.size = st1.funcs.size + δ) :
    CCExprListEquiv δ
      (Flat.convertExprList es scope envVar envMap st1).fst
      (Flat.convertExprList es scope envVar envMap st2).fst := by
  cases es with
  | nil => simp [Flat.convertExprList, CCExprListEquiv]
  | cons e rest =>
    simp only [Flat.convertExprList]
    have hd1 := convertExpr_state_delta e scope envVar envMap st1
    have hd2 := convertExpr_state_delta e scope envVar envMap st2
    have he := convertExpr_CCExprEquiv_shifted e scope envVar envMap st1 st2 δ hsz
    have hr := convertExprList_CCExprEquiv_shifted rest scope envVar envMap
      (Flat.convertExpr e scope envVar envMap st1).snd
      (Flat.convertExpr e scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCExprListEquiv]; exact ⟨he, hr⟩
  termination_by sizeOf es
  decreasing_by all_goals simp_wf <;> omega

private theorem convertPropList_CCExprEquiv_shifted (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (δ : Nat)
    (hsz : st2.funcs.size = st1.funcs.size + δ) :
    CCPropListEquiv δ
      (Flat.convertPropList ps scope envVar envMap st1).fst
      (Flat.convertPropList ps scope envVar envMap st2).fst := by
  cases ps with
  | nil => simp [Flat.convertPropList, CCPropListEquiv]
  | cons p rest =>
    obtain ⟨pn, pe⟩ := p
    simp only [Flat.convertPropList]
    have hd1 := convertExpr_state_delta pe scope envVar envMap st1
    have hd2 := convertExpr_state_delta pe scope envVar envMap st2
    have he := convertExpr_CCExprEquiv_shifted pe scope envVar envMap st1 st2 δ hsz
    have hr := convertPropList_CCExprEquiv_shifted rest scope envVar envMap
      (Flat.convertExpr pe scope envVar envMap st1).snd
      (Flat.convertExpr pe scope envVar envMap st2).snd δ
      (by rw [hd2.2, hd1.2]; omega)
    simp only [CCPropListEquiv]; exact ⟨trivial, he, hr⟩
  termination_by sizeOf ps
  decreasing_by all_goals simp_wf <;> simp_all <;> omega

private theorem convertOptExpr_CCExprEquiv_shifted (oe : Option Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) (δ : Nat)
    (hsz : st2.funcs.size = st1.funcs.size + δ) :
    CCOptExprEquiv δ
      (Flat.convertOptExpr oe scope envVar envMap st1).fst
      (Flat.convertOptExpr oe scope envVar envMap st2).fst := by
  cases oe with
  | none => simp [Flat.convertOptExpr, CCOptExprEquiv]
  | some e =>
    simp only [Flat.convertOptExpr, CCOptExprEquiv]
    exact convertExpr_CCExprEquiv_shifted e scope envVar envMap st1 st2 δ hsz
  termination_by sizeOf oe
  decreasing_by all_goals simp_all <;> omega
end

/-! ### ValidConversionR: structural valid conversion relation.

`ValidConversionR scope envVar envMap fe ce` holds when the Flat expression `fe` is a valid
closure-conversion of the Core expression `ce`. Unlike the exact conversion equation
`fe = (convertExpr ce scope envVar envMap st).fst` (which requires a single state for the
whole expression), ValidConversionR decomposes structurally: each sub-expression may have
been converted at an independent CCState. This is necessary because branching constructs
(if/while/tryCatch) cause the CCState to diverge between taken and un-taken paths.

Key properties:
- `convertExpr` output satisfies `ValidConversionR` (bridging lemma)
- Sibling sub-expressions are preserved unchanged through stepping
- The relation composes without funcs.size constraints between siblings -/
mutual
private def ValidConversionR (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    : Flat.Expr → Core.Expr → Prop
  -- Compound cases: recursive structural decomposition
  | .seq fa fb, .seq a b =>
      ValidConversionR scope envVar envMap fa a ∧
      ValidConversionR scope envVar envMap fb b
  | .«if» fc ft fe, .«if» c t e =>
      ValidConversionR scope envVar envMap fc c ∧
      ValidConversionR scope envVar envMap ft t ∧
      ValidConversionR scope envVar envMap fe e
  | .«let» n1 fi fb, .«let» n2 i b =>
      n1 = n2 ∧ ValidConversionR scope envVar envMap fi i ∧
      ValidConversionR (n2 :: scope) envVar envMap fb b
  | .assign n1 fv, .assign n2 v =>
      n1 = n2 ∧ ValidConversionR scope envVar envMap fv v
  | .while_ fc fb, .while_ c b =>
      ValidConversionR scope envVar envMap fc c ∧
      ValidConversionR scope envVar envMap fb b
  | .tryCatch fb cp1 fcb (some ffin), .tryCatch b cp2 cb (some fin) =>
      cp1 = cp2 ∧ ValidConversionR scope envVar envMap fb b ∧
      ValidConversionR (cp2 :: scope) envVar envMap fcb cb ∧
      ValidConversionR scope envVar envMap ffin fin
  | .tryCatch fb cp1 fcb none, .tryCatch b cp2 cb none =>
      cp1 = cp2 ∧ ValidConversionR scope envVar envMap fb b ∧
      ValidConversionR (cp2 :: scope) envVar envMap fcb cb
  | .binary op1 fl fr, .binary op2 l r =>
      op1 = op2 ∧ ValidConversionR scope envVar envMap fl l ∧
      ValidConversionR scope envVar envMap fr r
  | .unary op1 fa, .unary op2 a =>
      op1 = op2 ∧ ValidConversionR scope envVar envMap fa a
  | .getProp fo p1, .getProp o p2 =>
      p1 = p2 ∧ ValidConversionR scope envVar envMap fo o
  | .setProp fo p1 fv, .setProp o p2 v =>
      p1 = p2 ∧ ValidConversionR scope envVar envMap fo o ∧
      ValidConversionR scope envVar envMap fv v
  | .getIndex fo fi, .getIndex o i =>
      ValidConversionR scope envVar envMap fo o ∧
      ValidConversionR scope envVar envMap fi i
  | .setIndex fo fi fv, .setIndex o i v =>
      ValidConversionR scope envVar envMap fo o ∧
      ValidConversionR scope envVar envMap fi i ∧
      ValidConversionR scope envVar envMap fv v
  | .deleteProp fo p1, .deleteProp o p2 =>
      p1 = p2 ∧ ValidConversionR scope envVar envMap fo o
  | .typeof fa, .typeof a =>
      ValidConversionR scope envVar envMap fa a
  | .throw fa, .throw a =>
      ValidConversionR scope envVar envMap fa a
  | .labeled l1 fb, .labeled l2 b =>
      l1 = l2 ∧ ValidConversionR scope envVar envMap fb b
  | .«return» (some fa), .«return» (some a) =>
      ValidConversionR scope envVar envMap fa a
  | .«return» none, .«return» none => True
  | .await fa, .await a =>
      ValidConversionR scope envVar envMap fa a
  -- Base case: exact conversion at some CCState (handles lit, var, this,
  -- break, continue, call, newObj, objectLit, arrayLit, functionDef→makeClosure,
  -- yield, forIn, forOf, and all cross-constructor pairs)
  | fe, ce => ∃ (st : Flat.CCState), fe = (Flat.convertExpr ce scope envVar envMap st).fst
-- List version for future use with call/newObj args
private def ValidConversionRList (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    : List Flat.Expr → List Core.Expr → Prop
  | [], [] => True
  | fe :: frest, ce :: crest =>
      ValidConversionR scope envVar envMap fe ce ∧
      ValidConversionRList scope envVar envMap frest crest
  | _, _ => False
end

/-- Exact conversion at a single state implies ValidConversionR. -/
private theorem convertExpr_implies_ValidConversionR (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st : Flat.CCState) :
    ValidConversionR scope envVar envMap
      (Flat.convertExpr e scope envVar envMap st).fst e := by
  cases e with
  | lit v => exact ⟨st, rfl⟩
  | var n => exact ⟨st, rfl⟩
  | this => exact ⟨st, rfl⟩
  | «break» l => exact ⟨st, rfl⟩
  | «continue» l => exact ⟨st, rfl⟩
  | forIn _ _ _ => exact ⟨st, rfl⟩
  | forOf _ _ _ => exact ⟨st, rfl⟩
  | «let» name init body =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR init scope envVar envMap st,
      convertExpr_implies_ValidConversionR body (name :: scope) envVar envMap _⟩
  | assign name value =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR value scope envVar envMap st⟩
  | «if» cond then_ else_ =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨convertExpr_implies_ValidConversionR cond scope envVar envMap st,
      convertExpr_implies_ValidConversionR then_ scope envVar envMap _,
      convertExpr_implies_ValidConversionR else_ scope envVar envMap _⟩
  | seq a b =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨convertExpr_implies_ValidConversionR a scope envVar envMap st,
      convertExpr_implies_ValidConversionR b scope envVar envMap _⟩
  | binary op lhs rhs =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR lhs scope envVar envMap st,
      convertExpr_implies_ValidConversionR rhs scope envVar envMap _⟩
  | unary op arg =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR arg scope envVar envMap st⟩
  | getProp obj prop =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR obj scope envVar envMap st⟩
  | setProp obj prop value =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR obj scope envVar envMap st,
      convertExpr_implies_ValidConversionR value scope envVar envMap _⟩
  | getIndex obj idx =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨convertExpr_implies_ValidConversionR obj scope envVar envMap st,
      convertExpr_implies_ValidConversionR idx scope envVar envMap _⟩
  | setIndex obj idx value =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨convertExpr_implies_ValidConversionR obj scope envVar envMap st,
      convertExpr_implies_ValidConversionR idx scope envVar envMap _,
      convertExpr_implies_ValidConversionR value scope envVar envMap _⟩
  | deleteProp obj prop =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR obj scope envVar envMap st⟩
  | typeof arg =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact convertExpr_implies_ValidConversionR arg scope envVar envMap st
  | throw arg =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact convertExpr_implies_ValidConversionR arg scope envVar envMap st
  | while_ cond body =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨convertExpr_implies_ValidConversionR cond scope envVar envMap st,
      convertExpr_implies_ValidConversionR body scope envVar envMap _⟩
  | labeled label body =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact ⟨rfl, convertExpr_implies_ValidConversionR body scope envVar envMap st⟩
  | await arg =>
    simp only [Flat.convertExpr, ValidConversionR]
    exact convertExpr_implies_ValidConversionR arg scope envVar envMap st
  | «return» arg =>
    cases arg with
    | none => simp only [Flat.convertExpr, Flat.convertOptExpr, ValidConversionR]
    | some e =>
      simp only [Flat.convertExpr, Flat.convertOptExpr, ValidConversionR]
      exact convertExpr_implies_ValidConversionR e scope envVar envMap st
  | tryCatch body catchParam catchBody finally_ =>
    simp only [Flat.convertExpr, ValidConversionR]
    cases finally_ with
    | none =>
      exact ⟨rfl, convertExpr_implies_ValidConversionR body scope envVar envMap st,
        convertExpr_implies_ValidConversionR catchBody (catchParam :: scope) envVar envMap _⟩
    | some fin =>
      exact ⟨rfl, convertExpr_implies_ValidConversionR body scope envVar envMap st,
        convertExpr_implies_ValidConversionR catchBody (catchParam :: scope) envVar envMap _,
        convertExpr_implies_ValidConversionR fin scope envVar envMap _⟩
  -- Base cases that fall through to ∃ st
  | call _ _ => exact ⟨st, rfl⟩
  | newObj _ _ => exact ⟨st, rfl⟩
  | objectLit _ => exact ⟨st, rfl⟩
  | arrayLit _ => exact ⟨st, rfl⟩
  | functionDef _ _ _ _ _ => exact ⟨st, rfl⟩
  | yield _ _ => exact ⟨st, rfl⟩

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
  cheap.objects.size = fheap.objects.size ∧
  cheap.nextAddr = fheap.nextAddr ∧
  ∀ addr, addr < cheap.objects.size → cheap.objects[addr]? = fheap.objects[addr]?

private theorem HeapCorr_refl (h : Core.Heap) : HeapCorr h h :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

private theorem HeapCorr_get {ch fh : Core.Heap} {addr : Nat} (hc : HeapCorr ch fh) (hlt : addr < ch.objects.size) :
    ch.objects[addr]? = fh.objects[addr]? := hc.2.2 addr hlt

/-- Both heaps push the same object: size-equality relation is maintained. -/
private theorem HeapCorr_alloc_both {ch fh : Core.Heap} (hc : HeapCorr ch fh)
    (p : List (Core.PropName × Core.Value)) :
    HeapCorr { objects := ch.objects.push p, nextAddr := ch.nextAddr + 1 }
             { objects := fh.objects.push p, nextAddr := fh.nextAddr + 1 } := by
  have hsize := hc.1
  have hnext := hc.2.1
  refine ⟨by simp only [Array.size_push]; omega, by rw [hnext], fun addr hlt => ?_⟩
  simp [Array.size_push] at hlt
  rcases Nat.lt_or_ge addr ch.objects.size with h | h
  · simp only [Array.getElem?_push, show ¬(addr = ch.objects.size) from by omega,
               show ¬(addr = fh.objects.size) from by omega, ite_false]
    exact hc.2.2 addr h
  · have haddr_eq : addr = ch.objects.size := by omega
    subst haddr_eq
    simp only [Array.getElem?_push, hsize, ite_true]

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
    (hinj : HeapInj f ch fh)
    (p : List (Core.PropName × Core.Value)) :
    HeapInj f { objects := ch.objects.push p, nextAddr := ch.nextAddr + 1 }
             { objects := fh.objects.push p, nextAddr := fh.nextAddr + 1 } :=
  HeapCorr_alloc_both hinj p

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

private theorem list_find?_mem {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : l.find? p = some x) : x ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons a as ih =>
    simp only [List.find?] at h
    split at h
    · exact Option.some.inj h ▸ .head _
    · exact .tail _ (ih h)

private theorem HeapInj_set_same {ch fh : Core.Heap} {f : Nat → Nat}
    (hinj : HeapInj f ch fh) (addr : Nat) (hlt : addr < ch.objects.size)
    (p : List (Core.PropName × Core.Value)) :
    HeapInj f { ch with objects := ch.objects.set! addr p }
             { fh with objects := fh.objects.set! addr p } := by
  have sz_eq : ∀ (a : Array (List (Core.PropName × Core.Value))) (i : Nat) (v : List _),
      (a.set! i v).size = a.size := fun a i v => by
    simp only [Array.set!, Array.setIfInBounds]; split
    · exact Array.size_set ..
    · rfl
  refine ⟨by simp only [sz_eq]; exact hinj.1, by simp; exact hinj.2.1, fun addr' hlt' => ?_⟩
  simp only [sz_eq] at hlt'
  have hlt_f : addr < fh.objects.size := hinj.1 ▸ hlt
  by_cases h : addr' = addr
  · subst h; simp [Array.set!, Array.setIfInBounds, hlt, hlt_f]
  · simp only [Array.set!, Array.setIfInBounds, hlt, hlt_f, ↓reduceDIte]
    rw [Array.getElem?_set, Array.getElem?_set]
    simp [Ne.symm h, hinj.2.2 addr' hlt']

/-- All object addresses in a Core value are valid heap addresses. -/
private def ValueAddrWF (v : Core.Value) (heapSize : Nat) : Prop :=
  match v with
  | .object addr => addr < heapSize
  | _ => True

mutual
/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
def ExprAddrWF : Core.Expr → Nat → Prop
  | .lit v, n => ValueAddrWF v n
  | .var _, _ => True
  | .«let» _ init body, n => ExprAddrWF init n ∧ ExprAddrWF body n
  | .assign _ value, n => ExprAddrWF value n
  | .«if» cond t e, n => ExprAddrWF cond n ∧ ExprAddrWF t n ∧ ExprAddrWF e n
  | .seq a b, n => ExprAddrWF a n ∧ ExprAddrWF b n
  | .call f args, n => ExprAddrWF f n ∧ ExprAddrListWF args n
  | .newObj f args, n => ExprAddrWF f n ∧ ExprAddrListWF args n
  | .getProp e _, n => ExprAddrWF e n
  | .setProp o _ v, n => ExprAddrWF o n ∧ ExprAddrWF v n
  | .getIndex e1 e2, n => ExprAddrWF e1 n ∧ ExprAddrWF e2 n
  | .setIndex o i v, n => ExprAddrWF o n ∧ ExprAddrWF i n ∧ ExprAddrWF v n
  | .deleteProp e _, n => ExprAddrWF e n
  | .typeof e, n => ExprAddrWF e n
  | .unary _ e, n => ExprAddrWF e n
  | .binary _ l r, n => ExprAddrWF l n ∧ ExprAddrWF r n
  | .objectLit props, n => ExprAddrPropListWF props n
  | .arrayLit es, n => ExprAddrListWF es n
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

/-- All object addresses in a list of Core expressions are valid heap addresses. -/
def ExprAddrListWF : List Core.Expr → Nat → Prop
  | [], _ => True
  | e :: es, n => ExprAddrWF e n ∧ ExprAddrListWF es n

/-- All object addresses in a property list of Core expressions are valid heap addresses. -/
def ExprAddrPropListWF : List (String × Core.Expr) → Nat → Prop
  | [], _ => True
  | (_, e) :: ps, n => ExprAddrWF e n ∧ ExprAddrPropListWF ps n
end

private theorem ValueAddrWF_mono {v : Core.Value} {n m : Nat}
    (h : ValueAddrWF v n) (hle : n ≤ m) : ValueAddrWF v m := by
  cases v <;> simp [ValueAddrWF] at * <;> omega

mutual
private theorem ExprAddrWF_mono : (e : Core.Expr) → {n m : Nat} →
    ExprAddrWF e n → (n ≤ m) → ExprAddrWF e m
  | .lit v, _, _, h, hle => ValueAddrWF_mono h hle
  | .var _, _, _, _, _ => trivial
  | .call f args, _, _, h, hle => ⟨ExprAddrWF_mono f h.1 hle, ExprAddrListWF_mono args h.2 hle⟩
  | .newObj f args, _, _, h, hle => ⟨ExprAddrWF_mono f h.1 hle, ExprAddrListWF_mono args h.2 hle⟩
  | .objectLit props, _, _, h, hle => ExprAddrPropListWF_mono props h hle
  | .arrayLit es, _, _, h, hle => ExprAddrListWF_mono es h hle
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

private theorem ExprAddrListWF_mono : (es : List Core.Expr) → {n m : Nat} →
    ExprAddrListWF es n → (n ≤ m) → ExprAddrListWF es m
  | [], _, _, _, _ => trivial
  | e :: es, _, _, h, hle => ⟨ExprAddrWF_mono e h.1 hle, ExprAddrListWF_mono es h.2 hle⟩
  termination_by es => sizeOf es
  decreasing_by all_goals (try simp_wf) <;> omega

private theorem ExprAddrPropListWF_mono : (ps : List (String × Core.Expr)) → {n m : Nat} →
    ExprAddrPropListWF ps n → (n ≤ m) → ExprAddrPropListWF ps m
  | [], _, _, _, _ => trivial
  | (_, e) :: ps, _, _, h, hle => ⟨ExprAddrWF_mono e h.1 hle, ExprAddrPropListWF_mono ps h.2 hle⟩
  termination_by ps => sizeOf ps
  decreasing_by all_goals (try simp_wf) <;> omega
end

private theorem ExprAddrPropListWF_firstNonValueProp_target
    {props : List (Core.PropName × Core.Expr)} {done propName target rest n}
    (hfnv : Core.firstNonValueProp props = some (done, propName, target, rest))
    (hwf : ExprAddrPropListWF props n) : ExprAddrWF target n := by
  induction props generalizing done propName target rest with
  | nil => simp [Core.firstNonValueProp] at hfnv
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Core.firstNonValueProp at hfnv
    split at hfnv
    · -- pe = .lit _
      split at hfnv
      · next heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
        obtain ⟨_, _, rfl, rfl⟩ := hfnv
        simp only [ExprAddrPropListWF] at hwf; exact ih heq hwf.2
      · simp at hfnv
    · -- pe is not a lit
      simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
      obtain ⟨_, rfl, rfl, _⟩ := hfnv
      simp only [ExprAddrPropListWF] at hwf; exact hwf.1

private theorem ExprAddrListWF_firstNonValueExpr_target
    {es : List Core.Expr} {done target rest n}
    (hfnv : Core.firstNonValueExpr es = some (done, target, rest))
    (hwf : ExprAddrListWF es n) : ExprAddrWF target n := by
  induction es generalizing done target rest with
  | nil => simp [Core.firstNonValueExpr] at hfnv
  | cons e tl ih =>
    unfold Core.firstNonValueExpr at hfnv
    split at hfnv
    · -- e = .lit _
      split at hfnv
      · next heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
        obtain ⟨_, rfl, rfl⟩ := hfnv
        simp only [ExprAddrListWF] at hwf; exact ih heq hwf.2
      · simp at hfnv
    · -- e is not a lit
      simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
      obtain ⟨rfl, rfl, rfl⟩ := hfnv
      simp only [ExprAddrListWF] at hwf; exact hwf.1

private theorem ExprAddrPropListWF_append {l1 l2 : List (Core.PropName × Core.Expr)} {n} :
    ExprAddrPropListWF (l1 ++ l2) n ↔ ExprAddrPropListWF l1 n ∧ ExprAddrPropListWF l2 n := by
  induction l1 with
  | nil => simp [ExprAddrPropListWF]
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    simp only [List.cons_append, ExprAddrPropListWF]
    rw [ih]; constructor
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

private theorem ExprAddrListWF_append {l1 l2 : List Core.Expr} {n} :
    ExprAddrListWF (l1 ++ l2) n ↔ ExprAddrListWF l1 n ∧ ExprAddrListWF l2 n := by
  induction l1 with
  | nil => simp [ExprAddrListWF]
  | cons e tl ih =>
    simp only [List.cons_append, ExprAddrListWF]
    rw [ih]; constructor
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

private theorem ExprAddrPropListWF_firstNonValueProp_reconstruct
    {props : List (Core.PropName × Core.Expr)} {done propName target rest n m}
    {target' : Core.Expr}
    (hfnv : Core.firstNonValueProp props = some (done, propName, target, rest))
    (hwf : ExprAddrPropListWF props n) (hwf_new : ExprAddrWF target' m)
    (hn_le_m : n ≤ m) :
    ExprAddrPropListWF (done ++ [(propName, target')] ++ rest) m := by
  induction props generalizing done propName target rest with
  | nil => simp [Core.firstNonValueProp] at hfnv
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Core.firstNonValueProp at hfnv
    split at hfnv
    · -- pe = .lit _
      split at hfnv
      · next heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hfnv
        simp only [List.cons_append, ExprAddrPropListWF]
        simp only [ExprAddrPropListWF] at hwf
        exact And.intro (ExprAddrWF_mono _ hwf.1 hn_le_m) (ih heq hwf.2)
      · simp at hfnv
    · -- pe is not a lit
      simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfnv
      simp only [List.nil_append, ExprAddrPropListWF]
      simp only [ExprAddrPropListWF] at hwf
      exact And.intro hwf_new (ExprAddrPropListWF_mono _ hwf.2 hn_le_m)

private theorem ExprAddrListWF_firstNonValueExpr_reconstruct
    {es : List Core.Expr} {done target rest n m}
    {target' : Core.Expr}
    (hfnv : Core.firstNonValueExpr es = some (done, target, rest))
    (hwf : ExprAddrListWF es n) (hwf_new : ExprAddrWF target' m)
    (hn_le_m : n ≤ m) :
    ExprAddrListWF (done ++ [target'] ++ rest) m := by
  induction es generalizing done target rest with
  | nil => simp [Core.firstNonValueExpr] at hfnv
  | cons e tl ih =>
    unfold Core.firstNonValueExpr at hfnv
    split at hfnv
    · -- e = .lit _
      split at hfnv
      · next heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
        obtain ⟨rfl, rfl, rfl⟩ := hfnv
        simp only [List.cons_append, ExprAddrListWF]
        simp only [ExprAddrListWF] at hwf
        exact And.intro (ExprAddrWF_mono _ hwf.1 hn_le_m) (ih heq hwf.2)
      · simp at hfnv
    · -- e is not a lit
      simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
      obtain ⟨rfl, rfl, rfl⟩ := hfnv
      simp only [List.nil_append, ExprAddrListWF]
      simp only [ExprAddrListWF] at hwf
      exact And.intro hwf_new (ExprAddrListWF_mono _ hwf.2 hn_le_m)

private theorem Core_step_heap_size_mono
    {s s' : Core.State} {t : Core.TraceEvent}
    (hstep : Core.step? s = some (t, s')) : s.heap.objects.size ≤ s'.heap.objects.size := by
  exact Core.step?_heap_ge _ _ _ hstep

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

private theorem evalUnary_valueAddrWF (op : Core.UnaryOp) (v : Core.Value) (n : Nat)
    (h : ValueAddrWF v n) : ValueAddrWF (Core.evalUnary op v) n := by
  cases op <;> cases v <;> simp [Core.evalUnary, ValueAddrWF, Core.toBoolean, Core.toNumber] <;> try trivial

private theorem ValueAddrWF_ite (c : Prop) [Decidable c] (v1 v2 : Core.Value) (n : Nat)
    (h1 : ValueAddrWF v1 n) (h2 : ValueAddrWF v2 n) :
    ValueAddrWF (if c then v1 else v2) n := by
  split <;> assumption

private theorem evalBinary_valueAddrWF (op : Core.BinOp) (a b : Core.Value) (n : Nat)
    (ha : ValueAddrWF a n) (hb : ValueAddrWF b n) : ValueAddrWF (Core.evalBinary op a b) n := by
  cases op <;> cases a <;> cases b <;> simp only [Core.evalBinary, Core.toBoolean, Core.toNumber]
    <;> first
      | assumption
      | simp [ValueAddrWF]
      | (apply ValueAddrWF_ite <;> first | assumption | simp [ValueAddrWF])
      | skip
  -- logAnd/logOr .object cases: ValueAddrWF_ite leaves addr < n, which is exactly hb unfolded
  all_goals (apply ValueAddrWF_ite <;> first | assumption | simp [ValueAddrWF])
  all_goals exact hb

/-- Correspondence between Core function closures and Flat lifted function
    definitions. For each Core closure at index `i`, the Flat function table
    at the same index has:
    • matching parameter names
    • a body that is the closure-converted form of the Core body
    • an environment parameter that correctly maps the captured environment
    This is sorry'd — establishing the properties requires induction over
    the closure-conversion pass and is future work. -/
private def FuncsCorr (injMap : Nat → Nat)
    (coreFuncs : Array Core.FuncClosure) (flatFuncs : Array Flat.FuncDef)
    (ccFuncs : Array Flat.FuncDef) : Prop :=
  -- (1) Flat runtime funcs extend the CC-produced function table
  ccFuncs.size ≤ flatFuncs.size ∧
  (∀ i, i < ccFuncs.size → flatFuncs[i]? = ccFuncs[i]?) ∧
  -- (2) Each non-builtin Core closure corresponds to a Flat function definition.
  --     Index 0 (consoleLogIdx) is excluded: both Core and Flat handle console.log
  --     via special-case dispatch in their step functions, not via function lookup.
  --     Note: closureConvert does not add a logBuiltin placeholder, so Core indices
  --     start at 1 (after logBuiltin) while Flat indices start at 0.
  (∀ (i : Nat) (fc : Core.FuncClosure),
    i > 0 →
    coreFuncs[i]? = some fc →
    ∃ (fd : Flat.FuncDef),
      flatFuncs[i]? = some fd ∧
      fd.params = fc.params ∧
      -- fd.body is the closure-converted form of fc.body
      ∃ (innerEnvMap : Flat.EnvMapping) (st st' : Flat.CCState),
        fd.body = (Flat.convertExpr fc.body fc.params fd.envParam innerEnvMap st).fst ∧
        st' = (Flat.convertExpr fc.body fc.params fd.envParam innerEnvMap st).snd) ∧
  -- (3) Captured environment correspondence (also excludes consoleLogIdx)
  (∀ (i : Nat) (fc : Core.FuncClosure),
    i > 0 →
    coreFuncs[i]? = some fc →
    ∃ (fd : Flat.FuncDef),
      flatFuncs[i]? = some fd ∧
      ∃ (captured : List String) (innerEnvMap : Flat.EnvMapping),
        innerEnvMap = Flat.indexedMap captured 0 ∧
        captured.length ≤ fc.capturedEnv.length ∧
        (∀ (name : String), name ∈ captured →
          ∃ (v : Core.Value), (name, v) ∈ fc.capturedEnv))

/-- Simulation relation for closure conversion: Flat and Core states
    have matching traces, environment correspondence, and expression
    correspondence through the conversion. -/
private def CC_SimRel (_s : Core.Program) (t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  (∃ injMap, HeapInj injMap sc.heap sf.heap ∧ EnvCorrInj injMap sc.env sf.env ∧
    FuncsCorr injMap sc.funcs sf.funcs t.functions) ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧
  EnvAddrWF sc.env sc.heap.objects.size ∧
  HeapValuesWF sc.heap ∧
  sc.heap.nextAddr = sc.heap.objects.size ∧
  sc.expr.supported = true ∧
  (∀ (i : Nat) (fd : Core.FuncClosure), sc.funcs[i]? = some fd → fd.body.supported = true) ∧
  (∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st) ∨
  -- Error disjunct: after an error step, Flat may have dropped compound-expr
  -- wrappers (let/assign/seq) leaving a terminal literal value, while Core
  -- retains the wrapper.  The Flat state cannot step further (.lit never steps),
  -- so the simulation terminates here.
  (∃ (v : Flat.Value), sf.expr = .lit v)

private theorem closureConvert_init_related
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (h_supp : s.body.supported = true) :
    CC_SimRel s t (Flat.initialState t) (Core.initialState s) := by
  unfold CC_SimRel Flat.initialState Core.initialState
  refine ⟨rfl, ⟨id, HeapInj_id _, ?_, ?funcCorr_init⟩, h_wf, ?_, ?_, ?_, ?_, h_supp, ?funcs_supp, ?conv⟩
  · -- EnvCorrInj id: both envs have exactly one binding: "console" → .object 0
    show EnvCorr _ _
    have h_empty : EnvCorr Core.Env.empty Flat.Env.empty := by
      constructor <;> intro _ _ h <;> simp [Core.Env.empty, Core.Env.lookup, Flat.Env.empty, Flat.Env.lookup] at h
    exact EnvCorr_extend h_empty "console" (.object 0)
  case funcCorr_init =>
    -- FuncsCorr for initial state: Core has [logBuiltin] (only index 0).
    -- All per-function conditions require i > 0, so they are vacuously true.
    unfold FuncsCorr
    refine ⟨Nat.le_refl _, fun _ _ => rfl, ?_, ?_⟩ <;> {
      intro i fc hi hfc
      exfalso
      cases i with
      | zero => omega
      | succ n => simp_all
    }
  · -- ExprAddrWF: source programs don't contain .object addresses
    exact h_addr_wf
  · -- EnvAddrWF: initial env has "console" → .object 0, heap has 1 object
    exact EnvAddrWF_extend (EnvAddrWF_empty 1) "console" (.object 0) (by simp [ValueAddrWF])
  · -- HeapValuesWF: initial heap has console object with log function
    intro addr haddr props hprops kv hkv; dsimp at *; simp_all [ValueAddrWF]; rw [← hprops] at hkv; simp at hkv; subst hkv; trivial
  · -- heap.nextAddr = heap.objects.size
    rfl
  case funcs_supp =>
    -- FuncsSupported: initial funcs = #[logBuiltin], body = .lit .undefined
    intro i fd hi
    dsimp [Core.initialState] at hi
    cases i with
    | zero => simp at hi; rw [← hi]; rfl
    | succ n => exact absurd hi (by simp)
  case conv =>
    exact Or.inl (by
      unfold Flat.closureConvert at h
      simp only [Except.ok.injEq] at h
      let st2 := (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).fst.foldl
        (fun s f => (s.addFunc f).2) (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).2
      refine ⟨[], "__env_main", [], st2,
        (Flat.convertExpr s.body [] "__env_main" [] st2).2, ?_⟩
      rw [← h])

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

/-- convertExpr of a non-value supported expression is not a Flat value.
    The `supported` guard eliminates forIn/forOf/yield/await (which convert to .lit .undefined). -/
private theorem convertExpr_not_value_supported (e : Core.Expr)
    (h : Core.exprValue? e = none)
    (hsupp : e.supported = true)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none := by
  cases e with
  | lit v => simp [Core.exprValue?] at h
  | forIn _ _ _ => simp [Core.Expr.supported] at hsupp
  | forOf _ _ _ => simp [Core.Expr.supported] at hsupp
  | yield _ _ => simp [Core.Expr.supported] at hsupp
  | await _ => simp [Core.Expr.supported] at hsupp
  | var _ =>
    simp only [Flat.convertExpr]
    split <;> simp [Flat.exprValue?]
  | functionDef _ _ _ _ _ => unfold Flat.convertExpr; simp [Flat.exprValue?]
  | _ => unfold Flat.convertExpr <;>
    (try { simp [Flat.exprValue?]; done }) <;>
    (try { split <;> simp [Flat.exprValue?]; done })

/-- For supported, non-literal Core expressions, convertExpr never produces .lit.
    Directly eliminates forIn/forOf/yield/await via the supported guard. -/
private theorem convertExpr_not_lit_supported (e : Core.Expr) (scope : List String)
    (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : ∀ v, e ≠ .lit v)
    (hsupp : e.supported = true) :
    ∀ fv, (Flat.convertExpr e scope envVar envMap st).fst ≠ .lit fv := by
  intro fv; cases e with
  | lit v => exact absurd rfl (h v)
  | forIn _ _ _ => simp [Core.Expr.supported] at hsupp
  | forOf _ _ _ => simp [Core.Expr.supported] at hsupp
  | yield _ _ => simp [Core.Expr.supported] at hsupp
  | await _ => simp [Core.Expr.supported] at hsupp
  | var _ => simp [Flat.convertExpr]; split <;> simp
  | functionDef _ _ _ _ _ => unfold Flat.convertExpr; simp
  | _ => unfold Flat.convertExpr; simp

/-- If firstNonValueExpr finds a target in a list, and all elements are supported,
    then the target is supported. -/
private theorem listSupported_firstNonValueExpr_target {es : List Core.Expr}
    {done target rest}
    (h : Core.firstNonValueExpr es = some (done, target, rest))
    (hsupp : Core.Expr.listSupported es = true) :
    target.supported = true := by
  induction es generalizing done target rest with
  | nil => simp [Core.firstNonValueExpr] at h
  | cons e es' ih =>
    unfold Core.firstNonValueExpr at h
    simp [Core.Expr.listSupported] at hsupp
    split at h
    · -- e = .lit v: recurse
      match hrest : Core.firstNonValueExpr es' with
      | some val =>
        obtain ⟨d', t', r'⟩ := val
        simp [hrest] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact ih hrest hsupp.2
      | none => simp [hrest] at h
    · -- e is the target
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact hsupp.1

/-- If firstNonValueProp finds a target in a prop list, and all props are supported,
    then the target is supported. -/
private theorem propListSupported_firstNonValueProp_target {ps : List (Core.PropName × Core.Expr)}
    {done name target rest}
    (h : Core.firstNonValueProp ps = some (done, name, target, rest))
    (hsupp : Core.Expr.propListSupported ps = true) :
    target.supported = true := by
  induction ps generalizing done name target rest with
  | nil => simp [Core.firstNonValueProp] at h
  | cons p ps' ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Core.firstNonValueProp at h
    simp [Core.Expr.propListSupported] at hsupp
    split at h
    · -- pe = .lit v: recurse
      match hrest : Core.firstNonValueProp ps' with
      | some val =>
        obtain ⟨d', n', t', r'⟩ := val
        simp [hrest] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ih hrest hsupp.2
      | none => simp [hrest] at h
    · -- pe is the target
      simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact hsupp.1

/-- listSupported distributes over append. -/
private theorem listSupported_append (a b : List Core.Expr) :
    Core.Expr.listSupported (a ++ b) = (Core.Expr.listSupported a && Core.Expr.listSupported b) := by
  induction a with
  | nil => simp [Core.Expr.listSupported]
  | cons e es ih => simp [Core.Expr.listSupported, ih, Bool.and_assoc]

/-- propListSupported distributes over append. -/
private theorem propListSupported_append (a b : List (Core.PropName × Core.Expr)) :
    Core.Expr.propListSupported (a ++ b) = (Core.Expr.propListSupported a && Core.Expr.propListSupported b) := by
  induction a with
  | nil => simp [Core.Expr.propListSupported]
  | cons p ps ih => obtain ⟨pn, pe⟩ := p; simp [Core.Expr.propListSupported, ih, Bool.and_assoc]

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
  simp [Flat.step?, h]

private theorem Flat_step?_this_not_found_explicit (s : Flat.State)
    (h : s.env.lookup "this" = none) :
    Flat.step? { s with expr := .this } =
      some (.silent, { expr := .lit .undefined, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]

private theorem Flat_step?_var_found_explicit (s : Flat.State) (name : String) (v : Flat.Value)
    (h : s.env.lookup name = some v) :
    Flat.step? { s with expr := .var name } =
      some (.silent, { expr := .lit v, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]

private theorem Flat_step?_var_not_found_explicit (s : Flat.State) (name : String)
    (h : s.env.lookup name = none) :
    Flat.step? { s with expr := .var name } =
      some (.error ("ReferenceError: " ++ name),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("ReferenceError: " ++ name)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]

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

private theorem Flat_step?_break (s : Flat.State) (label : Option Core.LabelName) :
    Flat.step? { s with expr := .«break» label } =
      some (.error ("break:" ++ label.getD ""),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("break:" ++ label.getD "")],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Flat_step?_continue (s : Flat.State) (label : Option Core.LabelName) :
    Flat.step? { s with expr := .«continue» label } =
      some (.error ("continue:" ++ label.getD ""),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("continue:" ++ label.getD "")],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_break (s : Core.State) (label : Option Core.LabelName) :
    Core.step? { s with expr := .«break» label } =
      some (.error ("break:" ++ label.getD ""),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("break:" ++ label.getD "")],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace]; cases label <;> simp [Option.getD]

private theorem Core_step?_continue (s : Core.State) (label : Option Core.LabelName) :
    Core.step? { s with expr := .«continue» label } =
      some (.error ("continue:" ++ label.getD ""),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("continue:" ++ label.getD "")],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace]; cases label <;> simp [Option.getD]

private theorem Flat_step?_labeled (s : Flat.State) (label : Core.LabelName) (body : Flat.Expr) :
    Flat.step? { s with expr := .labeled label body } =
      some (.silent, { expr := body, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_labeled (s : Core.State) (label : Core.LabelName) (body : Core.Expr) :
    Core.step? { s with expr := .labeled label body } =
      some (.silent, { expr := body, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace]

private theorem Flat_step?_return_none (s : Flat.State) :
    Flat.step? { s with expr := .«return» none } =
      some (.error "return:undefined",
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error "return:undefined"],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_return_none (s : Core.State) :
    Core.step? { s with expr := .«return» none } =
      some (.error "return:undefined",
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error "return:undefined"],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace]

private theorem Flat_step?_return_some_lit (s : Flat.State) (fv : Flat.Value) :
    Flat.step? { s with expr := .«return» (some (.lit fv)) } =
      some (.error ("return:" ++ Flat.valueToString fv),
        { expr := .lit fv, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("return:" ++ Flat.valueToString fv)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_return_some_lit (s : Core.State) (cv : Core.Value) :
    Core.step? { s with expr := .«return» (some (.lit cv)) } =
      some (.error ("return:" ++ Core.valueToString cv),
        { expr := .lit cv, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("return:" ++ Core.valueToString cv)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, Core.exprValue?]

private theorem Flat_step?_throw_lit (s : Flat.State) (fv : Flat.Value) :
    Flat.step? { s with expr := .throw (.lit fv) } =
      some (.error (Flat.valueToString fv),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error (Flat.valueToString fv)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_throw_lit (s : Core.State) (cv : Core.Value) :
    Core.step? { s with expr := .throw (.lit cv) } =
      some (.error (Core.valueToString cv),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error (Core.valueToString cv)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, Core.exprValue?]

private theorem Flat_step?_yield_none (s : Flat.State) (delegate : Bool) :
    Flat.step? { s with expr := .yield none delegate } =
      some (.silent,
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_yield_none (s : Core.State) (delegate : Bool) :
    Core.step? { s with expr := .yield none delegate } =
      some (.silent,
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace]

private theorem Flat_step?_yield_some_lit (s : Flat.State) (fv : Flat.Value) (delegate : Bool) :
    Flat.step? { s with expr := .yield (some (.lit fv)) delegate } =
      some (.silent,
        { expr := .lit fv, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_yield_some_lit (s : Core.State) (cv : Core.Value) (delegate : Bool) :
    Core.step? { s with expr := .yield (some (.lit cv)) delegate } =
      some (.silent,
        { expr := .lit cv, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, Core.exprValue?]

private theorem Flat_step?_await_lit (s : Flat.State) (fv : Flat.Value) :
    Flat.step? { s with expr := .await (.lit fv) } =
      some (.silent,
        { expr := .lit fv, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Core_step?_await_lit (s : Core.State) (cv : Core.Value) :
    Core.step? { s with expr := .await (.lit cv) } =
      some (.silent,
        { expr := .lit cv, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace, Core.exprValue?]

-- Flat stepping helpers for non-value sub-expressions
private theorem Flat_step?_throw_step (s : Flat.State) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .throw fe } =
      some (t, { expr := .throw sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_throw_step (s : Core.State) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .throw e } =
      some (t, { expr := .throw sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_return_some_step (s : Flat.State) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .«return» (some fe) } =
      some (t, { expr := .«return» (some sa.expr), env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_return_some_step (s : Core.State) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .«return» (some e) } =
      some (t, { expr := .«return» (some sa.expr), env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_yield_some_step (s : Flat.State) (fe : Flat.Expr) (delegate : Bool)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .yield (some fe) delegate } =
      some (t, { expr := .yield (some sa.expr) delegate, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_yield_some_step (s : Core.State) (e : Core.Expr) (delegate : Bool)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .yield (some e) delegate } =
      some (t, { expr := .yield (some sa.expr) delegate, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_await_step (s : Flat.State) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .await fe } =
      some (t, { expr := .await sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_await_step (s : Core.State) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .await e } =
      some (t, { expr := .await sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_unary_value (s : Flat.State) (op : Core.UnaryOp) (fv : Flat.Value) :
    Flat.step? { s with expr := .unary op (.lit fv) } =
      some (.silent,
        { expr := .lit (Flat.evalUnary op fv), env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Flat_step?_typeof_value (s : Flat.State) (fv : Flat.Value) :
    Flat.step? { s with expr := .typeof (.lit fv) } =
      some (.silent,
        { expr := .lit (match fv with
            | .undefined => .string "undefined" | .null => .string "object"
            | .bool _ => .string "boolean" | .number _ => .string "number"
            | .string _ => .string "string" | .object _ => .string "object"
            | .closure _ _ => .string "function"),
          env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]; cases fv <;> rfl

private theorem Flat_step?_assign_value (s : Flat.State) (name : String) (fv : Flat.Value) :
    Flat.step? { s with expr := .assign name (.lit fv) } =
      some (.silent,
        { expr := .lit fv, env := Flat.Env.assign s.env name fv, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Flat_step?_unary_step (s : Flat.State) (op : Core.UnaryOp) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .unary op fe } =
      some (t, { expr := .unary op sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_unary_step (s : Core.State) (op : Core.UnaryOp) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .unary op e } =
      some (t, { expr := .unary op sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_typeof_step (s : Flat.State) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .typeof fe } =
      some (t, { expr := .typeof sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_typeof_step (s : Core.State) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .typeof e } =
      some (t, { expr := .typeof sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_assign_step (s : Flat.State) (name : String) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .assign name fe } =
      some (t, { expr := .assign name sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss, hnv]
  split <;> simp_all [Flat.exprValue?]

-- Flat_step?_assign_error: removed (unused after by_cases restructuring; had parse issues)

private theorem Core_step?_assign_step (s : Core.State) (name : String) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .assign name e } =
      some (t, { expr := .assign name sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_deleteProp_step (s : Flat.State) (prop : Core.PropName) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .deleteProp fe prop } =
      some (t, { expr := .deleteProp sa.expr prop, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_deleteProp_step (s : Core.State) (prop : Core.PropName) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .deleteProp e prop } =
      some (t, { expr := .deleteProp sa.expr prop, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_getProp_step (s : Flat.State) (prop : Core.PropName) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .getProp fe prop } =
      some (t, { expr := .getProp sa.expr prop, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_getProp_step (s : Core.State) (prop : Core.PropName) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .getProp e prop } =
      some (t, { expr := .getProp sa.expr prop, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_getIndex_step (s : Flat.State) (idx : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .getIndex fe idx } =
      some (t, { expr := .getIndex sa.expr idx, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases fe with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]

private theorem Core_step?_getIndex_step (s : Core.State) (idx : Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .getIndex e idx } =
      some (t, { expr := .getIndex sa.expr idx, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_setProp_obj_step (s : Flat.State) (prop : Core.PropName) (value : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .setProp fe prop value } =
      some (t, { expr := .setProp sa.expr prop value, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases fe with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]

private theorem Core_step?_setProp_obj_step (s : Core.State) (prop : Core.PropName) (value : Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .setProp e prop value } =
      some (t, { expr := .setProp sa.expr prop value, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_setIndex_obj_step (s : Flat.State) (idx value : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .setIndex fe idx value } =
      some (t, { expr := .setIndex sa.expr idx value, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases fe with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]

private theorem Core_step?_setIndex_obj_step (s : Core.State) (idx value : Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .setIndex e idx value } =
      some (t, { expr := .setIndex sa.expr idx value, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_call_func_step (s : Flat.State) (envExpr : Flat.Expr)
    (args : List Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .call fe envExpr args } =
      some (t, { expr := .call sa.expr envExpr args, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases fe with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]

/-- Flat call with value callee+env, non-value arg: step the first non-value arg. -/
private theorem Flat_step?_call_value_step_arg (s : Flat.State)
    (fv : Flat.Value) (ev : Flat.Value) (args : List Flat.Expr)
    (hvals : Flat.valuesFromExprList? args = none)
    (done : List Flat.Expr) (target : Flat.Expr) (remaining : List Flat.Expr)
    (hfnv : Flat.firstNonValueExpr args = some (done, target, remaining))
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := target } = some (t, sa)) :
    Flat.step? { s with expr := .call (.lit fv) (.lit ev) args } =
      some (t, { expr := .call (.lit fv) (.lit ev) (done ++ [sa.expr] ++ remaining),
                 env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  unfold Flat.step?; simp only [Flat.exprValue?, hvals]; rw [hfnv]; simp only [hss]; rfl

/-- Flat call with non-closure value callee, all-value args: return undefined. -/
private theorem Flat_step?_call_nonclosure (s : Flat.State)
    (fv : Flat.Value) (ev : Flat.Value) (args : List Flat.Expr)
    (argVals : List Flat.Value)
    (hvals : Flat.valuesFromExprList? args = some argVals)
    (hnc : ∀ fi ep, fv ≠ .closure fi ep) :
    Flat.step? { s with expr := .call (.lit fv) (.lit ev) args } =
      some (.silent, { expr := .lit .undefined, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  cases fv with
  | closure fi ep => exact absurd rfl (hnc fi ep)
  | _ => simp [Flat.step?, Flat.exprValue?, hvals]

/-- Flat call with value callee+env, non-value arg, sub-step returns none: overall none. -/
private theorem Flat_step?_call_value_arg_none (s : Flat.State)
    (fv : Flat.Value) (ev : Flat.Value) (args : List Flat.Expr)
    (hvals : Flat.valuesFromExprList? args = none)
    (done : List Flat.Expr) (target : Flat.Expr) (remaining : List Flat.Expr)
    (hfnv : Flat.firstNonValueExpr args = some (done, target, remaining))
    (hss : Flat.step? { s with expr := target } = none) :
    Flat.step? { s with expr := .call (.lit fv) (.lit ev) args } = none := by
  unfold Flat.step?; simp only [Flat.exprValue?, hvals]; rw [hfnv]; simp only [hss]

/-- Flat call with closure at consoleLogIdx, env value, all arg values. -/
private theorem Flat_step?_call_consoleLog_vals (s : Flat.State)
    (envPtr : Nat) (envVal : Flat.Value) (args : List Flat.Expr)
    (argVals : List Flat.Value)
    (hvals : Flat.valuesFromExprList? args = some argVals) :
    Flat.step? { s with expr := .call (.lit (.closure Core.consoleLogIdx envPtr)) (.lit envVal) args } =
      let msg := match argVals with
        | [v] => Flat.valueToString v
        | vs => String.intercalate " " (vs.map Flat.valueToString)
      some (.log msg, { expr := .lit .undefined, env := s.env, heap := s.heap,
                        trace := s.trace ++ [.log msg], funcs := s.funcs,
                        callStack := s.callStack }) := by
  unfold Flat.step?
  simp [Flat.exprValue?, hvals, Core.consoleLogIdx, Flat.step?_pushTrace_expand]
  cases argVals with | nil => rfl | cons hd tl => cases tl with | nil => rfl | cons _ _ => rfl

/-- Core call with function at consoleLogIdx, all-value args (general). -/
private theorem Core_step?_call_consoleLog_general (args : List Core.Expr) (argVals : List Core.Value)
    (env : Core.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Core.FuncClosure) (cs : List (List (Core.VarName × Core.Value)))
    (hargs : Core.allValues args = some argVals) :
    let msg := match argVals with
      | [v] => Core.valueToString v
      | vs => String.intercalate " " (vs.map Core.valueToString)
    Core.step? ⟨.call (.lit (.function Core.consoleLogIdx)) args, env, heap, trace, funcs, cs⟩ =
      some (.log msg, ⟨.lit .undefined, env, heap,
                       trace ++ [.log msg], funcs, cs⟩) := by
  unfold Core.step?
  simp [Core.exprValue?, hargs, Core.consoleLogIdx, Core.pushTrace]
  cases argVals with | nil => rfl | cons hd tl => cases tl with | nil => rfl | cons _ _ => rfl

/-- Console.log message from converted values equals message from original values. -/
private theorem consoleLog_msg_convertValue (argVals : List Core.Value) :
    (match argVals.map Flat.convertValue with
      | [v] => Flat.valueToString v
      | vs => String.intercalate " " (vs.map Flat.valueToString)) =
    (match argVals with
      | [v] => Core.valueToString v
      | vs => String.intercalate " " (vs.map Core.valueToString)) := by
  cases argVals with
  | nil => rfl
  | cons hd tl =>
    cases tl with
    | nil => simp [List.map, valueToString_convertValue]
    | cons hd2 tl2 =>
      simp only [List.map, valueToString_convertValue]
      congr 1
      induction tl2 with
      | nil => rfl
      | cons h t ih => simp [List.map, valueToString_convertValue, ih]

/-- Core consoleLog step stated with Flat message form (for simulation).
    Unlike Core_step?_call_consoleLog_general, the msg uses Flat.valueToString
    on converted values, matching the Flat step's event form. -/
private theorem Core_step?_call_consoleLog_flat_msg (args : List Core.Expr) (argVals : List Core.Value)
    (env : Core.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Core.FuncClosure) (cs : List (List (Core.VarName × Core.Value)))
    (hargs : Core.allValues args = some argVals) :
    Core.step? ⟨.call (.lit (.function Core.consoleLogIdx)) args, env, heap, trace, funcs, cs⟩ =
      some (.log (match argVals.map Flat.convertValue with
        | [v] => Flat.valueToString v
        | vs => String.intercalate " " (vs.map Flat.valueToString)),
       ⟨.lit .undefined, env, heap,
        trace ++ [.log (match argVals.map Flat.convertValue with
          | [v] => Flat.valueToString v
          | vs => String.intercalate " " (vs.map Flat.valueToString))],
        funcs, cs⟩) := by
  unfold Core.step?
  simp [Core.exprValue?, hargs, Core.consoleLogIdx, Core.pushTrace, consoleLog_msg_convertValue argVals]
  cases argVals with | nil => rfl | cons hd tl => cases tl with | nil => rfl | cons _ _ => rfl

private theorem Core_step?_call_func_step (s : Core.State) (args : List Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .call e args } =
      some (t, { expr := .call sa.expr args, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_seq_value (s : Flat.State) (fv : Flat.Value) (b : Flat.Expr) :
    Flat.step? { s with expr := .seq (.lit fv) b } =
      some (.silent,
        { expr := b, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Flat_step?_let_value (s : Flat.State) (name : String) (fv : Flat.Value) (body : Flat.Expr) :
    Flat.step? { s with expr := .«let» name (.lit fv) body } =
      some (.silent,
        { expr := body, env := Flat.Env.extend s.env name fv, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

private theorem Flat_step?_seq_step (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .seq fe b } =
      some (t, { expr := .seq sa.expr b, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss, hnv]
  split <;> simp_all [Flat.exprValue?]

-- Flat_step?_seq_error: removed (unused after by_cases restructuring; had parse issues)

private theorem Core_step?_seq_step (s : Core.State) (b : Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .seq e b } =
      some (t, { expr := .seq sa.expr b, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_let_step (s : Flat.State) (name : String) (body : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .«let» name fe body } =
      some (t, { expr := .«let» name sa.expr body, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss, hnv]
  split <;> simp_all [Flat.exprValue?]

private theorem Flat_step?_let_error (s : Flat.State) (name : String) (body : Flat.Expr)
    (fe : Flat.Expr) (hnv : Flat.exprValue? fe = none) (msg : String) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (.error msg, sa)) :
    Flat.step? { s with expr := .«let» name fe body } =
      some (.error msg, { expr := sa.expr, env := sa.env, heap := sa.heap,
                          trace := s.trace ++ [.error msg], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hnv, hss, Flat.pushTrace]

private theorem Flat_step?_assign_error (s : Flat.State) (name : String)
    (fe : Flat.Expr) (hnv : Flat.exprValue? fe = none) (msg : String) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (.error msg, sa)) :
    Flat.step? { s with expr := .assign name fe } =
      some (.error msg, { expr := sa.expr, env := sa.env, heap := sa.heap,
                          trace := s.trace ++ [.error msg], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hnv, hss, Flat.pushTrace]

private theorem Flat_step?_seq_error (s : Flat.State) (b : Flat.Expr)
    (fe : Flat.Expr) (hnv : Flat.exprValue? fe = none) (msg : String) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (.error msg, sa)) :
    Flat.step? { s with expr := .seq fe b } =
      some (.error msg, { expr := sa.expr, env := sa.env, heap := sa.heap,
                          trace := s.trace ++ [.error msg], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hnv, hss, Flat.pushTrace]

private theorem Core_step?_let_step (s : Core.State) (name : String) (body : Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .«let» name e body } =
      some (t, { expr := .«let» name sa.expr body, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]



















private theorem Flat_step?_if_true (s : Flat.State) (fv : Flat.Value) (then_ else_ : Flat.Expr)
    (h : Flat.toBoolean fv = true) :
    Flat.step? { s with expr := .«if» (.lit fv) then_ else_ } =
      some (.silent,
        { expr := then_, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]

private theorem Flat_step?_if_false (s : Flat.State) (fv : Flat.Value) (then_ else_ : Flat.Expr)
    (h : Flat.toBoolean fv = false) :
    Flat.step? { s with expr := .«if» (.lit fv) then_ else_ } =
      some (.silent,
        { expr := else_, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h]

private theorem Flat_step?_if_step (s : Flat.State) (then_ else_ : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .«if» fe then_ else_ } =
      some (t, { expr := .«if» sa.expr then_ else_, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

private theorem Core_step?_if_step (s : Core.State) (then_ else_ : Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .«if» e then_ else_ } =
      some (t, { expr := .«if» sa.expr then_ else_, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_binary_lhs_step (s : Flat.State) (op : Core.BinOp) (rhs : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .binary op fe rhs } =
      some (t, { expr := .binary op sa.expr rhs, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases fe with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]

private theorem Core_step?_binary_lhs_step (s : Core.State) (op : Core.BinOp) (rhs : Core.Expr) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .binary op e rhs } =
      some (t, { expr := .binary op sa.expr rhs, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_binary_rhs_step (s : Flat.State) (op : Core.BinOp) (lv : Flat.Value) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .binary op (.lit lv) fe } =
      some (t, { expr := .binary op (.lit lv) sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  have hlv : Flat.exprValue? (.lit lv) = some lv := rfl
  simp only [Flat.step?, hlv, hnv, hss]; rfl

private theorem Core_step?_binary_rhs_step (s : Core.State) (op : Core.BinOp) (lv : Core.Value) (e : Core.Expr)
    (hnv : Core.exprValue? e = none)
    (t : Core.TraceEvent) (sa : Core.State)
    (hss : Core.step? { s with expr := e } = some (t, sa)) :
    Core.step? { s with expr := .binary op (.lit lv) e } =
      some (t, { expr := .binary op (.lit lv) sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := sa.funcs, callStack := sa.callStack }) := by
  simp [Core.step?, hnv, hss, Core.pushTrace]

private theorem Flat_step?_binary_values (s : Flat.State) (op : Core.BinOp) (lv rv : Flat.Value) :
    Flat.step? { s with expr := .binary op (.lit lv) (.lit rv) } =
      some (.silent, { expr := .lit (Flat.evalBinary op lv rv), env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

private theorem Flat_step?_objectLit_step (s : Flat.State)
    (props : List (Flat.PropName × Flat.Expr))
    (done : List (Flat.PropName × Flat.Expr)) (propName : Flat.PropName)
    (target : Flat.Expr) (rest : List (Flat.PropName × Flat.Expr))
    (hvals : Flat.valuesFromExprList? (props.map Prod.snd) = none)
    (hfnvp : Flat.firstNonValueProp props = some (done, propName, target, rest))
    (t : Core.TraceEvent) (se : Flat.State)
    (hss : Flat.step? { s with expr := target } = some (t, se)) :
    Flat.step? { s with expr := .objectLit props } =
      some (t, { expr := .objectLit (done ++ [(propName, se.expr)] ++ rest),
                 env := se.env, heap := se.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  unfold Flat.step?
  simp only [hvals]
  split
  · next done' propName' target' rest' hf =>
    have heq := hfnvp ▸ hf
    simp [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    simp only [hss]
    simp [Flat.step?_pushTrace_expand]
  · next hf =>
    simp [hfnvp] at hf

private theorem Flat_step?_objectLit_none (s : Flat.State)
    (props : List (Flat.PropName × Flat.Expr))
    (done : List (Flat.PropName × Flat.Expr)) (propName : Flat.PropName)
    (target : Flat.Expr) (rest : List (Flat.PropName × Flat.Expr))
    (hvals : Flat.valuesFromExprList? (props.map Prod.snd) = none)
    (hfnvp : Flat.firstNonValueProp props = some (done, propName, target, rest))
    (hss : Flat.step? { s with expr := target } = none) :
    Flat.step? { s with expr := .objectLit props } = none := by
  unfold Flat.step?
  simp only [hvals]
  split
  · next done' propName' target' rest' hf =>
    have heq := hfnvp ▸ hf
    simp [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    simp only [hss]
  · next hf =>
    simp [hfnvp] at hf


private theorem Flat_step?_arrayLit_step (s : Flat.State)
    (elems : List Flat.Expr)
    (done : List Flat.Expr) (target : Flat.Expr) (rest : List Flat.Expr)
    (hvals : Flat.valuesFromExprList? elems = none)
    (hfnve : Flat.firstNonValueExpr elems = some (done, target, rest))
    (t : Core.TraceEvent) (se : Flat.State)
    (hss : Flat.step? { s with expr := target } = some (t, se)) :
    Flat.step? { s with expr := .arrayLit elems } =
      some (t, { expr := .arrayLit (done ++ [se.expr] ++ rest),
                 env := se.env, heap := se.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  unfold Flat.step?
  simp only [hvals]
  split
  · next done' target' rest' hf =>
    have heq := hfnve ▸ hf
    simp [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [hss]
    simp [Flat.step?_pushTrace_expand]
  · next hf =>
    simp [hfnve] at hf

private theorem Flat_step?_arrayLit_none (s : Flat.State)
    (elems : List Flat.Expr)
    (done : List Flat.Expr) (target : Flat.Expr) (rest : List Flat.Expr)
    (hvals : Flat.valuesFromExprList? elems = none)
    (hfnve : Flat.firstNonValueExpr elems = some (done, target, rest))
    (hss : Flat.step? { s with expr := target } = none) :
    Flat.step? { s with expr := .arrayLit elems } = none := by
  unfold Flat.step?
  simp only [hvals]
  split
  · next done' target' rest' hf =>
    have heq := hfnve ▸ hf
    simp [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [hss]
  · next hf =>
    simp [hfnve] at hf



private theorem Core_step?_objectLit_step (s : Core.State)
    (props : List (Core.PropName × Core.Expr))
    (done : List (Core.PropName × Core.Expr)) (propName : Core.PropName)
    (target : Core.Expr) (rest : List (Core.PropName × Core.Expr))
    (hfnvp : Core.firstNonValueProp props = some (done, propName, target, rest))
    (t : Core.TraceEvent) (se : Core.State)
    (hss : Core.step? { s with expr := target } = some (t, se)) :
    Core.step? { s with expr := .objectLit props } =
      some (t, { expr := .objectLit (done ++ [(propName, se.expr)] ++ rest),
                 env := se.env, heap := se.heap,
                 trace := s.trace ++ [t], funcs := se.funcs, callStack := se.callStack }) := by
  unfold Core.step?
  split
  · next done' propName' target' rest' hf =>
    have heq := hfnvp ▸ hf
    simp [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    simp [hss, Core.pushTrace]
  · next hf =>
    simp [hfnvp] at hf

private theorem Core_step?_arrayLit_step (s : Core.State)
    (elems : List Core.Expr)
    (done : List Core.Expr) (target : Core.Expr) (rest : List Core.Expr)
    (hfnve : Core.firstNonValueExpr elems = some (done, target, rest))
    (t : Core.TraceEvent) (se : Core.State)
    (hss : Core.step? { s with expr := target } = some (t, se)) :
    Core.step? { s with expr := .arrayLit elems } =
      some (t, { expr := .arrayLit (done ++ [se.expr] ++ rest),
                 env := se.env, heap := se.heap,
                 trace := s.trace ++ [t], funcs := se.funcs, callStack := se.callStack }) := by
  unfold Core.step?
  split
  · next done' target' rest' hf =>
    have heq := hfnve ▸ hf
    simp [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp [hss, Core.pushTrace]
  · next hf =>
    simp [hfnve] at hf

private theorem Flat_step?_while (s : Flat.State) (cond body : Flat.Expr) :
    Flat.step? { s with expr := .while_ cond body } =
      some (.silent, { expr := .«if» cond (.seq body (.while_ cond body)) (.lit .undefined),
                       env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  unfold Flat.step?; simp [Flat.exprValue?]

private theorem Core_step?_while (s : Core.State) (cond body : Core.Expr) :
    Core.step? { s with expr := .while_ cond body } =
      some (.silent, { expr := .«if» cond (.seq body (.while_ cond body)) (.lit .undefined),
                       env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Core.step?, Core.pushTrace]

private theorem Flat_step?_tryCatch_body_value (s : Flat.State)
    (v : Flat.Value) (catchParam : String) (catchBody : Flat.Expr)
    (h_ncf : catchParam ≠ "__call_frame_return__") :
    Flat.step? { s with expr := .tryCatch (.lit v) catchParam catchBody none } =
      some (.silent, { expr := .lit v,
                       env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h_ncf]

private theorem Flat_step?_tryCatch_body_value_finally (s : Flat.State)
    (v : Flat.Value) (catchParam : String) (catchBody fin : Flat.Expr)
    (h_ncf : catchParam ≠ "__call_frame_return__") :
    Flat.step? { s with expr := .tryCatch (.lit v) catchParam catchBody (some fin) } =
      some (.silent, { expr := .seq fin (.lit v),
                       env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, h_ncf]

private theorem Flat_step?_tryCatch_body_step (s : Flat.State)
    (body : Flat.Expr) (catchParam : String) (catchBody : Flat.Expr)
    (finally_ : Option Flat.Expr) (sb : Flat.State) (t : Core.TraceEvent)
    (h_ncf : catchParam ≠ "__call_frame_return__")
    (hbnv : Flat.exprValue? body = none)
    (hstep : Flat.step? { s with expr := body } = some (t, sb))
    (hne : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .tryCatch body catchParam catchBody finally_ } =
      some (t, { expr := .tryCatch sb.expr catchParam catchBody finally_,
                 env := sb.env, heap := sb.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  unfold Flat.step?
  rw [show Flat.exprValue? body = none from hbnv]
  rw [hstep]
  cases t with
  | silent => rfl
  | log msg => rfl
  | error msg => exact absurd rfl (hne msg)

private theorem Flat_step?_tryCatch_body_error (s : Flat.State)
    (body : Flat.Expr) (catchParam : String) (catchBody : Flat.Expr)
    (finally_ : Option Flat.Expr) (sb : Flat.State) (msg : String)
    (h_ncf : catchParam ≠ "__call_frame_return__")
    (hbnv : Flat.exprValue? body = none)
    (hstep : Flat.step? { s with expr := body } = some (.error msg, sb)) :
    Flat.step? { s with expr := .tryCatch body catchParam catchBody finally_ } =
      some (.error msg,
        let handler := match finally_ with | some fin => Flat.Expr.seq catchBody fin | none => catchBody
        { expr := handler,
          env := Flat.Env.extend sb.env catchParam (.string msg),
          heap := sb.heap,
          trace := s.trace ++ [.error msg], funcs := s.funcs, callStack := s.callStack }) := by
  unfold Flat.step?
  rw [show Flat.exprValue? body = none from hbnv]
  rw [hstep]
  have : (catchParam == "__call_frame_return__") = false := by
    rw [beq_eq_false_iff_ne]; exact h_ncf
  simp [this]
  cases finally_ with
  | none => rfl
  | some fin => rfl

-- Helper: Flat getProp on object → heap property lookup
private theorem Flat_step?_getProp_object (s : Flat.State) (addr : Nat) (prop : Core.PropName) :
    Flat.step? { s with expr := .getProp (.lit (.object addr)) prop } =
      let v := match Flat.heapObjectAt? s.heap addr with
        | some props =>
            match props.find? (fun kv => kv.fst == prop) with
            | some (_, cv) => Flat.coreToFlatValue cv
            | none => if prop == "length" then Flat.Value.number (Float.ofNat props.length) else .undefined
        | none => Flat.Value.undefined
      some (.silent, { expr := .lit v, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

-- Helper: Flat getProp on string → length or undefined
private theorem Flat_step?_getProp_string (s : Flat.State) (str : String) (prop : Core.PropName) :
    Flat.step? { s with expr := .getProp (.lit (.string str)) prop } =
      some (.silent, { expr := .lit (if prop == "length" then .number (Float.ofNat str.length) else .undefined),
                       env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?]

-- Helper: getProp on a non-object non-string Flat value → .undefined
private theorem Flat_step?_getProp_primitive (s : Flat.State) (v : Flat.Value) (prop : Core.PropName)
    (hno : ∀ a, v ≠ .object a) (hns : ∀ str, v ≠ .string str) :
    Flat.step? { s with expr := .getProp (.lit v) prop } =
      some (.silent, { expr := .lit .undefined, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  cases v with
  | object a => exact absurd rfl (hno a)
  | string str => exact absurd rfl (hns str)
  | _ => simp [Flat.step?]

-- Helper: Core getProp on a non-object non-string Core value → .undefined
private theorem Core_step?_getProp_primitive (s : Core.State) (v : Core.Value) (prop : Core.PropName)
    (hno : ∀ a, v ≠ .object a) (hns : ∀ str, v ≠ .string str) :
    Core.step? { s with expr := .getProp (.lit v) prop } =
      some (.silent, { expr := .lit .undefined, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  cases v with
  | object a => exact absurd rfl (hno a)
  | string str => exact absurd rfl (hns str)
  | _ => simp [Core.step?, Core.exprValue?, Core.pushTrace]

-- Helper: convertValue of non-object non-string is non-object non-string
private theorem convertValue_not_object (v : Core.Value)
    (h : ∀ a, v ≠ .object a) : ∀ a, Flat.convertValue v ≠ .object a := by
  intro a; cases v <;> simp [Flat.convertValue] at * <;> exact h a rfl

private theorem convertValue_not_string (v : Core.Value)
    (h : ∀ s, v ≠ .string s) : ∀ s, Flat.convertValue v ≠ .string s := by
  intro s; cases v <;> simp [Flat.convertValue] at * <;> exact h s rfl

/-! ## Value sub-case step helpers -/

-- deleteProp: obj is .object addr (value case)
private theorem Flat_step?_deleteProp_object_value (s : Flat.State) (addr : Nat) (prop : Core.PropName) :
    Flat.step? { s with expr := .deleteProp (.lit (.object addr)) prop } =
      some (.silent,
        { expr := .lit (.bool true), env := s.env,
          heap := match Flat.heapObjectAt? s.heap addr with
            | some props =>
                { s.heap with objects := s.heap.objects.set! addr (props.filter (fun kv => kv.fst != prop)) }
            | none => s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

-- deleteProp: obj is non-object value
private theorem Flat_step?_deleteProp_nonobject_value (s : Flat.State) (v : Flat.Value) (prop : Core.PropName)
    (hobj : ∀ addr, v ≠ .object addr) :
    Flat.step? { s with expr := .deleteProp (.lit v) prop } =
      some (.silent,
        { expr := .lit (.bool true), env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | _ => simp only [Flat.step?, Flat.exprValue?]; rfl

-- setProp: obj is .object addr, value is a value → heap mutation
private theorem Flat_step?_setProp_object_both_values (s : Flat.State) (addr : Nat) (prop : Core.PropName)
    (v : Flat.Value) :
    Flat.step? { s with expr := .setProp (.lit (.object addr)) prop (.lit v) } =
      some (.silent,
        { expr := .lit v, env := s.env,
          heap := let cv := Flat.flatToCoreValue v
            match Flat.heapObjectAt? s.heap addr with
            | some props =>
                let updated := if props.any (fun kv => kv.fst == prop)
                  then props.map (fun kv => if kv.fst == prop then (prop, cv) else kv)
                  else props ++ [(prop, cv)]
                { s.heap with objects := s.heap.objects.set! addr updated }
            | none => s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

-- setProp: obj is non-object value, value is a value → return value, no heap change
private theorem Flat_step?_setProp_nonobject_both_values (s : Flat.State) (v : Flat.Value) (prop : Core.PropName)
    (vv : Flat.Value) (hobj : ∀ addr, v ≠ .object addr) :
    Flat.step? { s with expr := .setProp (.lit v) prop (.lit vv) } =
      some (.silent,
        { expr := .lit vv, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | _ => simp only [Flat.step?, Flat.exprValue?]; rfl

-- setProp: obj is value, value needs stepping (Flat)
private theorem Flat_step?_setProp_object_step_value (s : Flat.State) (addr : Nat) (prop : Core.PropName)
    (ve : Flat.Expr) (hnv : Flat.exprValue? ve = none)
    (t : Core.TraceEvent) (sv : Flat.State)
    (hss : Flat.step? { s with expr := ve } = some (t, sv)) :
    Flat.step? { s with expr := .setProp (.lit (.object addr)) prop ve } =
      some (t, { expr := .setProp (.lit (.object addr)) prop sv.expr, env := sv.env, heap := sv.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

-- setProp: obj is non-object value, value needs stepping (Flat)
private theorem Flat_step?_setProp_nonobject_step_value (s : Flat.State) (v : Flat.Value) (prop : Core.PropName)
    (ve : Flat.Expr) (hnv : Flat.exprValue? ve = none)
    (hobj : ∀ addr, v ≠ .object addr)
    (t : Core.TraceEvent) (sv : Flat.State)
    (hss : Flat.step? { s with expr := ve } = some (t, sv)) :
    Flat.step? { s with expr := .setProp (.lit v) prop ve } =
      some (t, { expr := .setProp (.lit v) prop sv.expr, env := sv.env, heap := sv.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | _ =>
    simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]


private theorem Flat_step?_setProp_value_none (s : Flat.State) (v : Flat.Value) (prop : Core.PropName)
    (ve : Flat.Expr) (hnv : Flat.exprValue? ve = none)
    (hss : Flat.step? { s with expr := ve } = none) :
    Flat.step? { s with expr := .setProp (.lit v) prop ve } = none := by
  simp only [Flat.step?, hnv, hss]
  cases v <;> simp [Flat.exprValue?]

-- Core: obj is value, value needs stepping (setProp)
private theorem Core_step?_setProp_value_step (cv : Core.Value) (prop : Core.PropName)
    (ve : Core.Expr) (hnv : Core.exprValue? ve = none)
    (env : Core.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Core.FuncClosure) (cs : List (List (Core.VarName × Core.Value)))
    (t : Core.TraceEvent) (sv : Core.State)
    (hss : Core.step? ⟨ve, env, heap, trace, funcs, cs⟩ = some (t, sv)) :
    Core.step? ⟨.setProp (.lit cv) prop ve, env, heap, trace, funcs, cs⟩ =
      some (t, { expr := .setProp (.lit cv) prop sv.expr, env := sv.env, heap := sv.heap,
                 trace := trace ++ [t], funcs := sv.funcs, callStack := sv.callStack }) := by
  cases ve with
  | lit v => simp [Core.exprValue?] at hnv
  | _ =>
    cases cv <;> simp only [Core.step?, Core.exprValue?, hss]
    all_goals simp [Core.pushTrace]

-- getIndex: obj is .object addr, idx needs stepping (Flat)
private theorem Flat_step?_getIndex_object_step_idx (s : Flat.State) (addr : Nat)
    (ie : Flat.Expr) (hnv : Flat.exprValue? ie = none)
    (t : Core.TraceEvent) (si : Flat.State)
    (hss : Flat.step? { s with expr := ie } = some (t, si)) :
    Flat.step? { s with expr := .getIndex (.lit (.object addr)) ie } =
      some (t, { expr := .getIndex (.lit (.object addr)) si.expr, env := si.env, heap := si.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

-- getIndex: obj is .string, idx needs stepping (Flat)
private theorem Flat_step?_getIndex_string_step_idx (s : Flat.State) (str : String)
    (ie : Flat.Expr) (hnv : Flat.exprValue? ie = none)
    (t : Core.TraceEvent) (si : Flat.State)
    (hss : Flat.step? { s with expr := ie } = some (t, si)) :
    Flat.step? { s with expr := .getIndex (.lit (.string str)) ie } =
      some (t, { expr := .getIndex (.lit (.string str)) si.expr, env := si.env, heap := si.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]

-- getIndex: obj is non-object non-string value, idx needs stepping (Flat)
private theorem Flat_step?_getIndex_other_step_idx (s : Flat.State) (v : Flat.Value)
    (ie : Flat.Expr) (hnv : Flat.exprValue? ie = none)
    (hobj : ∀ addr, v ≠ .object addr) (hstr : ∀ str, v ≠ .string str)
    (t : Core.TraceEvent) (si : Flat.State)
    (hss : Flat.step? { s with expr := ie } = some (t, si)) :
    Flat.step? { s with expr := .getIndex (.lit v) ie } =
      some (t, { expr := .getIndex (.lit v) si.expr, env := si.env, heap := si.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | string str => exact absurd rfl (hstr str)
  | _ =>
    simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]



private theorem Flat_step?_getIndex_value_none (s : Flat.State) (v : Flat.Value)
    (ie : Flat.Expr) (hnv : Flat.exprValue? ie = none)
    (hss : Flat.step? { s with expr := ie } = none) :
    Flat.step? { s with expr := .getIndex (.lit v) ie } = none := by
  cases ie with
  | lit w => simp [Flat.exprValue?] at hnv
  | _ =>
    simp only [Flat.step?, Flat.exprValue?, hss]
    cases v <;> simp [Flat.exprValue?]

-- getIndex: non-object non-string obj, both values → .undefined (Flat)
private theorem Flat_step?_getIndex_other_both_values (s : Flat.State) (v : Flat.Value) (iv : Flat.Value)
    (hobj : ∀ addr, v ≠ .object addr) (hstr : ∀ str, v ≠ .string str) :
    Flat.step? { s with expr := .getIndex (.lit v) (.lit iv) } =
      some (.silent, { s with expr := .lit .undefined, trace := s.trace ++ [.silent] }) := by
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | string str => exact absurd rfl (hstr str)
  | _ => simp only [Flat.step?, Flat.exprValue?]; rfl

-- getIndex: obj is .object addr, both values → heap lookup (Flat)
private theorem Flat_step?_getIndex_object_both_values (s : Flat.State) (addr : Nat) (iv : Flat.Value) :
    Flat.step? { s with expr := .getIndex (.lit (.object addr)) (.lit iv) } =
      let propName := Flat.valueToString iv
      let v := match Flat.heapObjectAt? s.heap addr with
        | some props =>
            match props.find? (fun kv => kv.fst == propName) with
            | some (_, cv) => Flat.coreToFlatValue cv
            | none => if propName == "length" then .number (Float.ofNat props.length) else .undefined
        | none => .undefined
      some (.silent, { s with expr := .lit v, trace := s.trace ++ [.silent] }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

-- getIndex: obj is .string, both values → string indexing (Flat)
private theorem Flat_step?_getIndex_string_both_values (s : Flat.State) (str : String) (iv : Flat.Value) :
    Flat.step? { s with expr := .getIndex (.lit (.string str)) (.lit iv) } =
      let propName := Flat.valueToString iv
      let v := match iv with
        | .number n =>
            let idx := n.toUInt64.toNat
            if n >= 0.0 && n.toUInt64.toFloat == n && idx < str.length
            then .string (String.Pos.Raw.get str ⟨idx⟩ |>.toString)
            else if propName == "length" then .number (Float.ofNat str.length) else .undefined
        | _ => if propName == "length" then .number (Float.ofNat str.length) else .undefined
      some (.silent, { s with expr := .lit v, trace := s.trace ++ [.silent] }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

-- Core: obj is value, idx needs stepping (getIndex)
private theorem Core_step?_getIndex_value_step (cv : Core.Value)
    (ie : Core.Expr) (hnv : Core.exprValue? ie = none)
    (env : Core.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Core.FuncClosure) (cs : List (List (Core.VarName × Core.Value)))
    (t : Core.TraceEvent) (si : Core.State)
    (hss : Core.step? ⟨ie, env, heap, trace, funcs, cs⟩ = some (t, si)) :
    Core.step? ⟨.getIndex (.lit cv) ie, env, heap, trace, funcs, cs⟩ =
      some (t, { expr := .getIndex (.lit cv) si.expr, env := si.env, heap := si.heap,
                 trace := trace ++ [t], funcs := si.funcs, callStack := si.callStack }) := by
  cases ie with
  | lit v => simp [Core.exprValue?] at hnv
  | _ =>
    cases cv <;> simp only [Core.step?, Core.exprValue?, hss]
    all_goals simp [Core.pushTrace]

-- Core: getIndex on string with both values: string character access
private theorem Core_step?_getIndex_string_val (str : String) (idxVal : Core.Value)
    (env : Core.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Core.FuncClosure) (cs : List (List (Core.VarName × Core.Value))) :
    let propName := Core.valueToString idxVal
    let v := match idxVal with
      | .number n =>
          let idx := n.toUInt64.toNat
          if n >= 0.0 && n.toUInt64.toFloat == n && idx < str.length
          then Core.Value.string (String.Pos.Raw.get str ⟨idx⟩ |>.toString)
          else .undefined
      | _ => if propName == "length" then .number (Float.ofNat str.length) else .undefined
    Core.step? ⟨.getIndex (.lit (.string str)) (.lit idxVal), env, heap, trace, funcs, cs⟩ =
      some (.silent, Core.pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  cases idxVal <;> simp [Core.step?, Core.exprValue?, Core.pushTrace]

/-! ## setIndex helper lemmas (value sub-cases) -/

-- setIndex: obj is object, idx needs stepping
private theorem Flat_step?_setIndex_object_step_idx (s : Flat.State) (addr : Nat)
    (ie value : Flat.Expr) (hnv : Flat.exprValue? ie = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := ie } = some (t, sa)) :
    Flat.step? { s with expr := .setIndex (.lit (.object addr)) ie value } =
      some (t, { expr := .setIndex (.lit (.object addr)) sa.expr value, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases ie with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]

-- setIndex: obj is non-object value, idx needs stepping
private theorem Flat_step?_setIndex_nonobject_step_idx (s : Flat.State) (v : Flat.Value)
    (ie value : Flat.Expr) (hobj : ∀ addr, v ≠ .object addr)
    (hnv : Flat.exprValue? ie = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := ie } = some (t, sa)) :
    Flat.step? { s with expr := .setIndex (.lit v) ie value } =
      some (t, { expr := .setIndex (.lit v) sa.expr value, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases ie with | lit w => simp [Flat.exprValue?] at hnv | _ =>
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | _ => simp [Flat.step?, hss]

-- setIndex: obj is object, idx is value, value needs stepping
private theorem Flat_step?_setIndex_object_step_value (s : Flat.State) (addr : Nat)
    (iv : Flat.Value) (ve : Flat.Expr) (hnv : Flat.exprValue? ve = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := ve } = some (t, sa)) :
    Flat.step? { s with expr := .setIndex (.lit (.object addr)) (.lit iv) ve } =
      some (t, { expr := .setIndex (.lit (.object addr)) (.lit iv) sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases ve with | lit w => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]

-- setIndex: obj is non-object value, idx is value, value needs stepping
private theorem Flat_step?_setIndex_nonobject_step_value (s : Flat.State) (v iv : Flat.Value)
    (ve : Flat.Expr) (hobj : ∀ addr, v ≠ .object addr)
    (hnv : Flat.exprValue? ve = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := ve } = some (t, sa)) :
    Flat.step? { s with expr := .setIndex (.lit v) (.lit iv) ve } =
      some (t, { expr := .setIndex (.lit v) (.lit iv) sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  cases ve with | lit w => simp [Flat.exprValue?] at hnv | _ =>
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | _ => simp [Flat.step?, hss]

-- setIndex: obj is object, all three values → heap mutation
private theorem Flat_step?_setIndex_object_both_values (s : Flat.State) (addr : Nat)
    (iv vv : Flat.Value) :
    Flat.step? { s with expr := .setIndex (.lit (.object addr)) (.lit iv) (.lit vv) } =
      let propName := Flat.valueToString iv
      let cv := Flat.flatToCoreValue vv
      let heap' := match Flat.heapObjectAt? s.heap addr with
        | some props =>
            let updated := if props.any (fun kv => kv.fst == propName)
              then props.map (fun kv => if kv.fst == propName then (propName, cv) else kv)
              else props ++ [(propName, cv)]
            { s.heap with objects := s.heap.objects.set! addr updated }
        | none => s.heap
      some (.silent, { s with expr := .lit vv, heap := heap', trace := s.trace ++ [.silent] }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

-- setIndex: obj is non-object, all three values → just return value
private theorem Flat_step?_setIndex_nonobject_both_values (s : Flat.State) (v iv vv : Flat.Value)
    (hobj : ∀ addr, v ≠ .object addr) :
    Flat.step? { s with expr := .setIndex (.lit v) (.lit iv) (.lit vv) } =
      some (.silent, { s with expr := .lit vv, trace := s.trace ++ [.silent] }) := by
  cases v with
  | object addr => exact absurd rfl (hobj addr)
  | _ => simp only [Flat.step?, Flat.exprValue?]; rfl

-- Core: setIndex with value obj, idx needs stepping
private theorem Core_step?_setIndex_value_step_idx (cv : Core.Value)
    (ie value : Core.Expr) (hnv : Core.exprValue? ie = none)
    (env : Core.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Core.FuncClosure) (cs : List (List (Core.VarName × Core.Value)))
    (t : Core.TraceEvent) (si : Core.State)
    (hss : Core.step? ⟨ie, env, heap, trace, funcs, cs⟩ = some (t, si)) :
    Core.step? ⟨.setIndex (.lit cv) ie value, env, heap, trace, funcs, cs⟩ =
      some (t, { expr := .setIndex (.lit cv) si.expr value, env := si.env, heap := si.heap,
                 trace := trace ++ [t], funcs := si.funcs, callStack := si.callStack }) := by
  cases ie with | lit v => simp [Core.exprValue?] at hnv | _ =>
  simp only [Core.step?, Core.exprValue?, hnv, hss]; simp [Core.pushTrace]

-- Core: setIndex with value obj+idx, value needs stepping
private theorem Core_step?_setIndex_value_step_value (cv iv : Core.Value)
    (ve : Core.Expr) (hnv : Core.exprValue? ve = none)
    (env : Core.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Core.FuncClosure) (cs : List (List (Core.VarName × Core.Value)))
    (t : Core.TraceEvent) (sv : Core.State)
    (hss : Core.step? ⟨ve, env, heap, trace, funcs, cs⟩ = some (t, sv)) :
    Core.step? ⟨.setIndex (.lit cv) (.lit iv) ve, env, heap, trace, funcs, cs⟩ =
      some (t, { expr := .setIndex (.lit cv) (.lit iv) sv.expr, env := sv.env, heap := sv.heap,
                 trace := trace ++ [t], funcs := sv.funcs, callStack := sv.callStack }) := by
  cases ve with | lit v => simp [Core.exprValue?] at hnv | _ =>
  unfold Core.step?
  have ho : Core.exprValue? (.lit cv) = some cv := rfl
  have hi : Core.exprValue? (.lit iv) = some iv := rfl
  rw [ho, hi, hnv]; simp [hss, Core.pushTrace]

-- setIndex: obj is value, idx needs stepping, but step? = none
private theorem Flat_step?_setIndex_value_idx_none (s : Flat.State) (v : Flat.Value)
    (ie value : Flat.Expr) (hnv : Flat.exprValue? ie = none)
    (hss : Flat.step? { s with expr := ie } = none) :
    Flat.step? { s with expr := .setIndex (.lit v) ie value } = none := by
  cases ie with
  | lit w => simp [Flat.exprValue?] at hnv
  | _ => cases v <;> simp [Flat.step?, Flat.exprValue?, hss]

-- setIndex: obj+idx are values, value needs stepping, but step? = none
private theorem Flat_step?_setIndex_value_value_none (s : Flat.State) (v iv : Flat.Value)
    (ve : Flat.Expr) (hnv : Flat.exprValue? ve = none)
    (hss : Flat.step? { s with expr := ve } = none) :
    Flat.step? { s with expr := .setIndex (.lit v) (.lit iv) ve } = none := by
  cases ve with
  | lit w => simp [Flat.exprValue?] at hnv
  | _ => cases v <;> simp [Flat.step?, Flat.exprValue?, hss]

/-! ## arrayLit helper lemmas -/

private theorem firstNonValueExpr_decompose {l : List Core.Expr} {done target rest}
    (h : Core.firstNonValueExpr l = some (done, target, rest)) :
    l = done ++ [target] ++ rest := by
  induction l generalizing done with
  | nil => simp [Core.firstNonValueExpr] at h
  | cons e es ih =>
    unfold Core.firstNonValueExpr at h
    split at h
    · -- e = .lit _
      match hrest : Core.firstNonValueExpr es with
      | some (d, t, r) =>
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have := ih hrest; simp [this]
      | none => simp [hrest] at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; simp

private theorem firstNonValueProp_decompose {l : List (Core.PropName × Core.Expr)} {done name target rest}
    (h : Core.firstNonValueProp l = some (done, name, target, rest)) :
    l = done ++ [(name, target)] ++ rest := by
  induction l generalizing done with
  | nil => simp [Core.firstNonValueProp] at h
  | cons p ps ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Core.firstNonValueProp at h
    split at h
    · -- pe = .lit _
      match hrest : Core.firstNonValueProp ps with
      | some (d, k, t, r) =>
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have := ih hrest; simp [this]
      | none => simp [hrest] at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp

/-- If firstNonValueExpr decomposes a list and all elements are supported,
    then done values are supported and rest is supported. -/
private theorem listSupported_firstNonValue_parts {es : List Core.Expr}
    {done target rest}
    (h : Core.firstNonValueExpr es = some (done, target, rest))
    (hsupp : Core.Expr.listSupported es = true) :
    Core.Expr.listSupported done = true ∧ Core.Expr.listSupported rest = true := by
  induction es generalizing done with
  | nil => simp [Core.firstNonValueExpr] at h
  | cons e es ih =>
    unfold Core.firstNonValueExpr at h
    split at h
    · -- e = .lit _
      match hrest : Core.firstNonValueExpr es with
      | some (d, t, r) =>
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [Core.Expr.listSupported, Bool.and_eq_true] at hsupp
        have ⟨hd_supp, hr_supp⟩ := ih hrest hsupp.2
        exact ⟨by simp [Core.Expr.listSupported, hsupp.1, hd_supp], hr_supp⟩
      | none => simp [hrest] at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [Core.Expr.listSupported, Bool.and_eq_true] at hsupp
      exact ⟨by simp [Core.Expr.listSupported], hsupp.2⟩

/-- Replacing the target with a supported expr preserves listSupported. -/
private theorem listSupported_replace_target {done rest : List Core.Expr}
    (e : Core.Expr) (hd_supp : Core.Expr.listSupported done = true)
    (he_supp : e.supported = true)
    (hr_supp : Core.Expr.listSupported rest = true) :
    Core.Expr.listSupported (done ++ [e] ++ rest) = true := by
  rw [listSupported_append, listSupported_append]
  simp [Bool.and_eq_true, Core.Expr.listSupported, hd_supp, he_supp, hr_supp]

/-- If firstNonValueProp decomposes a prop list and all elements are supported,
    then done values are supported and rest is supported. -/
private theorem propListSupported_firstNonValue_parts {ps : List (Core.PropName × Core.Expr)}
    {done name target rest}
    (h : Core.firstNonValueProp ps = some (done, name, target, rest))
    (hsupp : Core.Expr.propListSupported ps = true) :
    Core.Expr.propListSupported done = true ∧ Core.Expr.propListSupported rest = true := by
  induction ps generalizing done with
  | nil => simp [Core.firstNonValueProp] at h
  | cons p ps ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Core.firstNonValueProp at h
    split at h
    · -- pe = .lit _
      match hrest : Core.firstNonValueProp ps with
      | some (d, k, t, r) =>
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        simp [Core.Expr.propListSupported, Bool.and_eq_true] at hsupp
        have ⟨hd_supp, hr_supp⟩ := ih hrest hsupp.2
        exact ⟨by simp [Core.Expr.propListSupported, hsupp.1, hd_supp], hr_supp⟩
      | none => simp [hrest] at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp [Core.Expr.propListSupported, Bool.and_eq_true] at hsupp
      exact ⟨by simp [Core.Expr.propListSupported], hsupp.2⟩

/-- Replacing the target with a supported expr preserves propListSupported. -/
private theorem propListSupported_replace_target {done rest : List (Core.PropName × Core.Expr)}
    (name : Core.PropName) (e : Core.Expr)
    (hd_supp : Core.Expr.propListSupported done = true)
    (he_supp : e.supported = true)
    (hr_supp : Core.Expr.propListSupported rest = true) :
    Core.Expr.propListSupported (done ++ [(name, e)] ++ rest) = true := by
  rw [propListSupported_append, propListSupported_append]
  simp [Bool.and_eq_true, Core.Expr.propListSupported, hd_supp, he_supp, hr_supp]

private theorem listNoCallFrameReturn_append (a b : List Core.Expr) :
    listNoCallFrameReturn (a ++ b) = (listNoCallFrameReturn a && listNoCallFrameReturn b) := by
  induction a with
  | nil => simp [listNoCallFrameReturn]
  | cons hd tl ih => simp [listNoCallFrameReturn, ih, Bool.and_assoc]

private theorem firstNonValueExpr_listNoCallFrameReturn
    {elems : List Core.Expr} {done target rest}
    (hfnv : Core.firstNonValueExpr elems = some (done, target, rest))
    (hncfr : listNoCallFrameReturn elems = true) :
    listNoCallFrameReturn done = true ∧ noCallFrameReturn target = true ∧
    listNoCallFrameReturn rest = true := by
  induction elems generalizing done with
  | nil => simp [Core.firstNonValueExpr] at hfnv
  | cons e es ih =>
    simp [listNoCallFrameReturn] at hncfr
    unfold Core.firstNonValueExpr at hfnv
    split at hfnv
    · -- e = .lit v
      rename_i v
      match hrest : Core.firstNonValueExpr es with
      | some (d, t, r) =>
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at hfnv
        obtain ⟨rfl, rfl, rfl⟩ := hfnv
        have := ih hrest hncfr.2
        exact ⟨by simp [listNoCallFrameReturn, noCallFrameReturn]; exact this.1,
               this.2.1, this.2.2⟩
      | none => simp [hrest] at hfnv
    · -- e is not .lit
      simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
      obtain ⟨rfl, rfl, rfl⟩ := hfnv
      exact ⟨by simp [listNoCallFrameReturn], hncfr.1, hncfr.2⟩

private theorem convertExprList_firstNonValueExpr_some
    (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (done : List Core.Expr) (target : Core.Expr) (rest : List Core.Expr)
    (h : Core.firstNonValueExpr es = some (done, target, rest))
    (hnovalue : Core.exprValue? target = none)
    (hsupp : target.supported = true) :
    Flat.firstNonValueExpr (Flat.convertExprList es scope envVar envMap st).fst =
      some ((Flat.convertExprList done scope envVar envMap st).fst,
            (Flat.convertExpr target scope envVar envMap
              (Flat.convertExprList done scope envVar envMap st).snd).fst,
            (Flat.convertExprList rest scope envVar envMap
              (Flat.convertExpr target scope envVar envMap
                (Flat.convertExprList done scope envVar envMap st).snd).snd).fst) := by
  induction es generalizing done target rest st with
  | nil => simp [Core.firstNonValueExpr] at h
  | cons e es' ih =>
    unfold Core.firstNonValueExpr at h
    split at h
    · -- e = .lit v: Core skips this literal and recurses on es'
      rename_i v
      match hrest : Core.firstNonValueExpr es' with
      | some val =>
        obtain ⟨d', t', r'⟩ := val
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        -- LHS: convertExprList (.lit v :: es') starts with .lit (convertValue v), st unchanged
        have hlhs : (Flat.convertExprList (Core.Expr.lit v :: es') scope envVar envMap st).fst =
            .lit (Flat.convertValue v) :: (Flat.convertExprList es' scope envVar envMap st).fst := by
          simp [Flat.convertExprList, Flat.convertExpr]
        have hrhs1 : (Flat.convertExprList (Core.Expr.lit v :: d') scope envVar envMap st).fst =
            .lit (Flat.convertValue v) :: (Flat.convertExprList d' scope envVar envMap st).fst := by
          simp [Flat.convertExprList, Flat.convertExpr]
        have hrhs2 : (Flat.convertExprList (Core.Expr.lit v :: d') scope envVar envMap st).snd =
            (Flat.convertExprList d' scope envVar envMap st).snd := by
          simp [Flat.convertExprList, Flat.convertExpr]
        rw [hlhs, hrhs1, hrhs2]
        simp only [Flat.firstNonValueExpr, ih st d' t' r' hrest hnovalue hsupp]
      | none => simp [hrest] at h
    · -- e is not .lit: Core picks e as target, Flat also picks convertExpr e
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Flat.convertExprList]
      exact Flat_firstNonValueExpr_cons_not_value _ (convertExpr_not_value_supported e hnovalue hsupp scope envVar envMap st)

private theorem valuesFromExprList_none_of_firstNonValueExpr
    {elems : List Flat.Expr} {done target rest}
    (h : Flat.firstNonValueExpr elems = some (done, target, rest)) :
    Flat.valuesFromExprList? elems = none := by
  induction elems generalizing done target rest with
  | nil => simp [Flat.firstNonValueExpr] at h
  | cons e es ih =>
    cases e with
    | lit v =>
      unfold Flat.firstNonValueExpr at h
      simp only [] at h
      match hrest : Flat.firstNonValueExpr es with
      | some (d, t, r) =>
        have htail := ih hrest
        simp [Flat.valuesFromExprList?, Flat.exprValue?, htail]
      | none => rw [hrest] at h; simp at h
    | _ => simp [Flat.valuesFromExprList?, Flat.exprValue?]

/-- When Core.allValues returns some, the converted Flat args also have all values. -/
private theorem allValues_convertExprList_valuesFromExprList
    (args : List Core.Expr) (argVals : List Core.Value)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.allValues args = some argVals) :
    Flat.valuesFromExprList? (Flat.convertExprList args scope envVar envMap st).fst =
      some (argVals.map Flat.convertValue) := by
  induction args generalizing argVals st with
  | nil => simp [Core.allValues] at h; subst h; simp [Flat.convertExprList, Flat.valuesFromExprList?]
  | cons e rest ih =>
    cases e with
    | lit v =>
      simp [Core.allValues] at h
      match hrest : Core.allValues rest with
      | some vs =>
        simp [hrest] at h; subst h
        have hih := ih vs st hrest
        simp [Flat.convertExprList, Flat.convertExpr, Flat.valuesFromExprList?, Flat.exprValue?, hih]
      | none => simp [hrest] at h
    | _ => simp [Core.allValues] at h

/-- Converting a non-function Core.Value never produces a Flat.closure. -/
private theorem convertValue_not_closure_of_not_function (cv : Core.Value)
    (h : ∀ idx, cv ≠ .function idx) :
    ∀ fi ep, Flat.convertValue cv ≠ .closure fi ep := by
  cases cv with
  | function idx => exact absurd rfl (h idx)
  | _ => simp [Flat.convertValue]

/-- The Flat converted state does not change when Core.allValues args = some. -/
private theorem allValues_convertExprList_state
    (args : List Core.Expr) (argVals : List Core.Value)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.allValues args = some argVals) :
    (Flat.convertExprList args scope envVar envMap st).snd = st := by
  induction args generalizing argVals st with
  | nil => simp [Flat.convertExprList]
  | cons e rest ih =>
    cases e with
    | lit v =>
      simp [Core.allValues] at h
      match hrest : Core.allValues rest with
      | some vs =>
        simp [hrest] at h; subst h
        have hih := ih vs st hrest
        simp [Flat.convertExprList, Flat.convertExpr, hih]
      | none => simp [hrest] at h
    | _ => simp [Core.allValues] at h

private theorem convertExprList_append (a b : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertExprList (a ++ b) scope envVar envMap st).fst =
      (Flat.convertExprList a scope envVar envMap st).fst ++
      (Flat.convertExprList b scope envVar envMap (Flat.convertExprList a scope envVar envMap st).snd).fst := by
  induction a generalizing st with
  | nil => simp [Flat.convertExprList]
  | cons hd tl ih =>
    simp only [List.cons_append, Flat.convertExprList]
    exact congrArg ((Flat.convertExpr hd scope envVar envMap st).fst :: ·) (ih _)

private theorem convertExprList_append_snd (a b : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertExprList (a ++ b) scope envVar envMap st).snd =
      (Flat.convertExprList b scope envVar envMap (Flat.convertExprList a scope envVar envMap st).snd).snd := by
  induction a generalizing st with
  | nil => simp [Flat.convertExprList]
  | cons hd tl ih =>
    simp only [List.cons_append, Flat.convertExprList]
    exact ih _

private theorem propListNoCallFrameReturn_append (a b : List (Core.PropName × Core.Expr)) :
    propListNoCallFrameReturn (a ++ b) = (propListNoCallFrameReturn a && propListNoCallFrameReturn b) := by
  induction a with
  | nil => simp [propListNoCallFrameReturn]
  | cons hd tl ih =>
    simp only [List.cons_append, propListNoCallFrameReturn, ih, Bool.and_assoc]

private theorem firstNonValueProp_propListNoCallFrameReturn
    {props : List (Core.PropName × Core.Expr)} {done name target rest}
    (hfnv : Core.firstNonValueProp props = some (done, name, target, rest))
    (hncfr : propListNoCallFrameReturn props = true) :
    propListNoCallFrameReturn done = true ∧ noCallFrameReturn target = true ∧
    propListNoCallFrameReturn rest = true := by
  induction props generalizing done with
  | nil => simp [Core.firstNonValueProp] at hfnv
  | cons p ps ih =>
    obtain ⟨pn, pe⟩ := p
    simp [propListNoCallFrameReturn] at hncfr
    unfold Core.firstNonValueProp at hfnv
    split at hfnv
    · -- pe = .lit v
      rename_i v
      match hrest : Core.firstNonValueProp ps with
      | some (d, n, t, r) =>
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at hfnv
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hfnv
        have := ih hrest hncfr.2
        exact ⟨by simp [propListNoCallFrameReturn, noCallFrameReturn]; exact this.1,
               this.2.1, this.2.2⟩
      | none => simp [hrest] at hfnv
    · -- pe is not .lit
      simp only [Option.some.injEq, Prod.mk.injEq] at hfnv
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfnv
      exact ⟨by simp [propListNoCallFrameReturn], hncfr.1, hncfr.2⟩

private theorem valuesFromExprList_none_of_firstNonValueProp
    {props : List (Flat.PropName × Flat.Expr)} {done name target rest}
    (h : Flat.firstNonValueProp props = some (done, name, target, rest)) :
    Flat.valuesFromExprList? (props.map Prod.snd) = none := by
  induction props generalizing done name target rest with
  | nil => simp [Flat.firstNonValueProp] at h
  | cons p ps ih =>
    obtain ⟨pn, pe⟩ := p
    cases pe with
    | lit v =>
      unfold Flat.firstNonValueProp at h
      simp only [] at h
      match hrest : Flat.firstNonValueProp ps with
      | some (d, n, t, r) =>
        have htail := ih hrest
        simp [List.map, Flat.valuesFromExprList?, Flat.exprValue?, htail]
      | none => rw [hrest] at h; simp at h
    | _ => simp [List.map, Flat.valuesFromExprList?, Flat.exprValue?]

/-- When all Core props are values (firstNonValueProp = none), convertPropList preserves CCState. -/
private theorem convertPropList_state_none
    (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.firstNonValueProp ps = none) :
    (Flat.convertPropList ps scope envVar envMap st).snd = st := by
  induction ps generalizing st with
  | nil => simp [Flat.convertPropList]
  | cons p ps' ih =>
    obtain ⟨pn, pe⟩ := p
    cases pe with
    | lit v =>
      unfold Core.firstNonValueProp at h
      cases hrest : Core.firstNonValueProp ps' with
      | some _ => simp [hrest] at h
      | none =>
        simp [Flat.convertPropList, Flat.convertExpr]
        exact ih st hrest
    | _ => simp [Core.firstNonValueProp] at h

/-- When all Core elems are values (firstNonValueExpr = none), convertExprList preserves CCState. -/
private theorem convertExprList_state_none
    (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.firstNonValueExpr es = none) :
    (Flat.convertExprList es scope envVar envMap st).snd = st := by
  induction es generalizing st with
  | nil => simp [Flat.convertExprList]
  | cons e es' ih =>
    cases e with
    | lit v =>
      unfold Core.firstNonValueExpr at h
      cases hrest : Core.firstNonValueExpr es' with
      | some _ => simp [hrest] at h
      | none =>
        simp [Flat.convertExprList, Flat.convertExpr]
        exact ih st hrest
    | _ => simp [Core.firstNonValueExpr] at h

/-- When all Core elements are values, the converted Flat list also has no non-value. -/
private theorem convertExprList_firstNonValueExpr_none
    (es : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.firstNonValueExpr es = none) :
    Flat.firstNonValueExpr (Flat.convertExprList es scope envVar envMap st).fst = none := by
  induction es generalizing st with
  | nil => simp [Flat.convertExprList, Flat.firstNonValueExpr]
  | cons e es' ih =>
    cases e with
    | lit v =>
      unfold Core.firstNonValueExpr at h
      cases hrest : Core.firstNonValueExpr es' with
      | some _ => simp [hrest] at h
      | none =>
        have hcl : (Flat.convertExprList (Core.Expr.lit v :: es') scope envVar envMap st).fst =
            Flat.Expr.lit (Flat.convertValue v) :: (Flat.convertExprList es' scope envVar envMap st).fst := by
          simp [Flat.convertExprList, Flat.convertExpr]
        rw [hcl]; unfold Flat.firstNonValueExpr; simp [Flat.exprValue?, ih st hrest]
    | _ => simp [Core.firstNonValueExpr] at h

/-- When all Core elements are values, the zipIdx.filterMap on converted list equals mkIndexedProps. -/
private theorem convertExprList_zipIdx_filterMap_eq_mkIndexedProps
    (es : List Core.Expr) (startIdx : Nat)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.firstNonValueExpr es = none) :
    ((Flat.convertExprList es scope envVar envMap st).fst.zipIdx startIdx).filterMap
      (fun p => match Flat.exprValue? p.1 with | some v => some (toString p.2, Flat.flatToCoreValue v) | none => none) =
    Core.mkIndexedProps startIdx es := by
  induction es generalizing st startIdx with
  | nil => simp [Flat.convertExprList, Core.mkIndexedProps]
  | cons e es' ih =>
    cases e with
    | lit v =>
      unfold Core.firstNonValueExpr at h
      cases hrest : Core.firstNonValueExpr es' with
      | some _ => simp [hrest] at h
      | none =>
        have hcl : (Flat.convertExprList (Core.Expr.lit v :: es') scope envVar envMap st).fst =
            Flat.Expr.lit (Flat.convertValue v) :: (Flat.convertExprList es' scope envVar envMap st).fst := by
          simp [Flat.convertExprList, Flat.convertExpr]
        rw [hcl]
        simp only [List.zipIdx_cons, List.filterMap_cons, Flat.exprValue?,
          flatToCoreValue_convertValue, Core.mkIndexedProps]
        exact congrArg _ (ih (startIdx + 1) st hrest)
    | _ => simp [Core.firstNonValueExpr] at h

private theorem convertPropList_firstNonValueProp_none
    (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.firstNonValueProp ps = none) :
    Flat.firstNonValueProp (Flat.convertPropList ps scope envVar envMap st).fst = none := by
  induction ps generalizing st with
  | nil => simp [Flat.convertPropList, Flat.firstNonValueProp]
  | cons p ps' ih =>
    obtain ⟨pn, pe⟩ := p
    cases pe with
    | lit v =>
      unfold Core.firstNonValueProp at h
      cases hrest : Core.firstNonValueProp ps' with
      | some _ => simp [hrest] at h
      | none =>
        have : (Flat.convertPropList ((pn, Core.Expr.lit v) :: ps') scope envVar envMap st).fst =
            (pn, Flat.Expr.lit (Flat.convertValue v)) :: (Flat.convertPropList ps' scope envVar envMap st).fst := by
          simp [Flat.convertPropList, Flat.convertExpr]
        rw [this]; unfold Flat.firstNonValueProp; simp [Flat.exprValue?, ih st hrest]
    | _ => simp [Core.firstNonValueProp] at h

/-- When all Core props are values, the filterMap results match through conversion. -/
private theorem convertPropList_filterMap_eq
    (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (h : Core.firstNonValueProp ps = none) :
    ((Flat.convertPropList ps scope envVar envMap st).fst.filterMap fun (k, e) =>
      match Flat.exprValue? e with | some v => some (k, Flat.flatToCoreValue v) | none => none) =
    (ps.filterMap fun (k, e) =>
      match Core.exprValue? e with | some v => some (k, v) | none => none) := by
  induction ps generalizing st with
  | nil => simp [Flat.convertPropList]
  | cons p ps' ih =>
    obtain ⟨pn, pe⟩ := p
    cases pe with
    | lit v =>
      unfold Core.firstNonValueProp at h
      cases hrest : Core.firstNonValueProp ps' with
      | some _ => simp [hrest] at h
      | none =>
        have : (Flat.convertPropList ((pn, Core.Expr.lit v) :: ps') scope envVar envMap st).fst =
            (pn, Flat.Expr.lit (Flat.convertValue v)) :: (Flat.convertPropList ps' scope envVar envMap st).fst := by
          simp [Flat.convertPropList, Flat.convertExpr]
        rw [this]
        simp only [List.filterMap, Flat.exprValue?, Core.exprValue?, flatToCoreValue_convertValue]
        exact congrArg _ (ih st hrest)
    | _ => simp [Core.firstNonValueProp] at h

private theorem convertPropList_firstNonValueProp_some
    (ps : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState)
    (done : List (Core.PropName × Core.Expr)) (name : Core.PropName) (target : Core.Expr)
    (rest : List (Core.PropName × Core.Expr))
    (h : Core.firstNonValueProp ps = some (done, name, target, rest))
    (hnovalue : Core.exprValue? target = none)
    (hsupp : target.supported = true) :
    Flat.firstNonValueProp (Flat.convertPropList ps scope envVar envMap st).fst =
      some ((Flat.convertPropList done scope envVar envMap st).fst,
            name,
            (Flat.convertExpr target scope envVar envMap
              (Flat.convertPropList done scope envVar envMap st).snd).fst,
            (Flat.convertPropList rest scope envVar envMap
              (Flat.convertExpr target scope envVar envMap
                (Flat.convertPropList done scope envVar envMap st).snd).snd).fst) := by
  induction ps generalizing done name target rest st with
  | nil => simp [Core.firstNonValueProp] at h
  | cons p ps' ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Core.firstNonValueProp at h
    split at h
    · -- pe = .lit v: Core skips this literal property and recurses
      rename_i v
      match hrest : Core.firstNonValueProp ps' with
      | some val =>
        obtain ⟨d', n', t', r'⟩ := val
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have hlhs : (Flat.convertPropList ((pn, Core.Expr.lit v) :: ps') scope envVar envMap st).fst =
            (pn, .lit (Flat.convertValue v)) :: (Flat.convertPropList ps' scope envVar envMap st).fst := by
          simp [Flat.convertPropList, Flat.convertExpr]
        have hrhs1 : (Flat.convertPropList ((pn, Core.Expr.lit v) :: d') scope envVar envMap st).fst =
            (pn, .lit (Flat.convertValue v)) :: (Flat.convertPropList d' scope envVar envMap st).fst := by
          simp [Flat.convertPropList, Flat.convertExpr]
        have hrhs2 : (Flat.convertPropList ((pn, Core.Expr.lit v) :: d') scope envVar envMap st).snd =
            (Flat.convertPropList d' scope envVar envMap st).snd := by
          simp [Flat.convertPropList, Flat.convertExpr]
        rw [hlhs, hrhs1, hrhs2]
        simp only [Flat.firstNonValueProp, ih st d' n' t' r' hrest hnovalue hsupp]
      | none => simp [hrest] at h
    · -- pe is not .lit: Core picks pe as target
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp only [Flat.convertPropList]
      exact Flat_firstNonValueProp_cons_not_value _ _ (convertExpr_not_value_supported pe hnovalue hsupp scope envVar envMap st)

private theorem convertPropList_append (a b : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertPropList (a ++ b) scope envVar envMap st).fst =
      (Flat.convertPropList a scope envVar envMap st).fst ++
      (Flat.convertPropList b scope envVar envMap (Flat.convertPropList a scope envVar envMap st).snd).fst := by
  induction a generalizing st with
  | nil => simp [Flat.convertPropList]
  | cons hd tl ih =>
    obtain ⟨pn, pe⟩ := hd
    simp only [List.cons_append, Flat.convertPropList]
    exact congrArg ((pn, (Flat.convertExpr pe scope envVar envMap st).fst) :: ·) (ih _)

private theorem convertPropList_append_snd (a b : List (Core.PropName × Core.Expr))
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st : Flat.CCState) :
    (Flat.convertPropList (a ++ b) scope envVar envMap st).snd =
      (Flat.convertPropList b scope envVar envMap (Flat.convertPropList a scope envVar envMap st).snd).snd := by
  induction a generalizing st with
  | nil => simp [Flat.convertPropList]
  | cons hd tl ih =>
    obtain ⟨pn, pe⟩ := hd
    simp only [List.cons_append, Flat.convertPropList]
    exact ih _

private theorem tryCatch_body_depth_lt (body : Core.Expr) (cp : String) (cb : Core.Expr) (fin : Option Core.Expr) :
    body.depth < (Core.Expr.tryCatch body cp cb fin).depth := by
  cases fin <;> simp [Core.Expr.depth] <;> omega

private theorem state_with_expr_eq {s : Core.State} {e : Core.Expr} (h : s.expr = e) :
    s = { s with expr := e } := by cases s; subst h; rfl

set_option maxHeartbeats 8000000 in
private theorem Core_step_preserves_supported (s s' : Core.State) (ev : Core.TraceEvent)
    (hsupp : s.expr.supported = true)
    (hfuncs_supp : ∀ (i : Nat) (fd : Core.FuncClosure), s.funcs[i]? = some fd → fd.body.supported = true)
    (hstep : Core.step? s = some (ev, s')) :
    s'.expr.supported = true := by
  -- Prove by strong induction on expression depth (needed for sub-expression stepping cases)
  suffices ∀ (n : Nat) (s s' : Core.State) (ev : Core.TraceEvent),
      s.expr.depth ≤ n → s.expr.supported = true →
      (∀ (i : Nat) (fd : Core.FuncClosure), s.funcs[i]? = some fd → fd.body.supported = true) →
      Core.step? s = some (ev, s') →
      s'.expr.supported = true by
    exact this s.expr.depth s s' ev (Nat.le_refl _) hsupp hfuncs_supp hstep
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s s' ev hd hsupp hfuncs_supp hstep
  cases hexpr : s.expr with
  | lit v =>
    rw [state_with_expr_eq hexpr] at hstep; simp [Core.step?] at hstep
  | forIn => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | forOf => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | yield => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | await => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | var name =>
    rw [state_with_expr_eq hexpr] at hstep
    cases hlookup : Core.Env.lookup s.env name with
    | some v =>
      have h := Core_step?_var_found { s with expr := .var name } name v (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
    | none =>
      have h := Core_step?_var_not_found { s with expr := .var name } name (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
  | this =>
    rw [state_with_expr_eq hexpr] at hstep
    cases hlookup : Core.Env.lookup s.env "this" with
    | some v =>
      have h := Core_step?_this_found { s with expr := .this } v (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
    | none =>
      have h := Core_step?_this_not_found { s with expr := .this } (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
  | «break» label =>
    rw [state_with_expr_eq hexpr] at hstep
    have h := Core_step?_break { s with expr := .«break» label } label
    rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
  | «continue» label =>
    rw [state_with_expr_eq hexpr] at hstep
    have h := Core_step?_continue { s with expr := .«continue» label } label
    rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
  | «return» arg =>
    cases arg with
    | none =>
      rw [state_with_expr_eq hexpr] at hstep
      have h := Core_step?_return_none { s with expr := .«return» none }
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
    | some e =>
      rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
      rw [state_with_expr_eq hexpr] at hstep
      cases hval : Core.exprValue? e with
      | some v =>
        have hlit : e = .lit v := by cases e <;> simp [Core.exprValue?] at hval; subst hval; rfl
        subst hlit
        have h := Core_step?_return_some_lit { s with expr := .«return» (some (.lit v)) } v
        rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
      | none =>
        cases h_sub : Core.step? { s with expr := e } with
        | none => simp [Core.step?, hval, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_return_step_arg e s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          simp only [Core.pushTrace, Core.Expr.supported]
          exact ih e.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := e } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub
  | labeled lbl body =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    have h := Core_step?_labeled { s with expr := .labeled lbl body } lbl body
    rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
    exact hsupp
  | functionDef fname params body isAsync isGenerator =>
    rw [state_with_expr_eq hexpr] at hstep
    simp [Core.step?, Core.pushTrace] at hstep
    obtain ⟨-, rfl⟩ := hstep; rfl
  | while_ cond body =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    simp [Core.step?, Core.pushTrace] at hstep
    obtain ⟨-, rfl⟩ := hstep
    simp [Core.Expr.supported]; exact ⟨hsupp.1, hsupp.2, hsupp.1, hsupp.2⟩
  | newObj callee args =>
    rw [state_with_expr_eq hexpr] at hstep
    simp [Core.step?, Core.pushTrace] at hstep
    obtain ⟨-, rfl⟩ := hstep; rfl
  | «let» name init body =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? init with
    | some v =>
      have hlit : init = .lit v := by cases init <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep; exact hsupp.2
    | none =>
      cases h_sub : Core.step? { s with expr := init } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_let_step_init name init body s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨ih init.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := init } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub, hsupp.2⟩
  | assign name rhs =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? rhs with
    | some v =>
      have hlit : rhs = .lit v := by cases rhs <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep; rfl
    | none =>
      cases h_sub : Core.step? { s with expr := rhs } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_assign_step_rhs name rhs s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        exact ih rhs.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := rhs } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub
  | «if» cond then_ else_ =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? cond with
    | some v =>
      have hlit : cond = .lit v := by cases cond <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep
      simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp
      cases Core.toBoolean v <;> simp_all [Core.Expr.supported]
    | none =>
      cases h_sub : Core.step? { s with expr := cond } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_if_step_cond cond then_ else_ s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨⟨ih cond.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := cond } sa t (Nat.le_refl _) hsupp.1.1 hfuncs_supp h_sub, hsupp.1.2⟩, hsupp.2⟩
  | seq a b =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? a with
    | some v =>
      have hlit : a = .lit v := by cases a <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep; exact hsupp.2
    | none =>
      cases h_sub : Core.step? { s with expr := a } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_seq_nonvalue_lhs a b s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨ih a.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := a } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub, hsupp.2⟩
  | throw arg =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? arg with
    | some v =>
      have hlit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      have h := Core_step?_throw_lit { s with expr := .throw (.lit v) } v
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep; rfl
    | none =>
      cases h_sub : Core.step? { s with expr := arg } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_throw_step_arg arg s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        exact ih arg.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := arg } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub
  | typeof arg =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? arg with
    | some v =>
      have hlit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep; rfl
    | none =>
      cases h_sub : Core.step? { s with expr := arg } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_typeof_step_arg arg s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        exact ih arg.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := arg } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub
  | unary op arg =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? arg with
    | some v =>
      have hlit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep; rfl
    | none =>
      cases h_sub : Core.step? { s with expr := arg } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_unary_step_arg op arg s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        exact ih arg.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := arg } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub
  | binary op lhs rhs =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_l : Core.exprValue? lhs with
    | none =>
      cases h_sub : Core.step? { s with expr := lhs } with
      | none => simp [Core.step?, hval_l, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_binary_nonvalue_lhs op lhs rhs s.env s.heap s.trace s.funcs s.callStack hval_l t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨ih lhs.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := lhs } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub, hsupp.2⟩
    | some lv =>
      have hlit_l : lhs = .lit lv := by cases lhs <;> simp [Core.exprValue?] at hval_l; subst hval_l; rfl
      subst hlit_l
      cases hval_r : Core.exprValue? rhs with
      | some rv =>
        have hlit_r : rhs = .lit rv := by cases rhs <;> simp [Core.exprValue?] at hval_r; subst hval_r; rfl
        subst hlit_r
        simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
        obtain ⟨-, rfl⟩ := hstep; rfl
      | none =>
        cases h_sub : Core.step? { s with expr := rhs } with
        | none => simp [Core.step?, hval_r, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          simp [Core.step?, hval_r, h_sub, Core.pushTrace] at hstep
          obtain ⟨-, rfl⟩ := hstep
          simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
          exact ⟨trivial, ih rhs.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := rhs } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub⟩
  | deleteProp obj prop =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? obj with
    | some v =>
      have hlit : obj = .lit v := by cases obj <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      -- All value types produce .lit (.bool true) result
      cases v <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
        (try (obtain ⟨-, rfl⟩ := hstep; rfl)) <;>
        (try (split at hstep <;> (obtain ⟨-, rfl⟩ := hstep; rfl)))
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_deleteProp_step_obj obj prop s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub
  | getProp obj prop =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? obj with
    | some v =>
      have hlit : obj = .lit v := by cases obj <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      cases v <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
        (try (obtain ⟨-, rfl⟩ := hstep; rfl)) <;>
        (try (split at hstep <;> (try split at hstep) <;> (try split at hstep) <;>
          (obtain ⟨-, rfl⟩ := hstep; rfl)))
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_getProp_step_obj obj prop s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub
  | setProp obj prop value =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_o : Core.exprValue? obj with
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval_o, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_setProp_step_obj obj prop value s.env s.heap s.trace s.funcs s.callStack hval_o t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub, hsupp.2⟩
    | some ov =>
      have hlit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o; subst hval_o; rfl
      subst hlit
      cases hval_v : Core.exprValue? value with
      | none =>
        cases h_sub : Core.step? { s with expr := value } with
        | none => simp [Core.step?, hval_v, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_setProp_step_value ov prop value s.env s.heap s.trace s.funcs s.callStack hval_v t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
          exact ⟨trivial, ih value.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := value } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub⟩
      | some vv =>
        have hlit_v : value = .lit vv := by cases value <;> simp [Core.exprValue?] at hval_v; subst hval_v; rfl
        subst hlit_v
        cases ov <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
          (try (obtain ⟨-, rfl⟩ := hstep; rfl)) <;>
          (try (split at hstep <;> (try split at hstep) <;> (obtain ⟨-, rfl⟩ := hstep; rfl)))
  | getIndex obj idx =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_o : Core.exprValue? obj with
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval_o, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_getIndex_step_obj obj idx s.env s.heap s.trace s.funcs s.callStack hval_o t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub, hsupp.2⟩
    | some ov =>
      have hlit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o; subst hval_o; rfl
      subst hlit
      cases hval_i : Core.exprValue? idx with
      | none =>
        cases h_sub : Core.step? { s with expr := idx } with
        | none =>
          have hov : Core.exprValue? (.lit ov) = some ov := rfl
          simp [Core.step?, hov, hval_i, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_getIndex_step_idx ov idx s.env s.heap s.trace s.funcs s.callStack hval_i t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
          exact ⟨trivial, ih idx.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := idx } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub⟩
      | some iv =>
        have hlit_i : idx = .lit iv := by cases idx <;> simp [Core.exprValue?] at hval_i; subst hval_i; rfl
        subst hlit_i
        cases ov <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
          (try (obtain ⟨-, rfl⟩ := hstep; rfl)) <;>
          (try (split at hstep <;> (try split at hstep) <;> (obtain ⟨-, rfl⟩ := hstep; rfl)))
  | setIndex obj idx value =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_o : Core.exprValue? obj with
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval_o, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_setIndex_step_obj obj idx value s.env s.heap s.trace s.funcs s.callStack hval_o t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨⟨ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp.1.1 hfuncs_supp h_sub, hsupp.1.2⟩, hsupp.2⟩
    | some ov =>
      have hlit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o; subst hval_o; rfl
      subst hlit
      cases hval_i : Core.exprValue? idx with
      | none =>
        cases h_sub : Core.step? { s with expr := idx } with
        | none =>
          have hov : Core.exprValue? (.lit ov) = some ov := rfl
          simp [Core.step?, hov, hval_i, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_setIndex_step_idx ov idx value s.env s.heap s.trace s.funcs s.callStack hval_i t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
          exact ⟨⟨trivial, ih idx.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := idx } sa t (Nat.le_refl _) hsupp.1.2 hfuncs_supp h_sub⟩, hsupp.2⟩
      | some iv =>
        have hlit_i : idx = .lit iv := by cases idx <;> simp [Core.exprValue?] at hval_i; subst hval_i; rfl
        subst hlit_i
        cases hval_v : Core.exprValue? value with
        | none =>
          cases h_sub : Core.step? { s with expr := value } with
          | none =>
            have hov : Core.exprValue? (.lit ov) = some ov := rfl
            have hiv : Core.exprValue? (.lit iv) = some iv := rfl
            simp [Core.step?, hov, hiv, hval_v, h_sub] at hstep
          | some p =>
            obtain ⟨t, sa⟩ := p
            have hfwd := Core.step_setIndex_step_value ov iv value s.env s.heap s.trace s.funcs s.callStack hval_v t sa h_sub
            rw [hfwd] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨-, rfl⟩ := hstep
            simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
            exact ⟨⟨trivial, trivial⟩, ih value.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
              { s with expr := value } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub⟩
        | some vv =>
          have hlit_v : value = .lit vv := by cases value <;> simp [Core.exprValue?] at hval_v; subst hval_v; rfl
          subst hlit_v
          cases ov <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
            (try (obtain ⟨-, rfl⟩ := hstep; rfl)) <;>
            (try (split at hstep <;> (try split at hstep) <;> (obtain ⟨-, rfl⟩ := hstep; rfl)))
  | call callee args =>
    rw [hexpr] at hsupp; simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_c : Core.exprValue? callee with
    | none =>
      -- Callee is not a value: step the callee
      cases h_sub : Core.step? { s with expr := callee } with
      | none =>
        have := Core.step_call_callee_stuck callee args s.env s.heap s.trace s.funcs s.callStack hval_c h_sub
        rw [this] at hstep; exact absurd hstep (by simp)
      | some p =>
        obtain ⟨t, sc⟩ := p
        have hfwd := Core.step_call_step_callee callee args s.env s.heap s.trace s.funcs s.callStack hval_c t sc h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
        exact ⟨ih callee.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := callee } sc t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub, hsupp.2⟩
    | some cv =>
      have hlit_c : callee = .lit cv := by cases callee <;> simp [Core.exprValue?] at hval_c; subst hval_c; rfl
      subst hlit_c
      cases hallv : Core.allValues args with
      | some argVals =>
        -- All args are values, callee is a value
        cases cv with
        | function idx =>
          -- Function callee: case split on consoleLog vs non-consoleLog
          cases hcl : idx == Core.consoleLogIdx with
          | true =>
            -- consoleLog: idx = consoleLogIdx
            have hidx : idx = Core.consoleLogIdx := by
              simp [BEq.beq] at hcl; exact hcl
            subst hidx
            obtain ⟨msg, hfwd⟩ := Core.step_call_consoleLog args argVals s.env s.heap s.trace s.funcs s.callStack hallv
            rw [hfwd] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
          | false =>
            -- not consoleLog
            cases hfunc : s.funcs[idx]? with
            | some closure =>
              have hfwd := Core.step_call_func_closure idx args argVals s.env s.heap s.trace s.funcs s.callStack
                closure hallv hcl hfunc
              rw [hfwd] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨-, rfl⟩ := hstep
              simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
              -- closure.body.supported follows from the FuncsSupported invariant
              exact ⟨⟨hfuncs_supp idx closure hfunc, trivial⟩, trivial⟩
            | none =>
              have hfwd := Core.step_call_func_none idx args argVals s.env s.heap s.trace s.funcs s.callStack
                hallv hcl hfunc
              rw [hfwd] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
        | null =>
          have hfwd := Core.step_call_nonfunc_exact Core.Value.null args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
        | undefined =>
          have hfwd := Core.step_call_nonfunc_exact Core.Value.undefined args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
        | bool b =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.bool b) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
        | number n =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.number n) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
        | string str =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.string str) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
        | object addr =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.object addr) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep; simp [Core.pushTrace, Core.Expr.supported]
      | none =>
        -- Not all args are values: step first non-value arg
        cases hfnv : Core.firstNonValueExpr args with
        | none => exact (Core.allValues_firstNonValue_contra hallv hfnv).elim
        | some val =>
          obtain ⟨done, target, rest⟩ := val
          cases h_sub : Core.step? { s with expr := target } with
          | none =>
            have := Core.step_call_arg_stuck cv args s.env s.heap s.trace s.funcs s.callStack hallv done target rest hfnv h_sub
            rw [this] at hstep; exact absurd hstep (by simp)
          | some p =>
            obtain ⟨t, sa⟩ := p
            have hfwd := Core.step_call_step_arg cv args s.env s.heap s.trace s.funcs s.callStack hallv done target rest hfnv t sa h_sub
            rw [hfwd] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨-, rfl⟩ := hstep
            simp only [Core.pushTrace, Core.Expr.supported, Bool.and_eq_true]
            have htgt_supp := listSupported_firstNonValueExpr_target hfnv hsupp.2
            have ⟨hd_supp, hr_supp⟩ := listSupported_firstNonValue_parts hfnv hsupp.2
            have hsa_supp := ih target.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; have := Core.firstNonValueExpr_depth hfnv; omega)
              { s with expr := target } sa t (Nat.le_refl _) htgt_supp hfuncs_supp h_sub
            exact ⟨trivial, listSupported_replace_target sa.expr hd_supp hsa_supp hr_supp⟩
  | objectLit props =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hfnv : Core.firstNonValueProp props with
    | none =>
      -- All values: step allocates object on heap, result is .lit (trivially supported)
      exact Core.step_objectLit_allValues_result_supported props s.env s.heap s.trace s.funcs s.callStack hfnv ev s' hstep
    | some val =>
      obtain ⟨done, k, target, rest⟩ := val
      cases h_sub : Core.step? { s with expr := target } with
      | none =>
        have := Core.step_objectLit_prop_stuck props s.env s.heap s.trace s.funcs s.callStack done k target rest hfnv h_sub
        rw [this] at hstep; exact absurd hstep (by simp)
      | some p =>
        obtain ⟨t, se⟩ := p
        have hfwd := Core.step_objectLit_step_prop props s.env s.heap s.trace s.funcs s.callStack done k target rest hfnv t se h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        have htgt_supp := propListSupported_firstNonValueProp_target hfnv hsupp
        have ⟨hd_supp, hr_supp⟩ := propListSupported_firstNonValue_parts hfnv hsupp
        have hse_supp := ih target.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; have := Core.firstNonValueProp_depth hfnv; omega)
          { s with expr := target } se t (Nat.le_refl _) htgt_supp hfuncs_supp h_sub
        exact propListSupported_replace_target k se.expr hd_supp hse_supp hr_supp
  | arrayLit elems =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hfnv : Core.firstNonValueExpr elems with
    | none =>
      -- All values: step allocates array on heap, result is .lit (trivially supported)
      exact Core.step_arrayLit_allValues_result_supported elems s.env s.heap s.trace s.funcs s.callStack hfnv ev s' hstep
    | some val =>
      obtain ⟨done, target, rest⟩ := val
      cases h_sub : Core.step? { s with expr := target } with
      | none =>
        have := Core.step_arrayLit_elem_stuck elems s.env s.heap s.trace s.funcs s.callStack done target rest hfnv h_sub
        rw [this] at hstep; exact absurd hstep (by simp)
      | some p =>
        obtain ⟨t, se⟩ := p
        have hfwd := Core.step_arrayLit_step_elem elems s.env s.heap s.trace s.funcs s.callStack done target rest hfnv t se h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        simp only [Core.pushTrace, Core.Expr.supported]
        have htgt_supp := listSupported_firstNonValueExpr_target hfnv hsupp
        have ⟨hd_supp, hr_supp⟩ := listSupported_firstNonValue_parts hfnv hsupp
        have hse_supp := ih target.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; have := Core.firstNonValueExpr_depth hfnv; omega)
          { s with expr := target } se t (Nat.le_refl _) htgt_supp hfuncs_supp h_sub
        exact listSupported_replace_target se.expr hd_supp hse_supp hr_supp
  | tryCatch body catchParam catchBody finally_ =>
    rw [hexpr] at hsupp; unfold Core.Expr.supported at hsupp
    simp only [Bool.and_eq_true] at hsupp
    obtain ⟨⟨hsup_body, hsup_catch⟩, hsup_fin⟩ := hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_b : Core.exprValue? body with
    | some v =>
      have hstep' := hstep
      unfold Core.step? at hstep'
      simp only [hval_b] at hstep'
      split at hstep'
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
        obtain ⟨-, rfl⟩ := hstep'; simp [Core.pushTrace, Core.Expr.supported]
      · cases finally_ with
        | some fin =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
          obtain ⟨-, rfl⟩ := hstep'
          simp [Core.pushTrace, Core.Expr.supported, hsup_catch, hsup_fin]
        | none =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
          obtain ⟨-, rfl⟩ := hstep'; simp [Core.pushTrace, Core.Expr.supported]
    | none =>
      cases h_sub : Core.step? { s with expr := body } with
      | none =>
        exfalso; revert hstep; rw [state_with_expr_eq hexpr]; unfold Core.step?; simp [hval_b, h_sub]
      | some p =>
        obtain ⟨te, sb⟩ := p
        cases te with
        | error msg =>
          have hstep' := hstep
          unfold Core.step? at hstep'
          simp only [hval_b, h_sub] at hstep'
          split at hstep'
          · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
            obtain ⟨-, rfl⟩ := hstep'; simp [Core.pushTrace, Core.Expr.supported]
          · split at hstep'
            · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
              obtain ⟨-, rfl⟩ := hstep'; simp [Core.pushTrace, Core.Expr.supported]
            · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
              obtain ⟨-, rfl⟩ := hstep'
              cases finally_ with
              | some fin => simp [Core.pushTrace, Core.Expr.supported, hsup_catch, hsup_fin]
              | none => simp [Core.pushTrace, Core.Expr.supported, hsup_catch]
        | silent =>
          have hfwd := Core.step_tryCatch_step_body_silent body catchParam catchBody finally_ s.env s.heap s.trace s.funcs s.callStack hval_b sb h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          have hih := ih body.depth (by have hd' := hd; rw [hexpr] at hd'; cases finally_ <;> simp [Core.Expr.depth] at hd' <;> omega)
            { s with expr := body } sb .silent (Nat.le_refl _) hsup_body hfuncs_supp h_sub
          simp only [Core.pushTrace_expand]
          show Core.Expr.supported (.tryCatch sb.expr catchParam catchBody finally_) = true
          unfold Core.Expr.supported
          rw [hih, hsup_catch, hsup_fin]; rfl
        | log msg =>
          have hfwd := Core.step_tryCatch_step_body_log body catchParam catchBody finally_ s.env s.heap s.trace s.funcs s.callStack hval_b msg sb h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          have hih := ih body.depth (by have hd' := hd; rw [hexpr] at hd'; cases finally_ <;> simp [Core.Expr.depth] at hd' <;> omega)
            { s with expr := body } sb (.log msg) (Nat.le_refl _) hsup_body hfuncs_supp h_sub
          simp only [Core.pushTrace_expand]
          show Core.Expr.supported (.tryCatch sb.expr catchParam catchBody finally_) = true
          unfold Core.Expr.supported
          rw [hih, hsup_catch, hsup_fin]; rfl

set_option maxHeartbeats 8000000 in
private theorem Core_step_preserves_funcs_supported (s s' : Core.State) (ev : Core.TraceEvent)
    (hsupp : s.expr.supported = true)
    (hfuncs_supp : ∀ (i : Nat) (fd : Core.FuncClosure), s.funcs[i]? = some fd → fd.body.supported = true)
    (hstep : Core.step? s = some (ev, s')) :
    ∀ (i : Nat) (fd : Core.FuncClosure), s'.funcs[i]? = some fd → fd.body.supported = true := by
  suffices ∀ (n : Nat) (s s' : Core.State) (ev : Core.TraceEvent),
      s.expr.depth ≤ n → s.expr.supported = true →
      (∀ (i : Nat) (fd : Core.FuncClosure), s.funcs[i]? = some fd → fd.body.supported = true) →
      Core.step? s = some (ev, s') →
      ∀ (i : Nat) (fd : Core.FuncClosure), s'.funcs[i]? = some fd → fd.body.supported = true by
    exact this s.expr.depth s s' ev (Nat.le_refl _) hsupp hfuncs_supp hstep
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s s' ev hd hsupp hfuncs_supp hstep i fd hfd
  cases hexpr : s.expr with
  | lit v =>
    rw [state_with_expr_eq hexpr] at hstep; simp [Core.step?] at hstep
  | forIn => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | forOf => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | yield => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | await => rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
  | var name =>
    rw [state_with_expr_eq hexpr] at hstep
    cases hlookup : Core.Env.lookup s.env name with
    | some v =>
      have h := Core_step?_var_found { s with expr := .var name } name v (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      have h := Core_step?_var_not_found { s with expr := .var name } name (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
  | this =>
    rw [state_with_expr_eq hexpr] at hstep
    cases hlookup : Core.Env.lookup s.env "this" with
    | some v =>
      have h := Core_step?_this_found { s with expr := .this } v (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      have h := Core_step?_this_not_found { s with expr := .this } (by simp [hlookup])
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
  | «break» label =>
    rw [state_with_expr_eq hexpr] at hstep
    have h := Core_step?_break { s with expr := .«break» label } label
    rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
    exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
  | «continue» label =>
    rw [state_with_expr_eq hexpr] at hstep
    have h := Core_step?_continue { s with expr := .«continue» label } label
    rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
    exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
  | «return» arg =>
    cases arg with
    | none =>
      rw [state_with_expr_eq hexpr] at hstep
      have h := Core_step?_return_none { s with expr := .«return» none }
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | some e =>
      rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
      rw [state_with_expr_eq hexpr] at hstep
      cases hval : Core.exprValue? e with
      | some v =>
        have hlit : e = .lit v := by cases e <;> simp [Core.exprValue?] at hval; subst hval; rfl
        subst hlit
        have h := Core_step?_return_some_lit { s with expr := .«return» (some (.lit v)) } v
        rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
        exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
      | none =>
        cases h_sub : Core.step? { s with expr := e } with
        | none => simp [Core.step?, hval, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_return_step_arg e s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          exact ih e.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := e } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub i fd
            (by simpa [Core.pushTrace] using hfd)
  | labeled lbl body =>
    rw [state_with_expr_eq hexpr] at hstep
    have h := Core_step?_labeled { s with expr := .labeled lbl body } lbl body
    rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
    exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
  | functionDef fname params body isAsync isGenerator =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    simp [Core.step?, Core.pushTrace] at hstep
    obtain ⟨-, rfl⟩ := hstep
    simp only [Core.pushTrace] at hfd
    rw [Array.getElem?_push] at hfd
    split at hfd
    · simp only [Option.some.injEq] at hfd; subst hfd; exact hsupp
    · exact hfuncs_supp i fd hfd
  | while_ cond body =>
    rw [state_with_expr_eq hexpr] at hstep
    simp [Core.step?, Core.pushTrace] at hstep
    obtain ⟨-, rfl⟩ := hstep
    exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
  | newObj callee args =>
    rw [state_with_expr_eq hexpr] at hstep
    simp [Core.step?, Core.pushTrace] at hstep
    obtain ⟨-, rfl⟩ := hstep
    exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
  | «let» name init body =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? init with
    | some v =>
      have hlit : init = .lit v := by cases init <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := init } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_let_step_init name init body s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih init.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := init } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | assign name rhs =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? rhs with
    | some v =>
      have hlit : rhs = .lit v := by cases rhs <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := rhs } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_assign_step_rhs name rhs s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih rhs.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := rhs } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | «if» cond then_ else_ =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? cond with
    | some v =>
      have hlit : cond = .lit v := by cases cond <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := cond } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_if_step_cond cond then_ else_ s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih cond.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := cond } sa t (Nat.le_refl _) hsupp.1.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | seq a b =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? a with
    | some v =>
      have hlit : a = .lit v := by cases a <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := a } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_seq_nonvalue_lhs a b s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih a.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := a } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | throw arg =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? arg with
    | some v =>
      have hlit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      have h := Core_step?_throw_lit { s with expr := .throw (.lit v) } v
      rw [h] at hstep; injection hstep with hstep; obtain ⟨-, rfl⟩ := Prod.mk.inj hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := arg } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_throw_step_arg arg s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih arg.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := arg } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | typeof arg =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? arg with
    | some v =>
      have hlit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := arg } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_typeof_step_arg arg s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih arg.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := arg } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | unary op arg =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? arg with
    | some v =>
      have hlit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
      obtain ⟨-, rfl⟩ := hstep
      exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := arg } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_unary_step_arg op arg s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih arg.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := arg } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | binary op lhs rhs =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_l : Core.exprValue? lhs with
    | none =>
      cases h_sub : Core.step? { s with expr := lhs } with
      | none => simp [Core.step?, hval_l, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_binary_nonvalue_lhs op lhs rhs s.env s.heap s.trace s.funcs s.callStack hval_l t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih lhs.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := lhs } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
    | some lv =>
      have hlit_l : lhs = .lit lv := by cases lhs <;> simp [Core.exprValue?] at hval_l; subst hval_l; rfl
      subst hlit_l
      cases hval_r : Core.exprValue? rhs with
      | some rv =>
        have hlit_r : rhs = .lit rv := by cases rhs <;> simp [Core.exprValue?] at hval_r; subst hval_r; rfl
        subst hlit_r
        simp [Core.step?, Core.pushTrace, Core.exprValue?] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
      | none =>
        cases h_sub : Core.step? { s with expr := rhs } with
        | none => simp [Core.step?, hval_r, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          simp [Core.step?, hval_r, h_sub, Core.pushTrace] at hstep
          obtain ⟨-, rfl⟩ := hstep
          exact ih rhs.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := rhs } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub i fd
            (by simpa [Core.pushTrace] using hfd)
  | deleteProp obj prop =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? obj with
    | some v =>
      have hlit : obj = .lit v := by cases obj <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      cases v <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
        (try (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))) <;>
        (try (split at hstep <;> (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))))
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_deleteProp_step_obj obj prop s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | getProp obj prop =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval : Core.exprValue? obj with
    | some v =>
      have hlit : obj = .lit v := by cases obj <;> simp [Core.exprValue?] at hval; subst hval; rfl
      subst hlit
      cases v <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
        (try (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))) <;>
        (try (split at hstep <;> (try split at hstep) <;> (try split at hstep) <;>
          (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))))
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_getProp_step_obj obj prop s.env s.heap s.trace s.funcs s.callStack hval t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | setProp obj prop value =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_o : Core.exprValue? obj with
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval_o, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_setProp_step_obj obj prop value s.env s.heap s.trace s.funcs s.callStack hval_o t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
    | some ov =>
      have hlit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o; subst hval_o; rfl
      subst hlit
      cases hval_v : Core.exprValue? value with
      | none =>
        cases h_sub : Core.step? { s with expr := value } with
        | none => simp [Core.step?, hval_v, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_setProp_step_value ov prop value s.env s.heap s.trace s.funcs s.callStack hval_v t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          exact ih value.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := value } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub i fd
            (by simpa [Core.pushTrace] using hfd)
      | some vv =>
        have hlit_v : value = .lit vv := by cases value <;> simp [Core.exprValue?] at hval_v; subst hval_v; rfl
        subst hlit_v
        cases ov <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
          (try (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))) <;>
          (try (split at hstep <;> (try split at hstep) <;> (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))))
  | getIndex obj idx =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_o : Core.exprValue? obj with
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval_o, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_getIndex_step_obj obj idx s.env s.heap s.trace s.funcs s.callStack hval_o t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
    | some ov =>
      have hlit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o; subst hval_o; rfl
      subst hlit
      cases hval_i : Core.exprValue? idx with
      | none =>
        cases h_sub : Core.step? { s with expr := idx } with
        | none =>
          have hov : Core.exprValue? (.lit ov) = some ov := rfl
          simp [Core.step?, hov, hval_i, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_getIndex_step_idx ov idx s.env s.heap s.trace s.funcs s.callStack hval_i t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          exact ih idx.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := idx } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub i fd
            (by simpa [Core.pushTrace] using hfd)
      | some iv =>
        have hlit_i : idx = .lit iv := by cases idx <;> simp [Core.exprValue?] at hval_i; subst hval_i; rfl
        subst hlit_i
        cases ov <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
          (try (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))) <;>
          (try (split at hstep <;> (try split at hstep) <;> (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))))
  | setIndex obj idx value =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_o : Core.exprValue? obj with
    | none =>
      cases h_sub : Core.step? { s with expr := obj } with
      | none => simp [Core.step?, hval_o, h_sub] at hstep
      | some p =>
        obtain ⟨t, sa⟩ := p
        have hfwd := Core.step_setIndex_step_obj obj idx value s.env s.heap s.trace s.funcs s.callStack hval_o t sa h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih obj.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := obj } sa t (Nat.le_refl _) hsupp.1.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
    | some ov =>
      have hlit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o; subst hval_o; rfl
      subst hlit
      cases hval_i : Core.exprValue? idx with
      | none =>
        cases h_sub : Core.step? { s with expr := idx } with
        | none =>
          have hov : Core.exprValue? (.lit ov) = some ov := rfl
          simp [Core.step?, hov, hval_i, h_sub] at hstep
        | some p =>
          obtain ⟨t, sa⟩ := p
          have hfwd := Core.step_setIndex_step_idx ov idx value s.env s.heap s.trace s.funcs s.callStack hval_i t sa h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          exact ih idx.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
            { s with expr := idx } sa t (Nat.le_refl _) hsupp.1.2 hfuncs_supp h_sub i fd
            (by simpa [Core.pushTrace] using hfd)
      | some iv =>
        have hlit_i : idx = .lit iv := by cases idx <;> simp [Core.exprValue?] at hval_i; subst hval_i; rfl
        subst hlit_i
        cases hval_v : Core.exprValue? value with
        | none =>
          cases h_sub : Core.step? { s with expr := value } with
          | none =>
            have hov : Core.exprValue? (.lit ov) = some ov := rfl
            have hiv : Core.exprValue? (.lit iv) = some iv := rfl
            simp [Core.step?, hov, hiv, hval_v, h_sub] at hstep
          | some p =>
            obtain ⟨t, sa⟩ := p
            have hfwd := Core.step_setIndex_step_value ov iv value s.env s.heap s.trace s.funcs s.callStack hval_v t sa h_sub
            rw [hfwd] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨-, rfl⟩ := hstep
            exact ih value.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
              { s with expr := value } sa t (Nat.le_refl _) hsupp.2 hfuncs_supp h_sub i fd
              (by simpa [Core.pushTrace] using hfd)
        | some vv =>
          have hlit_v : value = .lit vv := by cases value <;> simp [Core.exprValue?] at hval_v; subst hval_v; rfl
          subst hlit_v
          cases ov <;> simp [Core.step?, Core.exprValue?, Core.pushTrace] at hstep <;>
            (try (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))) <;>
            (try (split at hstep <;> (try split at hstep) <;> (obtain ⟨-, rfl⟩ := hstep; exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd))))
  | call callee args =>
    rw [hexpr] at hsupp; simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_c : Core.exprValue? callee with
    | none =>
      cases h_sub : Core.step? { s with expr := callee } with
      | none =>
        have := Core.step_call_callee_stuck callee args s.env s.heap s.trace s.funcs s.callStack hval_c h_sub
        rw [this] at hstep; exact absurd hstep (by simp)
      | some p =>
        obtain ⟨t, sc⟩ := p
        have hfwd := Core.step_call_step_callee callee args s.env s.heap s.trace s.funcs s.callStack hval_c t sc h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        exact ih callee.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; omega)
          { s with expr := callee } sc t (Nat.le_refl _) hsupp.1 hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
    | some cv =>
      have hlit_c : callee = .lit cv := by cases callee <;> simp [Core.exprValue?] at hval_c; subst hval_c; rfl
      subst hlit_c
      cases hallv : Core.allValues args with
      | some argVals =>
        cases cv with
        | function idx =>
          cases hcl : idx == Core.consoleLogIdx with
          | true =>
            have hidx : idx = Core.consoleLogIdx := by
              simp [BEq.beq] at hcl; exact hcl
            subst hidx
            obtain ⟨msg, hfwd⟩ := Core.step_call_consoleLog args argVals s.env s.heap s.trace s.funcs s.callStack hallv
            rw [hfwd] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨-, rfl⟩ := hstep
            exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
          | false =>
            cases hfunc : s.funcs[idx]? with
            | some closure =>
              have hfwd := Core.step_call_func_closure idx args argVals s.env s.heap s.trace s.funcs s.callStack
                closure hallv hcl hfunc
              rw [hfwd] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨-, rfl⟩ := hstep
              exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
            | none =>
              have hfwd := Core.step_call_func_none idx args argVals s.env s.heap s.trace s.funcs s.callStack
                hallv hcl hfunc
              rw [hfwd] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨-, rfl⟩ := hstep
              exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
        | null =>
          have hfwd := Core.step_call_nonfunc_exact Core.Value.null args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
        | undefined =>
          have hfwd := Core.step_call_nonfunc_exact Core.Value.undefined args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
        | bool b =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.bool b) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
        | number n =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.number n) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
        | string str =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.string str) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
        | object addr =>
          have hfwd := Core.step_call_nonfunc_exact (Core.Value.object addr) args argVals s.env s.heap s.trace s.funcs s.callStack (fun idx h => Core.Value.noConfusion h) hallv
          rw [hfwd] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep; obtain ⟨-, rfl⟩ := hstep
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
      | none =>
        cases hfnv : Core.firstNonValueExpr args with
        | none => exact (Core.allValues_firstNonValue_contra hallv hfnv).elim
        | some val =>
          obtain ⟨done, target, rest⟩ := val
          cases h_sub : Core.step? { s with expr := target } with
          | none =>
            have := Core.step_call_arg_stuck cv args s.env s.heap s.trace s.funcs s.callStack hallv done target rest hfnv h_sub
            rw [this] at hstep; exact absurd hstep (by simp)
          | some p =>
            obtain ⟨t, sa⟩ := p
            have hfwd := Core.step_call_step_arg cv args s.env s.heap s.trace s.funcs s.callStack hallv done target rest hfnv t sa h_sub
            rw [hfwd] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨-, rfl⟩ := hstep
            have htgt_supp := listSupported_firstNonValueExpr_target hfnv hsupp.2
            exact ih target.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; have := Core.firstNonValueExpr_depth hfnv; omega)
              { s with expr := target } sa t (Nat.le_refl _) htgt_supp hfuncs_supp h_sub i fd
              (by simpa [Core.pushTrace] using hfd)
  | objectLit props =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hfnv : Core.firstNonValueProp props with
    | none =>
      -- All values: allocates object, preserves funcs
      have hstep' := hstep
      unfold Core.step? at hstep'
      split at hstep'
      · simp_all [Core.pushTrace]
      · simp [Core.pushTrace] at hstep'; obtain ⟨-, rfl⟩ := hstep'
        exact hfuncs_supp i fd hfd
    | some val =>
      obtain ⟨done, k, target, rest⟩ := val
      cases h_sub : Core.step? { s with expr := target } with
      | none =>
        have := Core.step_objectLit_prop_stuck props s.env s.heap s.trace s.funcs s.callStack done k target rest hfnv h_sub
        rw [this] at hstep; exact absurd hstep (by simp)
      | some p =>
        obtain ⟨t, se⟩ := p
        have hfwd := Core.step_objectLit_step_prop props s.env s.heap s.trace s.funcs s.callStack done k target rest hfnv t se h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        have htgt_supp := propListSupported_firstNonValueProp_target hfnv hsupp
        exact ih target.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; have := Core.firstNonValueProp_depth hfnv; omega)
          { s with expr := target } se t (Nat.le_refl _) htgt_supp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | arrayLit elems =>
    rw [hexpr] at hsupp; simp [Core.Expr.supported] at hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hfnv : Core.firstNonValueExpr elems with
    | none =>
      -- All values: allocates array, preserves funcs
      have hstep' := hstep
      unfold Core.step? at hstep'
      split at hstep'
      · simp_all [Core.pushTrace]
      · simp [Core.pushTrace] at hstep'; obtain ⟨-, rfl⟩ := hstep'
        exact hfuncs_supp i fd hfd
    | some val =>
      obtain ⟨done, target, rest⟩ := val
      cases h_sub : Core.step? { s with expr := target } with
      | none =>
        have := Core.step_arrayLit_elem_stuck elems s.env s.heap s.trace s.funcs s.callStack done target rest hfnv h_sub
        rw [this] at hstep; exact absurd hstep (by simp)
      | some p =>
        obtain ⟨t, se⟩ := p
        have hfwd := Core.step_arrayLit_step_elem elems s.env s.heap s.trace s.funcs s.callStack done target rest hfnv t se h_sub
        rw [hfwd] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨-, rfl⟩ := hstep
        have htgt_supp := listSupported_firstNonValueExpr_target hfnv hsupp
        exact ih target.depth (by rw [hexpr] at hd; simp [Core.Expr.depth] at hd; have := Core.firstNonValueExpr_depth hfnv; omega)
          { s with expr := target } se t (Nat.le_refl _) htgt_supp hfuncs_supp h_sub i fd
          (by simpa [Core.pushTrace] using hfd)
  | tryCatch body catchParam catchBody finally_ =>
    rw [hexpr] at hsupp; unfold Core.Expr.supported at hsupp
    simp only [Bool.and_eq_true] at hsupp
    obtain ⟨⟨hsup_body, _⟩, _⟩ := hsupp
    rw [state_with_expr_eq hexpr] at hstep
    cases hval_b : Core.exprValue? body with
    | some v =>
      have hstep' := hstep
      unfold Core.step? at hstep'
      simp only [hval_b] at hstep'
      split at hstep'
      · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
        obtain ⟨-, rfl⟩ := hstep'
        exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
      · cases finally_ with
        | some fin =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
          obtain ⟨-, rfl⟩ := hstep'
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
        | none =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
          obtain ⟨-, rfl⟩ := hstep'
          exact hfuncs_supp i fd (by simpa [Core.pushTrace] using hfd)
    | none =>
      cases h_sub : Core.step? { s with expr := body } with
      | none =>
        exfalso; revert hstep; rw [state_with_expr_eq hexpr]; unfold Core.step?; simp [hval_b, h_sub]
      | some p =>
        obtain ⟨te, sb⟩ := p
        have ih_body := ih body.depth
          (by have hd' := hd; rw [hexpr] at hd'; cases finally_ <;> simp [Core.Expr.depth] at hd' <;> omega)
          { s with expr := body } sb te (Nat.le_refl _) hsup_body hfuncs_supp h_sub
        cases te with
        | error msg =>
          have hstep' := hstep
          unfold Core.step? at hstep'
          simp only [hval_b, h_sub] at hstep'
          split at hstep'
          · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
            obtain ⟨-, rfl⟩ := hstep'
            exact ih_body i fd (by simpa [Core.pushTrace] using hfd)
          · split at hstep'
            · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
              obtain ⟨-, rfl⟩ := hstep'
              exact ih_body i fd (by simpa [Core.pushTrace] using hfd)
            · simp only [Option.some.injEq, Prod.mk.injEq] at hstep'
              obtain ⟨-, rfl⟩ := hstep'
              exact ih_body i fd (by simpa [Core.pushTrace] using hfd)
        | silent =>
          have hfwd := Core.step_tryCatch_step_body_silent body catchParam catchBody finally_ s.env s.heap s.trace s.funcs s.callStack hval_b sb h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          exact ih_body i fd (by simpa [Core.pushTrace] using hfd)
        | log msg =>
          have hfwd := Core.step_tryCatch_step_body_log body catchParam catchBody finally_ s.env s.heap s.trace s.funcs s.callStack hval_b msg sb h_sub
          rw [hfwd] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨-, rfl⟩ := hstep
          exact ih_body i fd (by simpa [Core.pushTrace] using hfd)

/-- Any Flat error step produces a .lit result expression. -/
set_option maxHeartbeats 1600000 in
private theorem Flat_step_error_isLit
    (sf sf' : Flat.State) (msg : String)
    (hstep : Flat.step? sf = some (.error msg, sf')) :
    ∃ v, sf'.expr = .lit v := by
  suffices hgen : ∀ (n : Nat) (e : Flat.Expr) (env : Flat.Env) (heap : Core.Heap)
      (trace : List Core.TraceEvent) (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
      (sf' : Flat.State) (msg' : String),
      e.depth ≤ n →
      Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (.error msg', sf') →
      ∃ v, sf'.expr = .lit v by
    cases sf with | mk e env heap trace funcs cs =>
    exact hgen e.depth e env heap trace funcs cs sf' msg (Nat.le_refl _) hstep
  intro n; induction n with
  | zero =>
    intro e env heap trace funcs cs sf' msg' hd hstep
    cases e with
    | lit => unfold Flat.step? at hstep; simp at hstep
    | var name =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | this =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | «break» =>
      unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | «continue» =>
      unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | «return» arg =>
      cases arg with
      | none =>
        unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
        obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
      | some => simp [Flat.Expr.depth] at hd; omega
    | yield arg d =>
      cases arg with
      | none => unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      | some => simp [Flat.Expr.depth] at hd; omega
    | seq _ _ | «let» _ _ _ | assign _ _ | «if» _ _ _
    | binary _ _ _ | unary _ _ | typeof _ | call _ _ _
    | newObj _ _ _ | getProp _ _ | setProp _ _ _ | getIndex _ _
    | setIndex _ _ _ | deleteProp _ _ | throw _
    | tryCatch _ _ _ _ | while_ _ _ | labeled _ _ | await _
    | getEnv _ _ | makeClosure _ _ | makeEnv _ | objectLit _ | arrayLit _ =>
      simp [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth] at hd; omega
  | succ n ih =>
    intro e env heap trace funcs cs sf' msg' hd hstep
    cases e with
    | lit => unfold Flat.step? at hstep; simp at hstep
    | var name =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | this =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | «break» =>
      unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | «continue» =>
      unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
    | «return» arg =>
      cases arg with
      | none =>
        unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
        obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
      | some v =>
        unfold Flat.step? at hstep; dsimp only [] at hstep
        split at hstep
        · simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
    | seq a b =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | «let» name init body =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | assign name rhs =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | «if» cond then_ else_ =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | unary op arg =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | binary op lhs rhs =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
      · split at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
        · simp at hstep
    | typeof arg =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | throw arg =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | yield arg d =>
      cases arg with
      | none => unfold Flat.step? at hstep; simp [Flat.pushTrace] at hstep
      | some v =>
        unfold Flat.step? at hstep; dsimp only [] at hstep
        split at hstep
        · simp [Flat.pushTrace] at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
    | await arg =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp [Flat.pushTrace] at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | getProp obj prop =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · simp at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | deleteProp obj prop =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | setProp obj prop val =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
      · split at hstep
        · simp at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
      · split at hstep
        · simp at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
    | getIndex obj idx =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
      · split at hstep
        · simp at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
      · split at hstep
        · simp at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
      · split at hstep
        · simp at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
    | setIndex obj idx val =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep <;>
        (try split at hstep) <;> (try split at hstep) <;>
        (try split at hstep) <;> (try split at hstep) <;>
        first
        | simp at hstep
        | (have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
           have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
           simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩)
    | getEnv envE idx =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | makeClosure funcIdx envE =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | call f envE args =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
      · split at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
        · split at hstep
          · simp at hstep
          · split at hstep
            · rename_i hfnv
              split at hstep
              · split at hstep
                · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
                  have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; have := Flat.firstNonValueExpr_depth hfnv; omega) hsub
                  simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
                · simp at hstep
              · simp at hstep
            · simp at hstep
    | newObj f envE args =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · split at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
      · split at hstep
        · split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
        · split at hstep
          · simp at hstep
          · split at hstep
            · rename_i hfnv
              split at hstep
              · split at hstep
                · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
                  have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; have := Flat.firstNonValueExpr_depth hfnv; omega) hsub
                  simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
                · simp at hstep
              · simp at hstep
            · simp at hstep
    | makeEnv values =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · rename_i hfnv
          split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; have := Flat.firstNonValueExpr_depth hfnv; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
        · simp at hstep
    | arrayLit elems =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · rename_i hfnv
          split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; have := Flat.firstNonValueExpr_depth hfnv; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
        · simp at hstep
    | objectLit props =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · rename_i hfnv
          split at hstep
          · split at hstep
            · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
              have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; have := Flat.firstNonValueProp_depth hfnv; omega) hsub
              simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
            · simp at hstep
          · simp at hstep
        · simp at hstep
    | tryCatch body catchParam catchBody fin =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · simp at hstep
      · split at hstep
        · split at hstep
          · simp at hstep
          · split at hstep
            · simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨_, rfl⟩
            · simp at hstep
        · split at hstep
          · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
            have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
          · simp at hstep
        · simp at hstep
    | while_ cond body =>
      unfold Flat.step? at hstep; simp at hstep
    | labeled name body =>
      unfold Flat.step? at hstep; dsimp only [] at hstep
      split at hstep
      · split at hstep
        · have hsub := ‹Flat.step? ⟨_, env, heap, trace, funcs, cs⟩ = some (Core.TraceEvent.error _, _)›
          have ⟨v, hv⟩ := ih _ env heap trace funcs cs _ _ (by simp [Flat.Expr.depth] at hd ⊢; omega) hsub
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ⟨v, hv⟩
        · simp at hstep
      · simp at hstep

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
      (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State)
      (scope : List String) (st st' : Flat.CCState),
      sc.expr.depth = n → sf.trace = sc.trace →
      HeapInj injMap sc.heap sf.heap → EnvCorrInj injMap sc.env sf.env →
      FuncsCorr injMap sc.funcs sf.funcs t.functions →
      EnvAddrWF sc.env sc.heap.objects.size →
      HeapValuesWF sc.heap →
      sc.heap.nextAddr = sc.heap.objects.size →
      noCallFrameReturn sc.expr = true →
      ExprAddrWF sc.expr sc.heap.objects.size →
      sc.expr.supported = true →
      (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st →
      Flat.Step sf ev sf' →
      ∃ (injMap' : Nat → Nat) (sc' : Core.State), Core.Step sc ev sc' ∧ sf'.trace = sc'.trace ∧
        HeapInj injMap' sc'.heap sf'.heap ∧ EnvCorrInj injMap' sc'.env sf'.env ∧
        EnvAddrWF sc'.env sc'.heap.objects.size ∧
        HeapValuesWF sc'.heap ∧
        sc'.heap.nextAddr = sc'.heap.objects.size ∧
        noCallFrameReturn sc'.expr = true ∧
        ExprAddrWF sc'.expr sc'.heap.objects.size ∧
        -- ARCHITECTURAL NOTE on CCStateAgree (equality) vs CCStateAgreeWeak (≤):
        --
        -- CCStateAgree (nextId = nextId, funcs.size = funcs.size) is required here because
        -- proved cases (let, seq, binary, assign, etc.) use `convertExpr_state_determined`,
        -- which shows that two convertExpr calls with equal initial state produce equal
        -- expressions. This equality on expressions is critical: different nextId values
        -- generate different fresh variable names, producing structurally different ASTs.
        --
        -- However, CCStateAgree is UNPROVABLE for branching constructs (if/while/tryCatch).
        -- For `if cond then_ else_`: after taking the then-branch, the post-state includes
        -- fresh vars from converting else_ (since convertExpr converts both branches),
        -- but the witness st_a' must match st' which went through both branches. The
        -- actual execution only traverses one branch, leaving a state gap equal to the
        -- unconverted branch's state consumption.
        --
        -- A correct fix would require either: (a) an expression equivalence relation that
        -- is insensitive to fresh variable renaming (α-equivalence on generated names), or
        -- (b) a two-phase conversion that separates name allocation from code generation.
        -- Both are significant architectural changes beyond the current proof framework.
        ((∃ (st_a st_a' : Flat.CCState),
          (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
          CCStateAgree st st_a ∧ CCStateAgree st' st_a') ∨
         (∃ (v : Flat.Value) (msg : String), sf'.expr = .lit v ∧ ev = .error msg)) ∧
        FuncsCorr injMap' sc'.funcs sf'.funcs t.functions by
    intro sf sc ev sf' hrel hstep
    obtain ⟨htrace, ⟨injMap, hinj, henv, hfuncCorr⟩, hncfr, hexprwf, henvwf, hheapvwf, hheapna, hsupp, hfuncs_supp, h_expr_rel⟩ := hrel
    -- CC_SimRel expression relation is now a disjunction
    cases h_expr_rel with
    | inr h_val =>
      -- Error disjunct: sf.expr = .lit v, so Flat.Step sf ev sf' is impossible
      obtain ⟨v, hv⟩ := h_val
      exfalso
      have : Flat.step? sf = none := by
        have hsf : sf = { sf with expr := .lit v } := by cases sf; simp_all
        rw [hsf]; simp [Flat.step?]
      obtain ⟨hstep_eq⟩ := hstep
      rw [this] at hstep_eq; exact absurd hstep_eq (by simp)
    | inl h_conv =>
      obtain ⟨scope, envVar, envMap, st, st', hconv⟩ := h_conv
      obtain ⟨injMap', sc', hcstep, htrace', hinj', henv', henvwf', hheapvwf', hheapna', hncfr', hexprwf', h_expr_or, hfuncCorr'⟩ :=
        this sc.expr.depth envVar envMap injMap sf sc ev sf' scope st st' rfl htrace hinj henv hfuncCorr henvwf hheapvwf hheapna hncfr hexprwf hsupp hconv hstep
      have hsupp' : sc'.expr.supported = true :=
        Core_step_preserves_supported _ _ _ hsupp hfuncs_supp (by obtain ⟨h⟩ := hcstep; exact h)
      have hfuncs_supp' : ∀ (i : Nat) (fd : Core.FuncClosure), sc'.funcs[i]? = some fd → fd.body.supported = true :=
        Core_step_preserves_funcs_supported _ _ _ hsupp hfuncs_supp (by obtain ⟨h⟩ := hcstep; exact h)
      -- Reconstruct CC_SimRel with the disjunction from suffices
      cases h_expr_or with
      | inl h_left =>
        obtain ⟨st_a, st_a', hconv', _, _⟩ := h_left
        exact ⟨sc', hcstep, htrace', ⟨injMap', hinj', henv', hfuncCorr'⟩, hncfr', hexprwf', henvwf', hheapvwf', hheapna', hsupp', hfuncs_supp', Or.inl ⟨scope, envVar, envMap, st_a, st_a', hconv'⟩⟩
      | inr h_right =>
        obtain ⟨v, _, hv, _⟩ := h_right
        exact ⟨sc', hcstep, htrace', ⟨injMap', hinj', henv', hfuncCorr'⟩, hncfr', hexprwf', henvwf', hheapvwf', hheapna', hsupp', hfuncs_supp', Or.inr ⟨v, hv⟩⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_depth =>
  intro envVar envMap injMap sf sc ev sf' scope st st' hd htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr hexprwf hsupp hconv ⟨hstep⟩
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
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    -- Case split on whether the variable is captured
    cases hlookupEnv : Flat.lookupEnv envMap name with
    | some idx =>
      -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
      simp [hlookupEnv] at hconv
      sorry -- BLOCKED: multi-step simulation gap (architectural).
            -- Flat .getEnv (.var envVar) idx takes 2 steps:
            --   step 1: envVar lookup → .getEnv (.lit envObj) idx
            --   step 2: heap access → .lit val
            -- Core .var name takes 1 step: env lookup → .lit value.
            -- The theorem requires 1-to-1 step correspondence (Flat.Step → Core.Step), but the
            -- intermediate Flat state .getEnv (.lit envObj) idx is not convertExpr of any Core expr.
            -- FIX: change simulation to many-to-one (Flat.Steps → Core.Step), or use stuttering
            -- simulation with a well-founded measure, or change convertExpr to avoid sub-expressions
            -- in .getEnv (requires envObj at compile time — not currently available).
    | none =>
      -- Non-captured variable: convertExpr gives .var name (same as Core)
      simp [hlookupEnv] at hconv
      obtain ⟨hfexpr, hst_eq⟩ := hconv
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
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · have hsc' : sc = { sc with expr := .var name } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_var_found _ _ _ hclookup
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF]; exact henvwf name cv hclookup
        · exact ⟨st, st, by simp [sc', Flat.convertExpr, hfvcv], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
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
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · have hsc' : sc = { sc with expr := .var name } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_var_not_found _ _ hclookup
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF, ValueAddrWF]
        · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «this» =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst_eq⟩ := hconv
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · have hsc' : sc = { sc with expr := .this } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_this_found _ _ hclookup
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF]; exact henvwf "this" cv hclookup
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, hfvcv], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · have hsc' : sc = { sc with expr := .this } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_this_not_found _ hclookup
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF, ValueAddrWF]
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «let» name init body =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    cases hcev : Core.exprValue? init with
    | some cv =>
      have hlit : init = .lit cv := by
        cases init <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hconv
      have hsf_eta : sf = { sf with expr := .«let» name (.lit (Flat.convertValue cv)) (Flat.convertExpr body (name :: scope) envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_let_value] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State :=
        ⟨body, Core.Env.extend sc.env name cv, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · show Core.step? sc = some (.silent, sc')
        have hsc' : sc = { sc with expr := .«let» name (.lit cv) body } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        simp [Core.step?, Core.exprValue?, Core.pushTrace, sc']
      · simp [sc', htrace]
      · exact hinj
      · exact EnvCorrInj_extend henvCorr name cv
      · exact EnvAddrWF_extend henvwf name cv (by simp [ExprAddrWF] at hexprwf; exact hexprwf.1)
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr
      · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2
      · have hscope := convertExpr_scope_irrelevant body scope (name :: scope) envVar envMap st
        exact ⟨st, (Flat.convertExpr body scope envVar envMap st).snd, by
          simp only [sc']; rw [hscope], ⟨rfl, rfl⟩, by
          rw [hconv.2, convertExpr_scope_irrelevant body (name :: scope) scope]; exact ⟨rfl, rfl⟩⟩
    | none =>
      have hsupp_init : init.supported = true := by simp [Core.Expr.supported, Bool.and_eq_true] at hsupp; exact hsupp.1
      have hfnv : Flat.exprValue? (Flat.convertExpr init scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported init hcev hsupp_init scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.let name (Flat.convertExpr init scope envVar envMap st).fst
          (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      match hm : Flat.step? { sf with expr := (Flat.convertExpr init scope envVar envMap st).fst } with
      | some (t, sa) =>
        by_cases herr : ∃ msg, t = .error msg
        · -- Error case: let-init evaluates to error.
          -- BLOCKED: Structural mismatch — Flat.step? drops the .let wrapper on error
          -- (sf'.expr = sa.expr) but Core.step? keeps it (sc'.expr = .let name sc_sub'.expr body).
          -- The simulation relation requires (sf'.expr, _) = convertExpr sc'.expr ..., which
          -- fails because convertExpr of .let produces .let but sf'.expr has no .let wrapper.
          obtain ⟨msg, rfl⟩ := herr
          -- Error case: Flat drops the .let wrapper; prove via error disjunct
          have heq := Flat_step?_let_error sf name
            (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst
            _ hfnv msg sa hm
          rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨hev_eq, hsf'_eq⟩ := hstep; subst hev_eq; subst hsf'_eq
          have hdepth : init.depth < n := by simp [Core.Expr.depth] at hd; omega
          have hncfr_init : noCallFrameReturn init = true := by
            simp [noCallFrameReturn] at hncfr; exact hncfr.1
          have hexprwf_init : ExprAddrWF init sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf.1
          have hsupp_init : init.supported = true := by simp [Core.Expr.supported, Bool.and_eq_true] at hsupp; exact hsupp.1
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', h_sub_expr_or, hfuncCorr_sub⟩ :=
            ih_depth init.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr init scope envVar envMap st).fst }
              { sc with expr := init }
              (.error msg) sa scope st (Flat.convertExpr init scope envVar envMap st).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_init hexprwf_init hsupp_init
              (by simp)
              ⟨hm⟩
          let sc' : Core.State :=
            ⟨.«let» name sc_sub'.expr body, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [.error msg], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · show Core.step? sc = some (.error msg, sc')
            have hsc' : sc = { sc with expr := .«let» name init body } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            exact Core_step?_let_step _ name _ _ hcev _ _ hcstep_sub
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
          · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf',
                ExprAddrWF_mono body (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) (Core_step_heap_size_mono hcstep_sub)⟩
          · -- Expression correspondence: use error disjunct (sf'.expr = sa.expr)
            cases h_sub_expr_or with
            | inr h_val =>
              obtain ⟨v, _, hv, _⟩ := h_val
              exact ⟨Or.inr ⟨v, msg, hv, rfl⟩, hfuncCorr_sub⟩
            | inl h_conv =>
              obtain ⟨st_a, st_a', hconv_sub, _, _⟩ := h_conv
              have h_sa_eq : sa.expr = (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst :=
                congrArg Prod.fst hconv_sub
              cases sc_sub'.expr with
              | lit cv =>
                simp [Flat.convertExpr] at h_sa_eq
                exact ⟨Or.inr ⟨Flat.convertValue cv, msg, h_sa_eq, rfl⟩, hfuncCorr_sub⟩
              | _ =>
                have ⟨v, hv⟩ := Flat_step_error_isLit _ _ _ hm
                exact ⟨Or.inr ⟨v, msg, hv, rfl⟩, hfuncCorr_sub⟩
        · -- Non-error case
          simp only [not_exists] at herr
          have hne : ∀ msg, t ≠ .error msg := herr
          have heq := Flat_step?_let_step sf name
            (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst
            _ hfnv t sa hm hne
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          have hsf'_eq := hsf'eq.symm; subst hsf'_eq
          have hdepth : init.depth < n := by simp [Core.Expr.depth] at hd; omega
          have hncfr_init : noCallFrameReturn init = true := by
            simp [noCallFrameReturn] at hncfr; exact hncfr.1
          have hexprwf_init : ExprAddrWF init sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf.1
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
            ih_depth init.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr init scope envVar envMap st).fst }
              { sc with expr := init }
              t sa scope st (Flat.convertExpr init scope envVar envMap st).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_init hexprwf_init hsupp_init
              (by simp)
              ⟨hm⟩
          let sc' : Core.State :=
            ⟨.«let» name sc_sub'.expr body, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [t], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · show Core.step? sc = some (t, sc')
            have hsc' : sc = { sc with expr := .«let» name init body } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            exact Core_step?_let_step _ name _ _ hcev _ _ hcstep_sub
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
          · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf',
                ExprAddrWF_mono body (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) (Core_step_heap_size_mono hcstep_sub)⟩
          · refine ⟨st_a, (Flat.convertExpr body (name :: scope) envVar envMap st_a').snd, ?_, hAgreeIn, ?_⟩
            · simp only [sc', Flat.convertExpr]
              have hbody := convertExpr_state_determined body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
              rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
              rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
              rw [hbody.1]
            · rw [hconv.2]
              exact (convertExpr_state_determined body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2).2
      | none =>
        have heq : Flat.step? { sf with expr := (Flat.Expr.let name (Flat.convertExpr init scope envVar envMap st).fst
            (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst) } = none := by
          simp only [Flat.step?, hfnv, hm]
        rw [heq] at hstep; exact absurd hstep (by simp)
  | assign name rhs =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? rhs with
    | some cv =>
      have hlit : rhs = .lit cv := by
        cases rhs <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr
      have hsf_eta : sf = { sf with expr := .assign name (.lit (Flat.convertValue cv)) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_assign_value] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State := ⟨.lit cv, sc.env.assign name cv, sc.heap,
        sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · have hsc' : sc = { sc with expr := .assign name (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; simp [Core.step?, Core.exprValue?, Core.pushTrace]; rfl
      · simp only [sc']; simp [htrace]
      · exact hinj
      · exact EnvCorrInj_assign henvCorr name cv
      · exact EnvAddrWF_assign henvwf name cv (by simp [ExprAddrWF] at hexprwf; exact hexprwf)
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp only [sc']; simp [noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF]; exact (by simp [ExprAddrWF] at hexprwf; exact hexprwf)
      · exact ⟨st, st, by simp only [sc']; simp [Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr rhs scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported rhs hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .assign name (Flat.convertExpr rhs scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      match hm : Flat.step? { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst } with
      | some (t, sa) =>
        by_cases herr : ∃ msg, t = .error msg
        · -- Error case: assign-rhs evaluates to error → error disjunct
          obtain ⟨msg, rfl⟩ := herr
          have heq := Flat_step?_assign_error sf name _ hfnv msg sa hm
          rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨hev_eq, hsf'_eq⟩ := hstep; subst hev_eq; subst hsf'_eq
          have hdepth : rhs.depth < n := by simp [Core.Expr.depth] at hd; omega
          have hncfr_rhs : noCallFrameReturn rhs = true := by
            simp [noCallFrameReturn] at hncfr; exact hncfr
          have hexprwf_rhs : ExprAddrWF rhs sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf
          have hsupp_rhs : rhs.supported = true := by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', h_sub_expr_or, hfuncCorr_sub⟩ :=
            ih_depth rhs.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst }
              { sc with expr := rhs }
              (.error msg) sa scope st (Flat.convertExpr rhs scope envVar envMap st).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_rhs hexprwf_rhs hsupp_rhs
              (by simp)
              ⟨hm⟩
          let sc' : Core.State :=
            ⟨.assign name sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [.error msg], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · show Core.step? sc = some (.error msg, sc')
            have hsc' : sc = { sc with expr := .assign name rhs } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            exact Core_step?_assign_step _ name _ hcev _ _ hcstep_sub
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · simp [sc', noCallFrameReturn]; exact hncfr'
          · simp only [sc']; simp only [ExprAddrWF]; exact hexprwf'
          · -- Expression correspondence: error disjunct
            cases h_sub_expr_or with
            | inr h_val =>
              obtain ⟨v, _, hv, _⟩ := h_val
              exact ⟨Or.inr ⟨v, msg, hv, rfl⟩, hfuncCorr_sub⟩
            | inl h_conv =>
              obtain ⟨st_a, st_a', hconv_sub, _, _⟩ := h_conv
              have h_sa_eq : sa.expr = (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst :=
                congrArg Prod.fst hconv_sub
              cases sc_sub'.expr with
              | lit cv =>
                simp [Flat.convertExpr] at h_sa_eq
                exact ⟨Or.inr ⟨Flat.convertValue cv, msg, h_sa_eq, rfl⟩, hfuncCorr_sub⟩
              | _ =>
                have ⟨v, hv⟩ := Flat_step_error_isLit _ _ _ hm
                exact ⟨Or.inr ⟨v, msg, hv, rfl⟩, hfuncCorr_sub⟩
        · -- Non-error case
          simp only [not_exists] at herr
          have hne : ∀ msg, t ≠ .error msg := herr
          have heq := Flat_step?_assign_step sf name _ hfnv t sa hm hne
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          have hsf'_eq := hsf'eq.symm; subst hsf'_eq
          have hdepth : rhs.depth < n := by simp [Core.Expr.depth] at hd; omega
          have hncfr_rhs : noCallFrameReturn rhs = true := by
            simp [noCallFrameReturn] at hncfr; exact hncfr
          have hexprwf_rhs : ExprAddrWF rhs sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
            ih_depth rhs.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst }
              { sc with expr := rhs }
              t sa scope st (Flat.convertExpr rhs scope envVar envMap st).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_rhs hexprwf_rhs (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
              (by simp)
              ⟨hm⟩
          let sc' : Core.State :=
            ⟨.assign name sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [t], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · show Core.step? sc = some (t, sc')
            have hsc' : sc = { sc with expr := .assign name rhs } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            exact Core_step?_assign_step _ name _ hcev _ _ hcstep_sub
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · simp [sc', noCallFrameReturn]; exact hncfr'
          · simp [sc', ExprAddrWF]; exact hexprwf'
          · exact ⟨st_a, st_a', by
              simp [sc', Flat.convertExpr]
              exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
      | none =>
        have heq : Flat.step? { sf with expr := .assign name (Flat.convertExpr rhs scope envVar envMap st).fst } = none := by
          simp only [Flat.step?, hfnv, hm]
        rw [heq] at hstep; exact absurd hstep (by simp)
  | «if» cond then_ else_ =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    cases hcev : Core.exprValue? cond with
    | some cv =>
      have hlit : cond = .lit cv := by
        cases cond <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hconv
      -- sf.expr = .if (.lit (convertValue cv)) then' else'
      have hsf_eta : sf = { sf with expr := (Flat.Expr.if (.lit (Flat.convertValue cv))
          (Flat.convertExpr then_ scope envVar envMap st).fst
          (Flat.convertExpr else_ scope envVar envMap (Flat.convertExpr then_ scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      cases htb : Core.toBoolean cv with
      | true =>
        rw [Flat_step?_if_true _ _ _ _ (by rw [toBoolean_convertValue, htb])] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State :=
          ⟨then_, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · show Core.step? sc = some (.silent, sc')
          have hsc' : sc = { sc with expr := .«if» (.lit cv) then_ else_ } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          simp [Core.step?, Core.exprValue?, Core.pushTrace, htb, sc']
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr.1
        · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2.1
        · exact ⟨st, (Flat.convertExpr then_ scope envVar envMap st).snd, by
            simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, sorry⟩ -- BLOCKED: CCStateAgree. st' includes else_ conversion state but
            -- st_a' = (convertExpr then_ ... st).snd. Would need convertExpr else_ to not change
            -- nextId/funcs.size, which fails when else_ contains functionDef nodes.
            -- FIX: Change invariant to CCStateAgreeWeak; then use convertExpr_state_mono else_.
      | false =>
        rw [Flat_step?_if_false _ _ _ _ (by rw [toBoolean_convertValue, htb])] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State :=
          ⟨else_, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · show Core.step? sc = some (.silent, sc')
          have hsc' : sc = { sc with expr := .«if» (.lit cv) then_ else_ } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          simp [Core.step?, Core.exprValue?, Core.pushTrace, htb, sc']
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr.2
        · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2.2
        · exact ⟨(Flat.convertExpr then_ scope envVar envMap st).snd,
            (Flat.convertExpr else_ scope envVar envMap (Flat.convertExpr then_ scope envVar envMap st).snd).snd, by
            simp [sc', Flat.convertExpr], sorry, by rw [hconv.2]; exact ⟨rfl, rfl⟩⟩
            -- BLOCKED: CCStateAgree. st_a must skip then_ conversion state to reach else_,
            -- but CCStateAgree st st_a requires equality which fails when then_ changes state.
            -- FIX: Change invariant to CCStateAgreeWeak; then use convertExpr_state_mono then_.
    | none =>
      have hsupp_cond : cond.supported = true := by
        have h := hsupp; unfold Core.Expr.supported at h; simp [Bool.and_eq_true] at h; exact h.1.1
      have hfnv : Flat.exprValue? (Flat.convertExpr cond scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported cond hcev hsupp_cond scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.if (Flat.convertExpr cond scope envVar envMap st).fst
          (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst
          (Flat.convertExpr else_ scope envVar envMap
            (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr cond scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .«if» sa.expr
                    (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst
                    (Flat.convertExpr else_ scope envVar envMap
                      (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr cond scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_if_step sf
            (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst
            (Flat.convertExpr else_ scope envVar envMap
              (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.if (Flat.convertExpr cond scope envVar envMap st).fst
              (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst
              (Flat.convertExpr else_ scope envVar envMap
                (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : cond.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_cond : noCallFrameReturn cond = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1.1
      have hexprwf_cond : ExprAddrWF cond sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth cond.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr cond scope envVar envMap st).fst }
          { sc with expr := cond }
          ev sa scope st (Flat.convertExpr cond scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_cond hexprwf_cond hsupp_cond
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.«if» sc_sub'.expr then_ else_, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .«if» cond then_ else_ } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_if_step _ _ _ _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact ⟨⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.1.2⟩, by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
      · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf',
            ExprAddrWF_mono then_ (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.1) (Core_step_heap_size_mono hcstep_sub),
            ExprAddrWF_mono else_ (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2) (Core_step_heap_size_mono hcstep_sub)⟩
      · have hthen := convertExpr_state_determined then_ scope envVar envMap
            (Flat.convertExpr cond scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
        have helse := convertExpr_state_determined else_ scope envVar envMap
            (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).snd
            (Flat.convertExpr then_ scope envVar envMap st_a').snd hthen.2.1 hthen.2.2
        refine ⟨st_a, (Flat.convertExpr else_ scope envVar envMap (Flat.convertExpr then_ scope envVar envMap st_a').snd).snd, ?_, hAgreeIn, ?_⟩
        · simp only [sc', Flat.convertExpr]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
          rw [hthen.1, helse.1]
        · rw [hconv.2]; exact helse.2
  | seq a b =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    cases hcev : Core.exprValue? a with
    | some cv =>
      have hlit : a = .lit cv := by
        cases a <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hconv
      have hsf_eta : sf = { sf with expr := .seq (.lit (Flat.convertValue cv)) (Flat.convertExpr b scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_seq_value] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State :=
        ⟨b, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · show Core.step? sc = some (.silent, sc')
        have hsc' : sc = { sc with expr := .seq (.lit cv) b } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        simp [Core.step?, Core.exprValue?, Core.pushTrace, sc']
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr
      · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2
      · exact ⟨st, (Flat.convertExpr b scope envVar envMap st).snd, by
          simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr a scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported a hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.seq (Flat.convertExpr a scope envVar envMap st).fst
          (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      match hm : Flat.step? { sf with expr := (Flat.convertExpr a scope envVar envMap st).fst } with
      | some (t, sa) =>
        by_cases herr : ∃ msg, t = .error msg
        · -- Error case: seq-first evaluates to error → error disjunct
          obtain ⟨msg, rfl⟩ := herr
          have heq := Flat_step?_seq_error sf
            (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst
            _ hfnv msg sa hm
          rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨hev_eq, hsf'_eq⟩ := hstep; subst hev_eq; subst hsf'_eq
          have hdepth : a.depth < n := by simp [Core.Expr.depth] at hd; omega
          have hncfr_a : noCallFrameReturn a = true := by
            simp [noCallFrameReturn] at hncfr; exact hncfr.1
          have hexprwf_a : ExprAddrWF a sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf.1
          have hsupp_a : a.supported = true := by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', h_sub_expr_or, hfuncCorr_sub⟩ :=
            ih_depth a.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr a scope envVar envMap st).fst }
              { sc with expr := a }
              (.error msg) sa scope st (Flat.convertExpr a scope envVar envMap st).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_a hexprwf_a hsupp_a
              (by simp)
              ⟨hm⟩
          let sc' : Core.State :=
            ⟨.seq sc_sub'.expr b, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [.error msg], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · show Core.step? sc = some (.error msg, sc')
            have hsc' : sc = { sc with expr := .seq a b } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            exact Core_step?_seq_step _ _ _ hcev _ _ hcstep_sub
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
          · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf',
                ExprAddrWF_mono b (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) (Core_step_heap_size_mono hcstep_sub)⟩
          · -- Expression correspondence: error disjunct
            cases h_sub_expr_or with
            | inr h_val =>
              obtain ⟨v, _, hv, _⟩ := h_val
              exact ⟨Or.inr ⟨v, msg, hv, rfl⟩, hfuncCorr_sub⟩
            | inl h_conv =>
              obtain ⟨st_a, st_a', hconv_sub, _, _⟩ := h_conv
              have h_sa_eq : sa.expr = (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst :=
                congrArg Prod.fst hconv_sub
              cases sc_sub'.expr with
              | lit cv =>
                simp [Flat.convertExpr] at h_sa_eq
                exact ⟨Or.inr ⟨Flat.convertValue cv, msg, h_sa_eq, rfl⟩, hfuncCorr_sub⟩
              | _ =>
                have ⟨v, hv⟩ := Flat_step_error_isLit _ _ _ hm
                exact ⟨Or.inr ⟨v, msg, hv, rfl⟩, hfuncCorr_sub⟩
        · -- Non-error case
          simp only [not_exists] at herr
          have hne : ∀ msg, t ≠ .error msg := herr
          have heq := Flat_step?_seq_step sf
            (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst
            _ hfnv t sa hm hne
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          have hsf'_eq := hsf'eq.symm; subst hsf'_eq
          have hdepth : a.depth < n := by simp [Core.Expr.depth] at hd; omega
          have hncfr_a : noCallFrameReturn a = true := by
            simp [noCallFrameReturn] at hncfr; exact hncfr.1
          have hexprwf_a : ExprAddrWF a sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf.1
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
            ih_depth a.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr a scope envVar envMap st).fst }
              { sc with expr := a }
              t sa scope st (Flat.convertExpr a scope envVar envMap st).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_a hexprwf_a (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
              (by simp)
              ⟨hm⟩
          let sc' : Core.State :=
            ⟨.seq sc_sub'.expr b, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [t], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · show Core.step? sc = some (t, sc')
            have hsc' : sc = { sc with expr := .seq a b } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            exact Core_step?_seq_step _ _ _ hcev _ _ hcstep_sub
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
          · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf',
                ExprAddrWF_mono b (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) (Core_step_heap_size_mono hcstep_sub)⟩
          · have hb := convertExpr_state_determined b scope envVar envMap
                (Flat.convertExpr a scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
            refine ⟨st_a, (Flat.convertExpr b scope envVar envMap st_a').snd, ?_, hAgreeIn, ?_⟩
            · simp only [sc', Flat.convertExpr]
              rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
              rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
              rw [hb.1]
            · rw [hconv.2]; exact hb.2
      | none =>
        have heq : Flat.step? { sf with expr := (Flat.Expr.seq (Flat.convertExpr a scope envVar envMap st).fst
            (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst) } = none := by
          simp only [Flat.step?, hfnv, hm]
        rw [heq] at hstep; exact absurd hstep (by simp)
  | unary op arg =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? arg with
    | some cv =>
      have hlit : arg = .lit cv := by
        cases arg <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr
      have hsf_eta : sf = { sf with expr := .unary op (.lit (Flat.convertValue cv)) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_unary_value] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State := ⟨.lit (Core.evalUnary op cv), sc.env, sc.heap,
        sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · have hsc' : sc = { sc with expr := .unary op (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; simp [Core.step?, Core.exprValue?, Core.pushTrace]; rfl
      · simp only [sc']; simp [htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp only [sc']; simp [noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF]; exact evalUnary_valueAddrWF op cv sc.heap.objects.size (by simp [ExprAddrWF] at hexprwf; exact hexprwf)
      · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
        show (Flat.Expr.lit (Flat.evalUnary op (Flat.convertValue cv)), st) = Flat.convertExpr (.lit (Core.evalUnary op cv)) scope envVar envMap st
        rw [evalUnary_convertValue]; simp [Flat.convertExpr]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr arg scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported arg hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .unary op (Flat.convertExpr arg scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .unary op sa.expr, env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_unary_step sf op _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .unary op (Flat.convertExpr arg scope envVar envMap st).fst } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : arg.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_arg : noCallFrameReturn arg = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr
      have hexprwf_arg : ExprAddrWF arg sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth arg.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst }
          { sc with expr := arg }
          ev sa scope st (Flat.convertExpr arg scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_arg hexprwf_arg (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.unary op sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .unary op arg } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_unary_step _ op _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | binary op lhs rhs =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    cases hlv : Core.exprValue? lhs with
    | some lv =>
      have hlit_lhs : lhs = .lit lv := by
        cases lhs <;> simp [Core.exprValue?] at hlv; subst hlv; rfl
      subst hlit_lhs
      simp [Flat.convertExpr] at hconv
      cases hrv : Core.exprValue? rhs with
      | some rv =>
        -- Both values: evaluate binary op
        have hlit_rhs : rhs = .lit rv := by
          cases rhs <;> simp [Core.exprValue?] at hrv; subst hrv; rfl
        subst hlit_rhs
        simp [Flat.convertExpr] at hconv
        have hsf_eta : sf = { sf with expr := .binary op (.lit (Flat.convertValue lv)) (.lit (Flat.convertValue rv)) } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        rw [Flat_step?_binary_values] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State :=
          ⟨.lit (Core.evalBinary op lv rv), sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · show Core.step? sc = some (.silent, sc')
          have hsc' : sc = { sc with expr := .binary op (.lit lv) (.lit rv) } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          simp [Core.step?, Core.exprValue?, Core.pushTrace, sc']
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF]; exact evalBinary_valueAddrWF op lv rv sc.heap.objects.size
            (by simp [ExprAddrWF] at hexprwf; exact hexprwf.1)
            (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2)
        · exact ⟨st, st, by
            simp [sc', Flat.convertExpr, evalBinary_convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
      | none =>
        -- rhs stepping, lhs is a value
        have hsupp_rhs : rhs.supported = true := by
          have h := hsupp; unfold Core.Expr.supported at h; simp [Bool.and_eq_true] at h; exact h.2
        have hfnv : Flat.exprValue? (Flat.convertExpr rhs scope envVar envMap st).fst = none :=
          convertExpr_not_value_supported rhs hrv hsupp_rhs scope envVar envMap st
        have hsf_eta : sf = { sf with expr := (Flat.Expr.binary op (.lit (Flat.convertValue lv))
            (Flat.convertExpr rhs scope envVar envMap st).fst) } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst } = some (ev, sa) ∧
            sf' = { expr := .binary op (.lit (Flat.convertValue lv)) sa.expr, env := sa.env, heap := sa.heap,
                    trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
          match hm : Flat.step? { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst } with
          | some (t, sa) =>
            have heq := Flat_step?_binary_rhs_step sf op (Flat.convertValue lv) _ hfnv t sa hm
            rw [heq] at hstep; simp at hstep
            obtain ⟨rfl, hsf'eq⟩ := hstep
            exact ⟨sa, rfl, hsf'eq.symm⟩
          | none =>
            have heq : Flat.step? { sf with expr := .binary op (.lit (Flat.convertValue lv)) (Flat.convertExpr rhs scope envVar envMap st).fst } = none := by
              have hlv : Flat.exprValue? (.lit (Flat.convertValue lv)) = some (Flat.convertValue lv) := rfl
              simp only [Flat.step?, hlv, hfnv, hm]
            rw [heq] at hstep; exact absurd hstep (by simp)
        subst hsf'_eq
        have hdepth : rhs.depth < n := by simp [Core.Expr.depth] at hd; omega
        have hncfr_rhs : noCallFrameReturn rhs = true := by
          simp [noCallFrameReturn] at hncfr; exact hncfr
        have hexprwf_rhs : ExprAddrWF rhs sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf.2
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
          ih_depth rhs.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst }
            { sc with expr := rhs }
            ev sa scope st (Flat.convertExpr rhs scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_rhs hexprwf_rhs hsupp_rhs
            (by simp)
            ⟨hsubstep⟩
        let sc' : Core.State :=
          ⟨.binary op (.lit lv) sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
        · show Core.step? sc = some (ev, sc')
          have hsc' : sc = { sc with expr := .binary op (.lit lv) rhs } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core_step?_binary_rhs_step _ op lv _ hrv _ _ hcstep_sub
        · simp [sc', htrace, htrace_sub]
        · exact hinj'
        · exact henvCorr'
        · exact henvwf'
        · exact hheapvwf'
        · exact hheapna'
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp only [sc']; simp only [ExprAddrWF]; exact ⟨by
            exact ValueAddrWF_mono (by simp [ExprAddrWF] at hexprwf; exact hexprwf.1) (Core_step_heap_size_mono hcstep_sub), hexprwf'⟩
        · exact ⟨st_a, st_a', by
            simp [sc', Flat.convertExpr, Flat.exprValue?]
            exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
    | none =>
      -- lhs stepping
      have hfnv : Flat.exprValue? (Flat.convertExpr lhs scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported lhs hlv (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.binary op (Flat.convertExpr lhs scope envVar envMap st).fst
          (Flat.convertExpr rhs scope envVar envMap (Flat.convertExpr lhs scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr lhs scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .binary op sa.expr
                    (Flat.convertExpr rhs scope envVar envMap (Flat.convertExpr lhs scope envVar envMap st).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr lhs scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_binary_lhs_step sf op
            (Flat.convertExpr rhs scope envVar envMap (Flat.convertExpr lhs scope envVar envMap st).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.binary op (Flat.convertExpr lhs scope envVar envMap st).fst
              (Flat.convertExpr rhs scope envVar envMap (Flat.convertExpr lhs scope envVar envMap st).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : lhs.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_lhs : noCallFrameReturn lhs = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1
      have hexprwf_lhs : ExprAddrWF lhs sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth lhs.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr lhs scope envVar envMap st).fst }
          { sc with expr := lhs }
          ev sa scope st (Flat.convertExpr lhs scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_lhs hexprwf_lhs (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.binary op sc_sub'.expr rhs, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .binary op lhs rhs } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_binary_lhs_step _ op _ _ hlv _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
      · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf', by
            exact ExprAddrWF_mono rhs (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) (Core_step_heap_size_mono hcstep_sub)⟩
      · have hrhs := convertExpr_state_determined rhs scope envVar envMap
            (Flat.convertExpr lhs scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
        refine ⟨st_a, (Flat.convertExpr rhs scope envVar envMap st_a').snd, ?_, hAgreeIn, ?_⟩
        · simp only [sc', Flat.convertExpr]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
          rw [hrhs.1]
        · rw [hconv.2]; exact hrhs.2
  | call f args =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? f with
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr f scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported f hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.call (Flat.convertExpr f scope envVar envMap st).fst
          (.lit .null)
          (Flat.convertExprList args scope envVar envMap (Flat.convertExpr f scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
          Flat.step? { sf with expr := (Flat.convertExpr f scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .call sa.expr (.lit .null)
                    (Flat.convertExprList args scope envVar envMap (Flat.convertExpr f scope envVar envMap st).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr f scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_call_func_step sf (.lit .null)
            (Flat.convertExprList args scope envVar envMap (Flat.convertExpr f scope envVar envMap st).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.call (Flat.convertExpr f scope envVar envMap st).fst
              (.lit .null)
              (Flat.convertExprList args scope envVar envMap (Flat.convertExpr f scope envVar envMap st).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : f.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_f : noCallFrameReturn f = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1
      have hexprwf_f : ExprAddrWF f sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf',
             hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth f.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr f scope envVar envMap st).fst }
          { sc with expr := f }
          ev sa scope st (Flat.convertExpr f scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_f hexprwf_f (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.call sc_sub'.expr args, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .call f args } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_call_func_step _ args _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
      · simp only [sc', ExprAddrWF]; exact ⟨hexprwf',
            ExprAddrListWF_mono args
              (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2)
              (Core_step_heap_size_mono hcstep_sub)⟩
      · have hargs := convertExprList_state_determined args scope envVar envMap
            (Flat.convertExpr f scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
        refine ⟨st_a, (Flat.convertExprList args scope envVar envMap st_a').snd, ?_, hAgreeIn, ?_⟩
        · simp only [sc', Flat.convertExpr]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
          rw [hargs.1]
        · rw [hst]; exact hargs.2
    | some cv =>
      have hlit : f = .lit cv := by
        cases f <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr hst
      -- Case split on whether all args are values
      cases hallv : Core.allValues args with
      | some argVals =>
        -- Case split on whether callee is a function
        have hfunc_or_not : (∃ idx, cv = .function idx) ∨ (∀ idx, cv ≠ .function idx) := by
          cases cv with
          | function idx => left; exact ⟨idx, rfl⟩
          | _ => right; intro idx h; cases h
        rcases hfunc_or_not with ⟨idx, rfl⟩ | hnotfunc
        · -- Function call case: cv = .function idx, all args are values
          by_cases hidx : idx = Core.consoleLogIdx
          · -- ConsoleLog call: both sides produce .log msg, result .lit .undefined
            subst hidx
            have hfvals := allValues_convertExprList_valuesFromExprList args argVals scope envVar envMap st hallv
            have hmsg := consoleLog_msg_convertValue argVals
            have hsf_eta : sf = { sf with expr := (Flat.Expr.call (.lit (.closure Core.consoleLogIdx 0)) (.lit .null)
                (Flat.convertExprList args scope envVar envMap st).fst) } := by
              cases sf; simp_all [Flat.convertValue]
            rw [hsf_eta] at hstep
            -- Both Flat and Core produce (.log msg, .lit .undefined)
            have hflat := Flat_step?_call_consoleLog_vals sf 0 .null _ _ hfvals
            have hst_eq := allValues_convertExprList_state args argVals scope envVar envMap st hallv
            -- Prove Core step independently
            have hsc_eta : sc = ⟨.call (.lit (.function Core.consoleLogIdx)) args, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            have hcore := Core_step?_call_consoleLog_flat_msg args argVals sc.env sc.heap sc.trace sc.funcs sc.callStack hallv
            rw [← hsc_eta] at hcore
            -- Both steps produce the same (event, state') pair
            let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap, sc.trace ++ [ev], sc.funcs, sc.callStack⟩
            have hpair := hstep.symm.trans hflat
            simp only [Option.some.injEq, Prod.mk.injEq] at hpair
            obtain ⟨hev_eq, hsf'_eq⟩ := hpair
            subst hev_eq; subst hsf'_eq
            refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
            · -- Core.step?: eliminate dependent match by case splitting
              revert hcore
              cases argVals with
              | nil => intro hcore; exact hcore
              | cons hd tl => cases tl with
                | nil => intro hcore; exact hcore
                | cons a b => intro hcore; exact hcore
            · simp [sc', htrace]
            · exact hinj
            · exact henvCorr
            · exact henvwf
            · exact hheapvwf
            · simp [sc', hheapna]
            · simp [sc', noCallFrameReturn]
            · simp [sc', ExprAddrWF, ValueAddrWF]
            · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩,
                by rw [hst, hst_eq]; exact ⟨rfl, rfl⟩⟩
          · -- Non-consoleLog function call: FuncsCorr now available (wired into CC_SimRel).
            -- BLOCKED: Still needs multi-step simulation (Flat call is N steps vs Core's 1).
            -- hfuncCorr : FuncsCorr injMap sc.funcs sf.funcs t.functions
            -- Use hfuncCorr to extract matching Flat.FuncDef for the Core function call.
            sorry
        · -- Non-function callee with all-value args
          have hnc := convertValue_not_closure_of_not_function cv hnotfunc
          have hfvals := allValues_convertExprList_valuesFromExprList args argVals scope envVar envMap st hallv
          have hsf_eta : sf = { sf with expr := (Flat.Expr.call (.lit (Flat.convertValue cv)) (.lit .null)
              (Flat.convertExprList args scope envVar envMap st).fst) } := by
            cases sf; simp_all
          rw [hsf_eta] at hstep
          rw [Flat_step?_call_nonclosure _ _ _ _ _ hfvals hnc] at hstep
          simp at hstep
          obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
          let sc' : Core.State :=
            ⟨.lit .undefined, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
          refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
          · show Core.step? sc = some (.silent, sc')
            have hsc' : sc = { sc with expr := .call (.lit cv) args } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            have := Core.step_call_nonfunc_exact cv args argVals sc.env sc.heap sc.trace sc.funcs sc.callStack hnotfunc hallv
            simp only [Core.pushTrace, sc'] at this ⊢; exact this
          · simp [sc', htrace]
          · exact hinj
          · exact henvCorr
          · exact henvwf
          · exact hheapvwf
          · simp [sc', hheapna]
          · simp [sc', noCallFrameReturn]
          · simp [sc', ExprAddrWF, ValueAddrWF]
          · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by rw [hst, allValues_convertExprList_state args argVals scope envVar envMap st hallv]; exact ⟨rfl, rfl⟩⟩
            simp [sc', Flat.convertExpr, Flat.convertValue]
      | none =>
        -- allValues args = none, so there exists a non-value arg
        cases hcfnv : Core.firstNonValueExpr args with
        | none => exact False.elim (Core.allValues_firstNonValue_contra hallv hcfnv)
        | some val =>
          obtain ⟨done_c, target_c, rest_c⟩ := val
          have htarget_not_lit := Core.firstNonValueExpr_not_lit hcfnv
          have htarget_novalue : Core.exprValue? target_c = none := by
            cases target_c with
            | lit v => exact absurd rfl (htarget_not_lit v)
            | _ => rfl
          have htarget_supp : target_c.supported = true :=
            listSupported_firstNonValueExpr_target hcfnv (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          have hffnv := convertExprList_firstNonValueExpr_some args scope envVar envMap st
              done_c target_c rest_c hcfnv htarget_novalue htarget_supp
          have hsf_eta : sf = { sf with expr := (Flat.Expr.call (.lit (Flat.convertValue cv)) (.lit .null)
              (Flat.convertExprList args scope envVar envMap st).fst) } := by
            cases sf; simp_all
          rw [hsf_eta] at hstep
          have hvals := valuesFromExprList_none_of_firstNonValueExpr hffnv
          obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
              Flat.step? { sf with expr := (Flat.convertExpr target_c scope envVar envMap
                (Flat.convertExprList done_c scope envVar envMap st).snd).fst } = some (ev, sa) ∧
              sf' = { expr := .call (.lit (Flat.convertValue cv)) (.lit .null)
                        ((Flat.convertExprList done_c scope envVar envMap st).fst ++
                         [sa.expr] ++
                         (Flat.convertExprList rest_c scope envVar envMap
                           (Flat.convertExpr target_c scope envVar envMap
                             (Flat.convertExprList done_c scope envVar envMap st).snd).snd).fst),
                      env := sa.env, heap := sa.heap,
                      trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
            match hm : Flat.step? { sf with expr := (Flat.convertExpr target_c scope envVar envMap
                (Flat.convertExprList done_c scope envVar envMap st).snd).fst } with
            | some (t, se) =>
              have heq := Flat_step?_call_value_step_arg sf (Flat.convertValue cv) .null _ hvals _ _ _ hffnv t se hm
              rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨se, rfl, hsf'eq.symm⟩
            | none =>
              have heq := Flat_step?_call_value_arg_none sf (Flat.convertValue cv) .null _ hvals _ _ _ hffnv hm
              rw [heq] at hstep; exact absurd hstep (by simp)
          subst hsf'_eq
          have hdepth : target_c.depth < n := by
            simp [Core.Expr.depth] at hd
            have := Core.firstNonValueExpr_depth hcfnv; omega
          have ⟨hncfr_done, hncfr_target, hncfr_rest⟩ :=
            firstNonValueExpr_listNoCallFrameReturn hcfnv (by simp [noCallFrameReturn] at hncfr; exact hncfr)
          have hexprwf_target : ExprAddrWF target_c sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf
            exact ExprAddrListWF_firstNonValueExpr_target hcfnv hexprwf.2
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf',
                  hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
            ih_depth target_c.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr target_c scope envVar envMap
                (Flat.convertExprList done_c scope envVar envMap st).snd).fst }
              { sc with expr := target_c }
              ev sa scope
              (Flat.convertExprList done_c scope envVar envMap st).snd
              (Flat.convertExpr target_c scope envVar envMap
                (Flat.convertExprList done_c scope envVar envMap st).snd).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_target hexprwf_target htarget_supp
              (by simp)
              ⟨hsubstep⟩
          let sc' : Core.State :=
            ⟨.call (.lit cv) (done_c ++ [sc_sub'.expr] ++ rest_c),
             sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · -- Core.step?
            show Core.step? sc = some (ev, sc')
            have hsc' : sc = { sc with expr := .call (.lit cv) args } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            have hcstep_anon : Core.step? ⟨target_c, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ =
                some (ev, sc_sub') := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; exact hcstep_sub
            have hcore_step := Core.step_call_step_arg cv args sc.env sc.heap sc.trace sc.funcs sc.callStack
                hallv done_c target_c rest_c hcfnv ev sc_sub' hcstep_anon
            simp only [Core.pushTrace] at hcore_step
            have : sc' = { sc_sub' with
              expr := .call (.lit cv) (done_c ++ [sc_sub'.expr] ++ rest_c),
              trace := sc.trace ++ [ev] } := by simp [sc']
            rw [this]; exact hcore_step
          · -- trace
            simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · -- noCallFrameReturn
            simp only [sc', noCallFrameReturn]
            rw [listNoCallFrameReturn_append, listNoCallFrameReturn_append]
            simp [listNoCallFrameReturn, hncfr', hncfr_done, hncfr_rest]
          · -- ExprAddrWF call
            simp only [sc', ExprAddrWF]
            exact ⟨ValueAddrWF_mono (by simp [ExprAddrWF] at hexprwf; exact hexprwf.1)
                (Core_step_heap_size_mono hcstep_sub),
              ExprAddrListWF_firstNonValueExpr_reconstruct hcfnv
                (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) hexprwf'
                (Core_step_heap_size_mono hcstep_sub)⟩
          · -- CCState agreement (call sub-step)
            have hargs := firstNonValueExpr_decompose hcfnv
            have hsd := convertExpr_state_determined sc_sub'.expr scope envVar envMap
              (Flat.convertExprList done_c scope envVar envMap st).snd st_a hAgreeIn.1 hAgreeIn.2
            have hconv'_fst : sa.expr = (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst :=
              congrArg Prod.fst hconv'
            have hconv'_snd : st_a' = (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd :=
              congrArg Prod.snd hconv'
            have htgt_eq : (Flat.convertExpr sc_sub'.expr scope envVar envMap
                (Flat.convertExprList done_c scope envVar envMap st).snd).fst = sa.expr :=
              hsd.1.trans hconv'_fst.symm
            have hagree_mid : CCStateAgree
                (Flat.convertExpr target_c scope envVar envMap
                  (Flat.convertExprList done_c scope envVar envMap st).snd).snd
                (Flat.convertExpr sc_sub'.expr scope envVar envMap
                  (Flat.convertExprList done_c scope envVar envMap st).snd).snd := by
              constructor
              · have h1 := hAgreeOut.1; rw [hconv'_snd] at h1; exact h1.trans hsd.2.1.symm
              · have h2 := hAgreeOut.2; rw [hconv'_snd] at h2; exact h2.trans hsd.2.2.symm
            have hsd_rest := convertExprList_state_determined rest_c scope envVar envMap
              _ _ hagree_mid.1 hagree_mid.2
            have hcels_snd : ∀ (e : Core.Expr) (s : Flat.CCState),
                (Flat.convertExprList [e] scope envVar envMap s).snd =
                (Flat.convertExpr e scope envVar envMap s).snd := by
              intro e s; simp [Flat.convertExprList]
            have hcels_fst : ∀ (e : Core.Expr) (s : Flat.CCState),
                (Flat.convertExprList [e] scope envVar envMap s).fst =
                [(Flat.convertExpr e scope envVar envMap s).fst] := by
              intro e s; simp [Flat.convertExprList]
            have hdecomp_fst : ∀ (x : Core.Expr),
                (Flat.convertExprList (done_c ++ [x] ++ rest_c) scope envVar envMap st).fst =
                (Flat.convertExprList done_c scope envVar envMap st).fst ++
                [(Flat.convertExpr x scope envVar envMap
                  (Flat.convertExprList done_c scope envVar envMap st).snd).fst] ++
                (Flat.convertExprList rest_c scope envVar envMap
                  (Flat.convertExpr x scope envVar envMap
                    (Flat.convertExprList done_c scope envVar envMap st).snd).snd).fst := by
              intro x
              rw [convertExprList_append, convertExprList_append, hcels_fst]
              rw [show (Flat.convertExprList (done_c ++ [x]) scope envVar envMap st).snd =
                  (Flat.convertExpr x scope envVar envMap
                    (Flat.convertExprList done_c scope envVar envMap st).snd).snd from by
                rw [convertExprList_append_snd, hcels_snd]]
            have hdecomp_snd : ∀ (x : Core.Expr),
                (Flat.convertExprList (done_c ++ [x] ++ rest_c) scope envVar envMap st).snd =
                (Flat.convertExprList rest_c scope envVar envMap
                  (Flat.convertExpr x scope envVar envMap
                    (Flat.convertExprList done_c scope envVar envMap st).snd).snd).snd := by
              intro x
              rw [convertExprList_append_snd, convertExprList_append_snd, hcels_snd]
            have hexpr_eq :
                Flat.Expr.call (.lit (Flat.convertValue cv)) (.lit .null)
                  ((Flat.convertExprList done_c scope envVar envMap st).fst ++
                  [sa.expr] ++
                  (Flat.convertExprList rest_c scope envVar envMap
                    (Flat.convertExpr target_c scope envVar envMap
                      (Flat.convertExprList done_c scope envVar envMap st).snd).snd).fst) =
                Flat.Expr.call (.lit (Flat.convertValue cv)) (.lit .null)
                  (Flat.convertExprList (done_c ++ [sc_sub'.expr] ++ rest_c) scope envVar envMap st).fst := by
              rw [hdecomp_fst]
              congr 1; congr 1; congr 1
              · congr 1; exact htgt_eq.symm
              · exact hsd_rest.1
            refine ⟨st, (Flat.convertExprList (done_c ++ [sc_sub'.expr] ++ rest_c) scope envVar envMap st).snd,
              ?_, ⟨rfl, rfl⟩, ?_⟩
            · simp only [sc', Flat.convertExpr]
              exact Prod.ext hexpr_eq rfl
            · rw [hst, hargs, hdecomp_snd target_c, hdecomp_snd sc_sub'.expr]
              exact hsd_rest.2
  | newObj f args =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    -- Core.newObj always allocates an empty object at heap.nextAddr, ignoring sub-expressions.
    -- The simulation only works when all Flat sub-expressions are values (Flat also allocates).
    cases hfev : Core.exprValue? f with
    | none =>
      sorry -- BLOCKED: multi-step simulation gap (architectural). Same class as L4921.
            -- Core newObj allocates immediately regardless of sub-expression evaluation,
            -- but Flat steps f first. Intermediate Flat state (f partially evaluated) is not
            -- convertExpr of any Core expr. Needs many-to-one or stuttering simulation.
    | some fv =>
      have hflit : f = .lit fv := by
        cases f <;> simp [Core.exprValue?] at hfev; subst hfev; rfl
      subst hflit
      simp [Flat.convertExpr] at hfexpr hst
      cases hcfnv : Core.firstNonValueExpr args with
      | some val =>
        sorry -- BLOCKED: multi-step simulation gap (architectural). Same class as L4921.
              -- Core newObj allocates immediately regardless of arg evaluation,
              -- but Flat steps the first non-value arg. Needs many-to-one or stuttering simulation.
      | none =>
        -- All elements are values: both Core and Flat allocate empty objects on heap.
        have hffnv := convertExprList_firstNonValueExpr_none args scope envVar envMap st hcfnv
        have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values _ hffnv
        have hsf_eta : sf = { sf with expr := (Flat.Expr.newObj (.lit (Flat.convertValue fv))
            (.lit .null) (Flat.convertExprList args scope envVar envMap st).fst) } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        rw [Flat.step?_newObj_allValues _ _ _ _ _ _ _ rfl rfl hvs] at hstep
        simp only [Prod.mk.injEq, Option.some.injEq] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        have hna_eq : sc.heap.nextAddr = sf.heap.nextAddr := hinj.2.1
        have hst_eq : (Flat.convertExprList args scope envVar envMap st).snd = st :=
          convertExprList_state_none args scope envVar envMap st hcfnv
        let caddr := sc.heap.nextAddr
        let cheap' : Core.Heap := { objects := sc.heap.objects.push [], nextAddr := caddr + 1 }
        let sc' : Core.State := ⟨.lit (.object caddr), sc.env, cheap',
          sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        have hcstep : Core.step? sc = some (.silent, sc') := by
          have hsc' : sc = { sc with expr := .newObj (.lit fv) args } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          have := Core.step_newObj_exact (.lit fv) args sc.env sc.heap sc.trace sc.funcs sc.callStack
          simp only [Core.pushTrace, sc', cheap', caddr] at this ⊢; exact this
        have hinj' : HeapInj injMap cheap' ⟨sf.heap.objects.push [],
            sf.heap.nextAddr + 1⟩ :=
          HeapInj_alloc_both hinj []
        have hheapvwf' : HeapValuesWF cheap' := by
          intro addr haddr props' hprops' kv hkv
          simp only [cheap', caddr, Array.size_push] at haddr
          rw [Array.getElem?_push] at hprops'
          split at hprops'
          · simp only [Option.some.injEq] at hprops'; subst hprops'; simp at hkv
          · next hne =>
            have haddr' : addr < sc.heap.objects.size := by omega
            exact ValueAddrWF_mono (hheapvwf addr haddr' props' hprops' kv hkv) (by simp only [cheap', Array.size_push]; omega)
        refine ⟨injMap, sc', ⟨hcstep⟩, ?trace_, ?hinj_, ?envcorr_, ?envwf_, ?hvwf_,
          ?hna_, ?ncfr_, ?ewf_, ?ccst_, hfuncCorr⟩
        case trace_ => simp [sc', htrace]
        case hinj_ => exact hinj'
        case envcorr_ => exact henvCorr
        case envwf_ => exact EnvAddrWF_mono henvwf (by simp only [sc', cheap', Array.size_push]; omega)
        case hvwf_ => exact hheapvwf'
        case hna_ => simp only [sc', cheap', caddr, Array.size_push, hheapna]
        case ncfr_ => simp [sc', noCallFrameReturn]
        case ewf_ => simp only [sc', ExprAddrWF, ValueAddrWF, cheap', caddr, Array.size_push]; rw [hheapna]; omega
        case ccst_ => exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue, caddr, hna_eq],
          ⟨rfl, rfl⟩, by rw [hst, hst_eq]; exact ⟨rfl, rfl⟩⟩
  | getProp obj prop =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv =>
      have hlit : obj = .lit cv := by
        cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr hst
      have hsf_eta : sf = { sf with expr := .getProp (.lit (Flat.convertValue cv)) prop } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Sub-cases by value type: object (heap lookup), string (length), or primitive (undefined)
      have hno_core : (∃ addr, cv = .object addr) ∨ (∃ str, cv = .string str) ∨ (∀ a, cv ≠ .object a) ∧ (∀ s, cv ≠ .string s) := by
        cases cv with
        | object a => left; exact ⟨a, rfl⟩
        | string s => right; left; exact ⟨s, rfl⟩
        | _ => right; right; exact ⟨by intro a; simp [Core.Value.noConfusion], by intro s; simp [Core.Value.noConfusion]⟩
      rcases hno_core with ⟨addr, rfl⟩ | ⟨str, rfl⟩ | ⟨hno, hns⟩
      · -- Object case: heap property lookup
        have : Flat.convertValue (.object addr) = .object addr := rfl
        rw [this] at hstep hsf_eta hfexpr
        rw [Flat_step?_getProp_object] at hstep
        simp at hstep; obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        have haddr_wf : addr < sc.heap.objects.size := by
          simp [ExprAddrWF, ValueAddrWF] at hexprwf; exact hexprwf
        -- Case split on heap lookup to build core result
        cases hprops : sc.heap.objects[addr]? with
        | none =>
          let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
            sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
          refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
          · have hsc' : sc = { sc with expr := .getProp (.lit (.object addr)) prop } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            have := Core.step?_getProp_object_val addr prop sc.env sc.heap sc.trace sc.funcs sc.callStack
            simp only [Core.pushTrace, sc', hprops] at this ⊢; exact this
          · simp [sc', htrace]
          · exact hinj
          · exact henvCorr
          · exact henvwf
          · exact hheapvwf
          · simp [sc', hheapna]
          · simp [sc', noCallFrameReturn]
          · simp only [sc', ExprAddrWF, ValueAddrWF]
          · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
            simp only [sc', Flat.convertExpr, Flat.convertValue]
            congr 1; congr 1
            rw [heapObjectAt?_eq, ← HeapInj_get hinj haddr_wf, hprops]
        | some props =>
          cases hfind : props.find? (fun (kv : Core.PropName × Core.Value) => kv.fst == prop) with
          | none =>
            let coreResult := if prop == "length" then Core.Value.number (Float.ofNat props.length) else Core.Value.undefined
            let sc' : Core.State := ⟨.lit coreResult, sc.env, sc.heap,
              sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
            refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
            · have hsc' : sc = { sc with expr := .getProp (.lit (.object addr)) prop } := by
                obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
              rw [hsc']
              have := Core.step?_getProp_object_val addr prop sc.env sc.heap sc.trace sc.funcs sc.callStack
              simp only [Core.pushTrace, sc', coreResult, hprops, hfind] at this ⊢; exact this
            · simp [sc', htrace]
            · exact hinj
            · exact henvCorr
            · exact henvwf
            · exact hheapvwf
            · simp [sc', hheapna]
            · simp [sc', noCallFrameReturn]
            · simp only [sc', ExprAddrWF, coreResult]; split <;> simp [ValueAddrWF]
            · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
              simp only [sc', Flat.convertExpr, Flat.convertValue, coreResult]
              congr 1; congr 1
              rw [heapObjectAt?_eq, ← HeapInj_get hinj haddr_wf, hprops]
              simp only [hfind]
              split
              · next h => simp [h]
              · next h => simp [h]
          | some kv =>
            let sc' : Core.State := ⟨.lit kv.2, sc.env, sc.heap,
              sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
            refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
            · have hsc' : sc = { sc with expr := .getProp (.lit (.object addr)) prop } := by
                obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
              rw [hsc']
              have := Core.step?_getProp_object_val addr prop sc.env sc.heap sc.trace sc.funcs sc.callStack
              simp only [Core.pushTrace, sc', hprops, hfind] at this ⊢; exact this
            · simp [sc', htrace]
            · exact hinj
            · exact henvCorr
            · exact henvwf
            · exact hheapvwf
            · simp [sc', hheapna]
            · simp [sc', noCallFrameReturn]
            · simp only [sc', ExprAddrWF]
              exact hheapvwf addr haddr_wf props hprops kv (list_find?_mem hfind)
            · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
              simp only [sc', Flat.convertExpr]
              congr 1; congr 1
              rw [heapObjectAt?_eq, ← HeapInj_get hinj haddr_wf, hprops]
              simp only [hfind]; exact (coreToFlatValue_eq_convertValue kv.2).symm
      · -- String case: length or undefined
        have : Flat.convertValue (.string str) = .string str := rfl
        rw [this] at hstep hsf_eta hfexpr
        rw [Flat_step?_getProp_string] at hstep
        simp at hstep; obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let coreResult := if prop == "length" then Core.Value.number (Float.ofNat str.length) else Core.Value.undefined
        let sc' : Core.State := ⟨.lit coreResult, sc.env, sc.heap,
          sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · have hsc' : sc = { sc with expr := .getProp (.lit (.string str)) prop } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          have := Core.step?_getProp_string_val str prop sc.env sc.heap sc.trace sc.funcs sc.callStack
          simp only [Core.pushTrace, sc', coreResult] at this ⊢; exact this
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp only [sc', ExprAddrWF, coreResult]; split <;> simp [ValueAddrWF]
        · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
          simp only [sc', Flat.convertExpr, coreResult]
          congr 1; congr 1; simp only [beq_iff_eq, coreResult]
          split <;> simp [Flat.convertValue]
      · -- Primitive case (null, undefined, bool, number, function): both return undefined
        rw [Flat_step?_getProp_primitive _ _ prop (convertValue_not_object cv hno) (convertValue_not_string cv hns)] at hstep
        simp at hstep; obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
          sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · have hsc' : sc = { sc with expr := .getProp (.lit cv) prop } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core_step?_getProp_primitive _ cv prop hno hns
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF, ValueAddrWF]
        · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
          simp [sc', Flat.convertExpr, Flat.convertValue]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported obj hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .getProp (Flat.convertExpr obj scope envVar envMap st).fst prop } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .getProp sa.expr prop, env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_getProp_step sf prop _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .getProp (Flat.convertExpr obj scope envVar envMap st).fst prop } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : obj.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_arg : noCallFrameReturn obj = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr
      have hexprwf_arg : ExprAddrWF obj sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_arg hexprwf_arg (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.getProp sc_sub'.expr prop, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .getProp obj prop } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_getProp_step _ prop _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | setProp obj prop value =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv =>
      have hlit : obj = .lit cv := by
        cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr hst
      have hsf_eta : sf = { sf with expr := (Flat.Expr.setProp (.lit (Flat.convertValue cv)) prop
          (Flat.convertExpr value scope envVar envMap st).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Sub-case split: is value also a Core value?
      cases hcev_v : Core.exprValue? value with
      | some vv =>
        -- Both obj and value are values
        have hlit_v : value = .lit vv := by
          cases value <;> simp [Core.exprValue?] at hcev_v; subst hcev_v; rfl
        subst hlit_v
        have hcv_v : (Flat.convertExpr (.lit vv) scope envVar envMap st).fst = .lit (Flat.convertValue vv) := by
          simp [Flat.convertExpr]
        rw [hcv_v] at hstep
        simp [Flat.convertExpr] at hfexpr hst
        -- Case split: cv is object or not
        have hno_core : (∃ addr, cv = .object addr) ∨ (∀ a, cv ≠ .object a) := by
          cases cv with
          | object a => left; exact ⟨a, rfl⟩
          | _ => right; intro a; exact Core.Value.noConfusion
        rcases hno_core with ⟨addr, rfl⟩ | hno
        · -- Object case: heap mutation (set prop at addr)
          have : Flat.convertValue (.object addr) = .object addr := rfl
          rw [this] at hstep
          rw [Flat_step?_setProp_object_both_values] at hstep
          simp only [flatToCoreValue_convertValue, Prod.mk.injEq, Option.some.injEq] at hstep
          obtain ⟨hev, hsf'⟩ := hstep; subst hev; subst hsf'
          have haddr_wf : addr < sc.heap.objects.size := by
            simp [ExprAddrWF, ValueAddrWF] at hexprwf; exact hexprwf.1
          have hvv_wf : ValueAddrWF vv sc.heap.objects.size := by
            simp [ExprAddrWF, ValueAddrWF] at hexprwf; exact hexprwf.2
          -- Build core result state
          let coreHeap' := match sc.heap.objects[addr]? with
            | some (props : List (Core.PropName × Core.Value)) =>
                let updated := if props.any (fun (kv : Core.PropName × Core.Value) => kv.fst == prop)
                  then props.map (fun (kv : Core.PropName × Core.Value) => if kv.fst == prop then (prop, vv) else kv)
                  else props ++ [(prop, vv)]
                { sc.heap with objects := sc.heap.objects.set! addr updated }
            | none => sc.heap
          let sc' : Core.State := ⟨.lit vv, sc.env, coreHeap',
            sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
          refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
          · -- Core step
            have hsc' : sc = { sc with expr := .setProp (.lit (.object addr)) prop (.lit vv) } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            have := Core.step?_setProp_object_val addr prop vv sc.env sc.heap sc.trace sc.funcs sc.callStack
            simp only [Core.pushTrace, sc', coreHeap'] at this ⊢; exact this
          · -- trace
            simp [sc', htrace]
          · -- HeapInj: both heaps do same set! at addr
            simp only [sc', coreHeap']
            rw [heapObjectAt?_eq, ← HeapInj_get hinj haddr_wf]
            cases sc.heap.objects[addr]? with
            | none => exact hinj
            | some props => exact HeapInj_set_same hinj addr haddr_wf _
          · -- EnvCorrInj
            exact henvCorr
          · -- EnvAddrWF
            simp only [sc', coreHeap']
            cases sc.heap.objects[addr]? with
            | none => exact henvwf
            | some props => exact EnvAddrWF_mono henvwf (by simp [size_set!])
          · -- HeapValuesWF
            simp only [sc', coreHeap']
            cases hprops : sc.heap.objects[addr]? with
            | none => exact hheapvwf
            | some props =>
              apply HeapValuesWF_set_at hheapvwf
              intro kv hkv
              by_cases hany : props.any (fun kv => kv.fst == prop)
              · simp only [hany, ↓reduceIte] at hkv
                obtain ⟨orig, horig, rfl⟩ := List.mem_map.mp hkv
                split
                · simp only; exact hvv_wf
                · exact hheapvwf addr haddr_wf props hprops orig horig
              · simp only [hany, Bool.false_eq_true, ↓reduceIte] at hkv
                rcases List.mem_append.mp hkv with h | h
                · exact hheapvwf addr haddr_wf props hprops kv h
                · rw [List.mem_singleton.mp h]; simp only; exact hvv_wf
          · -- hheapna
            simp only [sc', coreHeap']
            split
            · simp [Array.size_setIfInBounds, hheapna]
            · exact hheapna
          · -- noCallFrameReturn
            simp [sc', noCallFrameReturn]
          · -- ExprAddrWF
            have hvv_wf' : ValueAddrWF vv sc.heap.objects.size := by
              simp [ExprAddrWF] at hexprwf; exact hexprwf.2
            have hsize : coreHeap'.objects.size = sc.heap.objects.size := by
              simp only [coreHeap']
              split
              · simp [size_set!]
              · rfl
            simp only [sc', ExprAddrWF, ValueAddrWF]
            rw [hsize]
            exact hvv_wf'
          · -- CCState threading
            refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩; simp [sc', Flat.convertExpr, Flat.convertValue]
        · -- Non-object case: heap unchanged, return value
          have hno_flat : ∀ addr, Flat.convertValue cv ≠ .object addr :=
            convertValue_not_object cv hno
          rw [Flat_step?_setProp_nonobject_both_values _ _ _ _ hno_flat] at hstep
          simp at hstep; obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
          let sc' : Core.State := ⟨.lit vv, sc.env, sc.heap,
            sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
          refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
          · have hsc' : sc = { sc with expr := .setProp (.lit cv) prop (.lit vv) } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            have := Core.step?_setProp_nonobject_val cv prop vv sc.env sc.heap sc.trace sc.funcs sc.callStack hno
            simp only [Core.pushTrace, sc'] at this ⊢; exact this
          · simp [sc', htrace]
          · exact hinj
          · exact henvCorr
          · exact henvwf
          · exact hheapvwf
          · simp [sc', hheapna]
          · simp [sc', noCallFrameReturn]
          · have hvv_wf' : ValueAddrWF vv sc.heap.objects.size := by
              simp [ExprAddrWF] at hexprwf; exact hexprwf.2
            simp only [sc', ExprAddrWF, ValueAddrWF]; exact hvv_wf'
          · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
            simp [sc', Flat.convertExpr, Flat.convertValue]
      | none =>
        -- Value needs stepping; obj is already a value
        have hfnv_v : Flat.exprValue? (Flat.convertExpr value scope envVar envMap st).fst = none :=
          convertExpr_not_value_supported value hcev_v (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
        have hcv_wf : ValueAddrWF cv sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf.1
        -- Extract value sub-step from Flat step
        obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
            Flat.step? { sf with expr := (Flat.convertExpr value scope envVar envMap st).fst } = some (ev, sa) ∧
            sf' = { expr := (Flat.Expr.setProp (.lit (Flat.convertValue cv)) prop sa.expr), env := sa.env, heap := sa.heap,
                    trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
          match hm : Flat.step? { sf with expr := (Flat.convertExpr value scope envVar envMap st).fst } with
          | some (t, sa) =>
            have hno_core2 : (∃ addr, cv = .object addr) ∨ (∀ a, cv ≠ .object a) := by
              cases cv with
              | object a => left; exact ⟨a, rfl⟩
              | _ => right; intro a; exact Core.Value.noConfusion
            rcases hno_core2 with ⟨addr, rfl⟩ | hno2
            · have : Flat.convertValue (.object addr) = .object addr := rfl
              rw [this] at hstep
              have heq := Flat_step?_setProp_object_step_value sf addr prop _ hfnv_v t sa hm
              rw [heq] at hstep; simp at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨sa, rfl, by rw [← hsf'eq]; congr 1⟩
            · have hno_flat := convertValue_not_object cv hno2
              have heq := Flat_step?_setProp_nonobject_step_value sf (Flat.convertValue cv) prop _ hfnv_v hno_flat t sa hm
              rw [heq] at hstep; simp at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨sa, rfl, hsf'eq.symm⟩
          | none =>
            have heq := Flat_step?_setProp_value_none sf (Flat.convertValue cv) prop _ hfnv_v hm
            rw [heq] at hstep; exact absurd hstep (by simp)
        subst hsf'_eq
        have hdepth : value.depth < n := by simp [Core.Expr.depth] at hd; omega
        have hncfr_v : noCallFrameReturn value = true := by
          simp [noCallFrameReturn] at hncfr; exact hncfr
        have hexprwf_v : ExprAddrWF value sc.heap.objects.size := by
          have := hexprwf; simp [ExprAddrWF] at this; exact this.2
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf',
                ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
          ih_depth value.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr value scope envVar envMap st).fst }
            { sc with expr := value }
            ev sa scope st (Flat.convertExpr value scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_v hexprwf_v (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
            (by simp)
            ⟨hsubstep⟩
        let sc' : Core.State :=
          ⟨.setProp (.lit cv) prop sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
        · show Core.step? sc = some (ev, sc')
          have hsc' : sc = { sc with expr := .setProp (.lit cv) prop value } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core_step?_setProp_value_step cv prop value hcev_v sc.env sc.heap sc.trace sc.funcs sc.callStack ev sc_sub' hcstep_sub
        · simp [sc', htrace, htrace_sub]
        · exact hinj'
        · exact henvCorr'
        · exact henvwf'
        · exact hheapvwf'
        · exact hheapna'
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp only [sc']; simp only [ExprAddrWF]
          have heap_mono := Core_step_heap_size_mono hcstep_sub
          exact ⟨ValueAddrWF_mono hcv_wf heap_mono, hexprwf'⟩
        · refine ⟨st_a, st_a', ?_, hAgreeIn, by rw [hst]; exact hAgreeOut⟩
          simp only [sc', Flat.convertExpr, Flat.convertValue]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported obj hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.setProp (Flat.convertExpr obj scope envVar envMap st).fst prop
          (Flat.convertExpr value scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .setProp sa.expr prop
                    (Flat.convertExpr value scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_setProp_obj_step sf prop
            (Flat.convertExpr value scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.setProp (Flat.convertExpr obj scope envVar envMap st).fst prop
              (Flat.convertExpr value scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : obj.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_obj : noCallFrameReturn obj = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1
      have hexprwf_obj : ExprAddrWF obj sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_obj hexprwf_obj (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.setProp sc_sub'.expr prop value, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .setProp obj prop value } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_setProp_obj_step _ prop _ _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
      · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf', by
            exact ExprAddrWF_mono value (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) (Core_step_heap_size_mono hcstep_sub)⟩
      · have hval := convertExpr_state_determined value scope envVar envMap
            (Flat.convertExpr obj scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
        refine ⟨st_a, (Flat.convertExpr value scope envVar envMap st_a').snd, ?_, hAgreeIn, ?_⟩
        · simp only [sc', Flat.convertExpr]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
          rw [hval.1]
        · rw [hst]; exact hval.2
  | getIndex obj idx =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv =>
      have hlit : obj = .lit cv := by
        cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr hst
      have hsf_eta : sf = { sf with expr := (Flat.Expr.getIndex (.lit (Flat.convertValue cv))
          (Flat.convertExpr idx scope envVar envMap st).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Sub-case split: is idx also a Core value?
      cases hcev_i : Core.exprValue? idx with
      | some iv =>
        -- Both obj and idx are values: getIndex lookup
        have hlit_i : idx = .lit iv := by
          cases idx <;> simp [Core.exprValue?] at hcev_i; subst hcev_i; rfl
        subst hlit_i
        have hcv_i : (Flat.convertExpr (.lit iv) scope envVar envMap st).fst = .lit (Flat.convertValue iv) := by
          simp [Flat.convertExpr]
        rw [hcv_i] at hstep
        simp [Flat.convertExpr] at hfexpr hst
        -- Case split: cv is object, string, or other
        have hno_core : (∃ addr, cv = .object addr) ∨ (∃ str, cv = .string str) ∨ ((∀ a, cv ≠ .object a) ∧ (∀ str, cv ≠ .string str)) := by
          cases cv with
          | object a => left; exact ⟨a, rfl⟩
          | string s => right; left; exact ⟨s, rfl⟩
          | _ => right; right; exact ⟨fun a => Core.Value.noConfusion, fun s => Core.Value.noConfusion⟩
        rcases hno_core with ⟨addr, rfl⟩ | ⟨str, rfl⟩ | ⟨hno, hns⟩
        · -- Object case: heap lookup
          have : Flat.convertValue (.object addr) = .object addr := rfl
          rw [this] at hstep
          rw [Flat_step?_getIndex_object_both_values] at hstep
          simp only [Prod.mk.injEq, Option.some.injEq] at hstep
          obtain ⟨hev, hsf'⟩ := hstep; subst hev; subst hsf'
          have haddr_wf : addr < sc.heap.objects.size := by
            simp [ExprAddrWF, ValueAddrWF] at hexprwf; exact hexprwf.1
          -- Relate Flat and Core heap lookups
          have hheap_eq : Flat.heapObjectAt? sf.heap addr = sc.heap.objects[addr]? := by
            rw [heapObjectAt?_eq, ← HeapInj_get hinj haddr_wf]
          rw [hheap_eq, valueToString_convertValue]
          -- Build Core result state
          -- Core step result matches Flat: both do same heap lookup
          -- Flat result (in sf') uses coreToFlatValue; Core result uses raw value
          -- coreToFlatValue = convertValue, so they agree
          -- Case split on heap lookup to build core result
          cases hprops : sc.heap.objects[addr]? with
          | none =>
            let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
              sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
            refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
            · have hsc' : sc = { sc with expr := .getIndex (.lit (.object addr)) (.lit iv) } := by
                obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
              rw [hsc']
              have := Core.step?_getIndex_object_val addr iv sc.env sc.heap sc.trace sc.funcs sc.callStack
              simp only [Core.pushTrace, sc', hprops] at this ⊢; exact this
            · simp [sc', htrace]
            · exact hinj
            · exact henvCorr
            · exact henvwf
            · exact hheapvwf
            · simp [sc', hheapna]
            · simp [sc', noCallFrameReturn]
            · simp only [sc', ExprAddrWF, ValueAddrWF]
            · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
              simp only [sc', Flat.convertExpr, Flat.convertValue]
          | some props =>
            cases hfind : props.find? (fun (kv : Core.PropName × Core.Value) => kv.fst == Core.valueToString iv) with
            | none =>
              let coreResult := if Core.valueToString iv == "length" then Core.Value.number (Float.ofNat props.length) else Core.Value.undefined
              let sc' : Core.State := ⟨.lit coreResult, sc.env, sc.heap,
                sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
              refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
              · have hsc' : sc = { sc with expr := .getIndex (.lit (.object addr)) (.lit iv) } := by
                  obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
                rw [hsc']
                have := Core.step?_getIndex_object_val addr iv sc.env sc.heap sc.trace sc.funcs sc.callStack
                simp only [Core.pushTrace, sc', coreResult, hprops, hfind] at this ⊢; exact this
              · simp [sc', htrace]
              · exact hinj
              · exact henvCorr
              · exact henvwf
              · exact hheapvwf
              · simp [sc', hheapna]
              · simp [sc', noCallFrameReturn]
              · simp only [sc', ExprAddrWF, coreResult]; split <;> simp [ValueAddrWF]
              · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
                simp only [sc', Flat.convertExpr, Flat.convertValue, coreResult]
                congr 1; congr 1
                simp only [hfind]
                split
                · next h => simp [h]
                · next h => simp [h]
            | some kv =>
              let sc' : Core.State := ⟨.lit kv.2, sc.env, sc.heap,
                sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
              refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
              · have hsc' : sc = { sc with expr := .getIndex (.lit (.object addr)) (.lit iv) } := by
                  obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
                rw [hsc']
                have := Core.step?_getIndex_object_val addr iv sc.env sc.heap sc.trace sc.funcs sc.callStack
                simp only [Core.pushTrace, sc', hprops, hfind] at this ⊢; exact this
              · simp [sc', htrace]
              · exact hinj
              · exact henvCorr
              · exact henvwf
              · exact hheapvwf
              · simp [sc', hheapna]
              · simp [sc', noCallFrameReturn]
              · simp only [sc', ExprAddrWF]
                exact hheapvwf addr haddr_wf props hprops kv (list_find?_mem hfind)
              · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
                simp only [sc', Flat.convertExpr]
                congr 1; congr 1
                simp only [hfind]; exact (coreToFlatValue_eq_convertValue kv.2).symm
        · -- String case: string indexing
          sorry /- AXIOM: getIndex string semantic mismatch.
            Float.toString is @[extern] opaque so we cannot prove
            ∀ n : Float, valueToString (.number n) ≠ "length".
            FIX: remove `if propName == "length"` from Flat.step?'s
            .string/.number branch (Flat/Semantics.lean ~L739), or
            add `axiom float_toString_ne_length`. -/
        · -- Non-object, non-string: both return .undefined
          have hno_flat : ∀ addr, Flat.convertValue cv ≠ .object addr := convertValue_not_object cv hno
          have hns_flat : ∀ str, Flat.convertValue cv ≠ .string str := by
            intro str; cases cv <;> simp [Flat.convertValue] <;>
              first | exact (hno _ rfl).elim | exact (hns _ rfl).elim | exact Flat.Value.noConfusion
          rw [Flat_step?_getIndex_other_both_values _ _ _ hno_flat hns_flat] at hstep
          simp only [Prod.mk.injEq, Option.some.injEq] at hstep
          obtain ⟨hev, hsf'⟩ := hstep; subst hev; subst hsf'
          let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
            sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
          refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
          · have hsc' : sc = { sc with expr := .getIndex (.lit cv) (.lit iv) } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            cases cv <;> (try exact (hno _ rfl).elim) <;> (try exact (hns _ rfl).elim) <;>
              (simp [Core.step?, Core.exprValue?, Core.pushTrace]; rfl)
          · simp [sc', htrace]
          · exact hinj
          · exact henvCorr
          · exact henvwf
          · exact hheapvwf
          · simp [sc', hheapna]
          · simp [sc', noCallFrameReturn]
          · simp only [sc', ExprAddrWF, ValueAddrWF]
          · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
            simp [sc', Flat.convertExpr, Flat.convertValue]
      | none =>
        -- idx needs stepping; obj is already a value
        have hfnv_i : Flat.exprValue? (Flat.convertExpr idx scope envVar envMap st).fst = none :=
          convertExpr_not_value_supported idx hcev_i (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
        -- Extract value sub-step from Flat step
        obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
            Flat.step? { sf with expr := (Flat.convertExpr idx scope envVar envMap st).fst } = some (ev, sa) ∧
            sf' = { expr := (Flat.Expr.getIndex (.lit (Flat.convertValue cv)) sa.expr), env := sa.env, heap := sa.heap,
                    trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
          match hm : Flat.step? { sf with expr := (Flat.convertExpr idx scope envVar envMap st).fst } with
          | some (t, sa) =>
            have hno_core : (∃ addr, cv = .object addr) ∨ (∃ str, cv = .string str) ∨ ((∀ a, cv ≠ .object a) ∧ (∀ s, cv ≠ .string s)) := by
              cases cv with
              | object a => left; exact ⟨a, rfl⟩
              | string s => right; left; exact ⟨s, rfl⟩
              | _ => right; right; exact ⟨fun a => Core.Value.noConfusion, fun s => Core.Value.noConfusion⟩
            rcases hno_core with ⟨addr, rfl⟩ | ⟨str, rfl⟩ | ⟨hno, hns⟩
            · have : Flat.convertValue (.object addr) = .object addr := rfl
              rw [this] at hstep
              have heq := Flat_step?_getIndex_object_step_idx sf addr _ hfnv_i t sa hm
              rw [heq] at hstep; simp at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨sa, rfl, by rw [← hsf'eq]; congr 1⟩
            · have : Flat.convertValue (.string str) = .string str := rfl
              rw [this] at hstep
              have heq := Flat_step?_getIndex_string_step_idx sf str _ hfnv_i t sa hm
              rw [heq] at hstep; simp at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨sa, rfl, by rw [← hsf'eq]; congr 1⟩
            · have hno_flat : ∀ addr, Flat.convertValue cv ≠ .object addr := convertValue_not_object cv hno
              have hns_flat : ∀ str, Flat.convertValue cv ≠ .string str := by
                intro str; cases cv <;> simp [Flat.convertValue] <;> (try exact (hno _ rfl).elim) <;> (try exact (hns _ rfl).elim) <;> exact Flat.Value.noConfusion
              have heq := Flat_step?_getIndex_other_step_idx sf (Flat.convertValue cv) _ hfnv_i hno_flat hns_flat t sa hm
              rw [heq] at hstep; simp at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨sa, rfl, hsf'eq.symm⟩
          | none =>
            have heq := Flat_step?_getIndex_value_none sf (Flat.convertValue cv) _ hfnv_i hm
            rw [heq] at hstep; exact absurd hstep (by simp)
        subst hsf'_eq
        have hdepth : idx.depth < n := by simp [Core.Expr.depth] at hd; omega
        have hncfr_i : noCallFrameReturn idx = true := by
          simp [noCallFrameReturn] at hncfr; exact hncfr
        have hexprwf_i : ExprAddrWF idx sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf.2
        have hcv_wf : ValueAddrWF cv sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf.1
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf',
                ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
          ih_depth idx.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr idx scope envVar envMap st).fst }
            { sc with expr := idx }
            ev sa scope st (Flat.convertExpr idx scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_i hexprwf_i (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
            (by simp)
            ⟨hsubstep⟩
        let sc' : Core.State :=
          ⟨.getIndex (.lit cv) sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
        · show Core.step? sc = some (ev, sc')
          have hsc' : sc = { sc with expr := .getIndex (.lit cv) idx } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core_step?_getIndex_value_step cv idx hcev_i sc.env sc.heap sc.trace sc.funcs sc.callStack ev sc_sub' hcstep_sub
        · simp [sc', htrace, htrace_sub]
        · exact hinj'
        · exact henvCorr'
        · exact henvwf'
        · exact hheapvwf'
        · exact hheapna'
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp only [sc']; simp only [ExprAddrWF]
          have heap_mono := Core_step_heap_size_mono hcstep_sub
          exact ⟨ValueAddrWF_mono hcv_wf heap_mono, hexprwf'⟩
        · refine ⟨st_a, st_a', ?_, hAgreeIn, by rw [hst]; exact hAgreeOut⟩
          simp only [sc', Flat.convertExpr, Flat.convertValue]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported obj hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.getIndex (Flat.convertExpr obj scope envVar envMap st).fst
          (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .getIndex sa.expr (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_getIndex_step sf
            (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.getIndex (Flat.convertExpr obj scope envVar envMap st).fst
              (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : obj.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_arg : noCallFrameReturn obj = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1
      have hexprwf_arg : ExprAddrWF obj sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_arg hexprwf_arg (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.getIndex sc_sub'.expr idx, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .getIndex obj idx } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_getIndex_step _ idx _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
      · simp only [sc']; simp only [ExprAddrWF]; exact ⟨hexprwf', by
            exact ExprAddrWF_mono idx (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) (Core_step_heap_size_mono hcstep_sub)⟩
      · have hidx := convertExpr_state_determined idx scope envVar envMap
            (Flat.convertExpr obj scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
        refine ⟨st_a, (Flat.convertExpr idx scope envVar envMap st_a').snd, ?_, hAgreeIn, ?_⟩
        · simp only [sc', Flat.convertExpr]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
          rw [hidx.1]
        · rw [hst]; exact hidx.2
  | setIndex obj idx value =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv =>
      have hlit : obj = .lit cv := by
        cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr hst
      have hsf_eta : sf = { sf with expr := (Flat.Expr.setIndex (.lit (Flat.convertValue cv))
          (Flat.convertExpr idx scope envVar envMap st).fst
          (Flat.convertExpr value scope envVar envMap
            (Flat.convertExpr idx scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Case split on idx
      cases hcev_i : Core.exprValue? idx with
      | some iv =>
        have hlit_i : idx = .lit iv := by
          cases idx <;> simp [Core.exprValue?] at hcev_i; subst hcev_i; rfl
        subst hlit_i
        simp [Flat.convertExpr] at hfexpr hst
        -- Case split on value
        cases hcev_v : Core.exprValue? value with
        | some vv =>
          -- All three are values
          have hlit_v : value = .lit vv := by
            cases value <;> simp [Core.exprValue?] at hcev_v; subst hcev_v; rfl
          subst hlit_v
          have hcv_i : (Flat.convertExpr (.lit iv) scope envVar envMap st).fst = .lit (Flat.convertValue iv) := by
            simp [Flat.convertExpr]
          have hcv_v : (Flat.convertExpr (.lit vv) scope envVar envMap
              (Flat.convertExpr (.lit iv) scope envVar envMap st).snd).fst = .lit (Flat.convertValue vv) := by
            simp [Flat.convertExpr]
          rw [hcv_i, hcv_v] at hstep
          simp [Flat.convertExpr] at hfexpr hst
          -- Case split: cv is object or not
          have hno_core : (∃ addr, cv = .object addr) ∨ (∀ a, cv ≠ .object a) := by
            cases cv with
            | object a => left; exact ⟨a, rfl⟩
            | _ => right; intro a; exact Core.Value.noConfusion
          rcases hno_core with ⟨addr, rfl⟩ | hno
          · -- Object case: heap mutation
            have : Flat.convertValue (.object addr) = .object addr := rfl
            rw [this] at hstep
            rw [Flat_step?_setIndex_object_both_values] at hstep
            simp only [flatToCoreValue_convertValue, valueToString_convertValue, Prod.mk.injEq, Option.some.injEq] at hstep
            obtain ⟨hev, hsf'⟩ := hstep; subst hev; subst hsf'
            have haddr_wf : addr < sc.heap.objects.size := by
              simp [ExprAddrWF, ValueAddrWF] at hexprwf; exact hexprwf.1
            have hvv_wf : ValueAddrWF vv sc.heap.objects.size := by
              simp [ExprAddrWF, ValueAddrWF] at hexprwf; exact hexprwf.2.2
            let propName := Core.valueToString iv
            let coreHeap' := match sc.heap.objects[addr]? with
              | some (props : List (Core.PropName × Core.Value)) =>
                  let updated := if props.any (fun (kv : Core.PropName × Core.Value) => kv.fst == propName)
                    then props.map (fun (kv : Core.PropName × Core.Value) => if kv.fst == propName then (propName, vv) else kv)
                    else props ++ [(propName, vv)]
                  { sc.heap with objects := sc.heap.objects.set! addr updated }
              | none => sc.heap
            let sc' : Core.State := ⟨.lit vv, sc.env, coreHeap',
              sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
            refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
            · -- Core step
              have hsc' : sc = { sc with expr := .setIndex (.lit (.object addr)) (.lit iv) (.lit vv) } := by
                obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
              rw [hsc']
              have := Core.step?_setIndex_object_val addr iv vv sc.env sc.heap sc.trace sc.funcs sc.callStack
              simp only [Core.pushTrace, sc', coreHeap', propName] at this ⊢; exact this
            · -- trace
              simp [sc', htrace]
            · -- HeapInj: both heaps do same set! at addr
              simp only [sc', coreHeap', propName]
              rw [heapObjectAt?_eq, ← HeapInj_get hinj haddr_wf]
              cases sc.heap.objects[addr]? with
              | none => exact hinj
              | some props => exact HeapInj_set_same hinj addr haddr_wf _
            · -- EnvCorrInj
              exact henvCorr
            · -- EnvAddrWF
              simp only [sc', coreHeap', propName]
              cases sc.heap.objects[addr]? with
              | none => exact henvwf
              | some props => exact EnvAddrWF_mono henvwf (by simp [size_set!])
            · -- HeapValuesWF
              simp only [sc', coreHeap', propName]
              cases hprops : sc.heap.objects[addr]? with
              | none => exact hheapvwf
              | some props =>
                apply HeapValuesWF_set_at hheapvwf
                intro kv hkv
                by_cases hany : props.any (fun kv => kv.fst == Core.valueToString iv)
                · simp only [propName, hany, ↓reduceIte] at hkv
                  obtain ⟨orig, horig, rfl⟩ := List.mem_map.mp hkv
                  split
                  · simp only; exact hvv_wf
                  · exact hheapvwf addr haddr_wf props hprops orig horig
                · simp only [propName, hany, Bool.false_eq_true, ↓reduceIte] at hkv
                  rcases List.mem_append.mp hkv with h | h
                  · exact hheapvwf addr haddr_wf props hprops kv h
                  · rw [List.mem_singleton.mp h]; simp only; exact hvv_wf
            · -- hheapna
              simp only [sc', coreHeap', propName]
              split
              · simp [Array.size_setIfInBounds, hheapna]
              · exact hheapna
            · -- noCallFrameReturn
              simp [sc', noCallFrameReturn]
            · -- ExprAddrWF
              have hvv_wf' : ValueAddrWF vv sc.heap.objects.size := by
                simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2
              have hsize : coreHeap'.objects.size = sc.heap.objects.size := by
                simp only [coreHeap', propName]
                split
                · simp [size_set!]
                · rfl
              simp only [sc', ExprAddrWF, ValueAddrWF]
              rw [hsize]
              exact hvv_wf'
            · -- CCState threading
              refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
              simp [sc', Flat.convertExpr, Flat.convertValue]
          · -- Non-object case: heap unchanged, return value
            have hno_flat : ∀ addr, Flat.convertValue cv ≠ .object addr :=
              convertValue_not_object cv hno
            rw [Flat_step?_setIndex_nonobject_both_values _ _ _ _ hno_flat] at hstep
            simp at hstep; obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
            let sc' : Core.State := ⟨.lit vv, sc.env, sc.heap,
              sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
            refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
            · have hsc' : sc = { sc with expr := .setIndex (.lit cv) (.lit iv) (.lit vv) } := by
                obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
              rw [hsc']
              have := Core.step?_setIndex_nonobject_val cv iv vv sc.env sc.heap sc.trace sc.funcs sc.callStack hno
              simp only [Core.pushTrace, sc'] at this ⊢; exact this
            · simp [sc', htrace]
            · exact hinj
            · exact henvCorr
            · exact henvwf
            · exact hheapvwf
            · simp [sc', hheapna]
            · simp [sc', noCallFrameReturn]
            · have hvv_wf' : ValueAddrWF vv sc.heap.objects.size := by
                simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2
              simp only [sc', ExprAddrWF, ValueAddrWF]; exact hvv_wf'
            · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
              simp [sc', Flat.convertExpr, Flat.convertValue]
        | none =>
          -- value needs stepping; obj+idx are values
          -- Simplify: converting a literal doesn't change CCState
          have hst_iv : (Flat.convertExpr (.lit iv) scope envVar envMap st).snd = st := by
            simp [Flat.convertExpr]
          have hcv_i : (Flat.convertExpr (.lit iv) scope envVar envMap st).fst = .lit (Flat.convertValue iv) := by
            simp [Flat.convertExpr]
          rw [hcv_i, hst_iv] at hstep
          have hfnv_v : Flat.exprValue? (Flat.convertExpr value scope envVar envMap st).fst = none :=
            convertExpr_not_value_supported value hcev_v (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
          -- Extract value sub-step from Flat step
          obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
              Flat.step? { sf with expr := (Flat.convertExpr value scope envVar envMap st).fst } = some (ev, sa) ∧
              sf' = { expr := .setIndex (.lit (Flat.convertValue cv)) (.lit (Flat.convertValue iv)) sa.expr,
                      env := sa.env, heap := sa.heap,
                      trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
            match hm : Flat.step? { sf with expr := (Flat.convertExpr value scope envVar envMap st).fst } with
            | some (t, sa) =>
              have hno_core : (∃ addr, cv = .object addr) ∨ (∀ a, cv ≠ .object a) := by
                cases cv with
                | object a => left; exact ⟨a, rfl⟩
                | _ => right; intro a; exact Core.Value.noConfusion
              rcases hno_core with ⟨addr, rfl⟩ | hno
              · have : Flat.convertValue (.object addr) = .object addr := rfl
                rw [this] at hstep
                have heq := Flat_step?_setIndex_object_step_value sf addr (Flat.convertValue iv) _ hfnv_v t sa hm
                rw [heq] at hstep; simp at hstep
                obtain ⟨rfl, hsf'eq⟩ := hstep
                exact ⟨sa, rfl, hsf'eq.symm⟩
              · have hno_flat : ∀ addr, Flat.convertValue cv ≠ .object addr := convertValue_not_object cv hno
                have heq := Flat_step?_setIndex_nonobject_step_value sf (Flat.convertValue cv) (Flat.convertValue iv) _ hno_flat hfnv_v t sa hm
                rw [heq] at hstep; simp at hstep
                obtain ⟨rfl, hsf'eq⟩ := hstep
                exact ⟨sa, rfl, hsf'eq.symm⟩
            | none =>
              have heq := Flat_step?_setIndex_value_value_none sf (Flat.convertValue cv) (Flat.convertValue iv) _ hfnv_v hm
              rw [heq] at hstep; exact absurd hstep (by simp)
          subst hsf'_eq
          have hdepth : value.depth < n := by simp [Core.Expr.depth] at hd; omega
          have hncfr_v : noCallFrameReturn value = true := by
            simp [noCallFrameReturn] at hncfr; exact hncfr
          have hexprwf_v : ExprAddrWF value sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2
          have hcv_wf : ValueAddrWF cv sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf.1
          have hiv_wf : ValueAddrWF iv sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf.2.1
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf',
                  ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
            ih_depth value.depth hdepth envVar envMap injMap
              { sf with expr := (Flat.convertExpr value scope envVar envMap st).fst }
              { sc with expr := value }
              ev sa scope st (Flat.convertExpr value scope envVar envMap st).snd
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_v hexprwf_v (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
              (by simp)
              ⟨hsubstep⟩
          let sc' : Core.State :=
            ⟨.setIndex (.lit cv) (.lit iv) sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · show Core.step? sc = some (ev, sc')
            have hsc' : sc = { sc with expr := .setIndex (.lit cv) (.lit iv) value } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc']
            exact Core_step?_setIndex_value_step_value cv iv value hcev_v sc.env sc.heap sc.trace sc.funcs sc.callStack ev sc_sub' hcstep_sub
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · exact hheapna'
          · simp [sc', noCallFrameReturn]; exact hncfr'
          · simp only [sc']; simp only [ExprAddrWF]
            have heap_mono := Core_step_heap_size_mono hcstep_sub
            exact ⟨ValueAddrWF_mono hcv_wf heap_mono, ValueAddrWF_mono hiv_wf heap_mono, hexprwf'⟩
          · refine ⟨st_a, st_a', ?_, hAgreeIn, ?_⟩
            · simp only [sc', Flat.convertExpr, Flat.convertValue]
              rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
              rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
            · subst hst; exact hAgreeOut
      | none =>
        -- idx needs stepping; obj is already a value
        have hfnv_i : Flat.exprValue? (Flat.convertExpr idx scope envVar envMap st).fst = none :=
          convertExpr_not_value_supported idx hcev_i (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
        -- Extract idx sub-step from Flat step
        obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
            Flat.step? { sf with expr := (Flat.convertExpr idx scope envVar envMap st).fst } = some (ev, sa) ∧
            sf' = { expr := .setIndex (.lit (Flat.convertValue cv)) sa.expr
                      (Flat.convertExpr value scope envVar envMap
                        (Flat.convertExpr idx scope envVar envMap st).snd).fst,
                    env := sa.env, heap := sa.heap,
                    trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
          match hm : Flat.step? { sf with expr := (Flat.convertExpr idx scope envVar envMap st).fst } with
          | some (t, sa) =>
            have hno_core : (∃ addr, cv = .object addr) ∨ (∀ a, cv ≠ .object a) := by
              cases cv with
              | object a => left; exact ⟨a, rfl⟩
              | _ => right; intro a; exact Core.Value.noConfusion
            rcases hno_core with ⟨addr, rfl⟩ | hno
            · have : Flat.convertValue (.object addr) = .object addr := rfl
              rw [this] at hstep
              have heq := Flat_step?_setIndex_object_step_idx sf addr _ (Flat.convertExpr value scope envVar envMap
                (Flat.convertExpr idx scope envVar envMap st).snd).fst hfnv_i t sa hm
              rw [heq] at hstep; simp at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨sa, rfl, hsf'eq.symm⟩
            · have hno_flat : ∀ addr, Flat.convertValue cv ≠ .object addr := convertValue_not_object cv hno
              have heq := Flat_step?_setIndex_nonobject_step_idx sf (Flat.convertValue cv) _
                (Flat.convertExpr value scope envVar envMap
                  (Flat.convertExpr idx scope envVar envMap st).snd).fst hno_flat hfnv_i t sa hm
              rw [heq] at hstep; simp at hstep
              obtain ⟨rfl, hsf'eq⟩ := hstep
              exact ⟨sa, rfl, hsf'eq.symm⟩
          | none =>
            have heq := Flat_step?_setIndex_value_idx_none sf (Flat.convertValue cv) _ (Flat.convertExpr value scope envVar envMap
              (Flat.convertExpr idx scope envVar envMap st).snd).fst hfnv_i hm
            rw [heq] at hstep; exact absurd hstep (by simp)
        subst hsf'_eq
        have hdepth : idx.depth < n := by simp [Core.Expr.depth] at hd; omega
        have hncfr_i : noCallFrameReturn idx = true := by
          simp [noCallFrameReturn] at hncfr; exact hncfr.1
        have hexprwf_i : ExprAddrWF idx sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf.2.1
        have hcv_wf : ValueAddrWF cv sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf.1
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf',
                ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
          ih_depth idx.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr idx scope envVar envMap st).fst }
            { sc with expr := idx }
            ev sa scope st (Flat.convertExpr idx scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_i hexprwf_i (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
            (by simp)
            ⟨hsubstep⟩
        let sc' : Core.State :=
          ⟨.setIndex (.lit cv) sc_sub'.expr value, sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
        · show Core.step? sc = some (ev, sc')
          have hsc' : sc = { sc with expr := .setIndex (.lit cv) idx value } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core_step?_setIndex_value_step_idx cv idx value hcev_i sc.env sc.heap sc.trace sc.funcs sc.callStack ev sc_sub' hcstep_sub
        · simp [sc', htrace, htrace_sub]
        · exact hinj'
        · exact henvCorr'
        · exact henvwf'
        · exact hheapvwf'
        · exact hheapna'
        · simp [sc', noCallFrameReturn]; exact ⟨hncfr', by
            simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
        · simp only [sc']; simp only [ExprAddrWF]
          have heap_mono := Core_step_heap_size_mono hcstep_sub
          refine ⟨ValueAddrWF_mono hcv_wf heap_mono, hexprwf', ?_⟩
          exact ExprAddrWF_mono value (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2) heap_mono
        · have hval := convertExpr_state_determined value scope envVar envMap
              (Flat.convertExpr idx scope envVar envMap st).snd
              st_a' hAgreeOut.1 hAgreeOut.2
          refine ⟨st_a, (Flat.convertExpr value scope envVar envMap st_a').snd, ?_, hAgreeIn, ?_⟩
          · simp only [sc', Flat.convertExpr]
            rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
            rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
            rw [hval.1]
          · rw [hst]; exact hval.2
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported obj hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.setIndex (Flat.convertExpr obj scope envVar envMap st).fst
          (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst
          (Flat.convertExpr value scope envVar envMap
            (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .setIndex sa.expr
                    (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst
                    (Flat.convertExpr value scope envVar envMap
                      (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_setIndex_obj_step sf
            (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst
            (Flat.convertExpr value scope envVar envMap
              (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.setIndex (Flat.convertExpr obj scope envVar envMap st).fst
              (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).fst
              (Flat.convertExpr value scope envVar envMap
                (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : obj.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_obj : noCallFrameReturn obj = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1.1
      have hexprwf_obj : ExprAddrWF obj sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_obj hexprwf_obj (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.setIndex sc_sub'.expr idx value, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .setIndex obj idx value } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_setIndex_obj_step _ _ _ _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact ⟨⟨hncfr', by
          simp [noCallFrameReturn] at hncfr; exact hncfr.1.2⟩, by
          simp [noCallFrameReturn] at hncfr; exact hncfr.2⟩
      · simp only [sc']; simp only [ExprAddrWF]; refine ⟨hexprwf', ?_, ?_⟩
        · exact ExprAddrWF_mono idx (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.1) (Core_step_heap_size_mono hcstep_sub)
        · exact ExprAddrWF_mono value (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2) (Core_step_heap_size_mono hcstep_sub)
      · have hidx := convertExpr_state_determined idx scope envVar envMap
            (Flat.convertExpr obj scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
        have hval := convertExpr_state_determined value scope envVar envMap
            (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).snd).snd
            (Flat.convertExpr idx scope envVar envMap st_a').snd hidx.2.1 hidx.2.2
        refine ⟨st_a, (Flat.convertExpr value scope envVar envMap
            (Flat.convertExpr idx scope envVar envMap st_a').snd).snd, ?_, hAgreeIn, ?_⟩
        · simp only [sc', Flat.convertExpr]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst = sa.expr from (congrArg Prod.fst hconv').symm]
          rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' from (congrArg Prod.snd hconv').symm]
          rw [hidx.1, hval.1]
        · rw [hst]; exact hval.2
  | deleteProp obj prop =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv =>
      have hlit : obj = .lit cv := by
        cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr hst
      have hsf_eta : sf = { sf with expr := .deleteProp (.lit (Flat.convertValue cv)) prop } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Case split: cv is object or not
      have hno_core : (∃ addr, cv = .object addr) ∨ (∀ a, cv ≠ .object a) := by
        cases cv with
        | object a => left; exact ⟨a, rfl⟩
        | _ => right; intro a; exact Core.Value.noConfusion
      rcases hno_core with ⟨addr, rfl⟩ | hno
      · -- Object case: heap mutation (filter props at addr)
        have : Flat.convertValue (.object addr) = .object addr := rfl
        rw [this] at hstep hsf_eta hfexpr
        rw [Flat_step?_deleteProp_object_value] at hstep
        simp at hstep; obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        have haddr_wf : addr < sc.heap.objects.size := by
          simp [ExprAddrWF, ValueAddrWF] at hexprwf; exact hexprwf
        -- Build core result state
        let coreHeap' := match sc.heap.objects[addr]? with
          | some props =>
              { sc.heap with objects := sc.heap.objects.set! addr (props.filter (fun kv => kv.fst != prop)) }
          | none => sc.heap
        let sc' : Core.State := ⟨.lit (.bool true), sc.env, coreHeap',
          sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · -- Core step
          have hsc' : sc = { sc with expr := .deleteProp (.lit (.object addr)) prop } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          have := Core.step?_deleteProp_object_val addr prop sc.env sc.heap sc.trace sc.funcs sc.callStack
          simp only [Core.pushTrace, sc', coreHeap'] at this ⊢; exact this
        · -- trace
          simp [sc', htrace]
        · -- HeapInj: both heaps do same set! at addr with filtered props
          simp only [sc', coreHeap']
          rw [heapObjectAt?_eq, ← HeapInj_get hinj haddr_wf]
          cases sc.heap.objects[addr]? with
          | none => exact hinj
          | some props => exact HeapInj_set_same hinj addr haddr_wf _
        · -- EnvCorrInj
          exact henvCorr
        · -- EnvAddrWF
          simp only [sc', coreHeap']
          cases sc.heap.objects[addr]? with
          | none => exact henvwf
          | some props =>
            exact EnvAddrWF_mono henvwf (by simp [size_set!])
        · -- HeapValuesWF
          simp only [sc', coreHeap']
          cases hprops : sc.heap.objects[addr]? with
          | none => exact hheapvwf
          | some props =>
            exact HeapValuesWF_set_at hheapvwf (fun kv hkv =>
              ValueAddrWF_mono
                (hheapvwf addr haddr_wf props hprops kv ((List.mem_filter.mp hkv).1))
                (by simp [size_set!]))
        · -- hheapna
          simp only [sc', coreHeap']
          split
          · simp [Array.size_setIfInBounds, hheapna]
          · exact hheapna
        · -- noCallFrameReturn
          simp [sc', noCallFrameReturn]
        · -- ExprAddrWF
          simp only [sc', ExprAddrWF, ValueAddrWF]
        · -- CCState threading
          refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
          simp [sc', Flat.convertExpr, Flat.convertValue]
      · -- Non-object case: heap unchanged, both return .lit (.bool true)
        have hno_flat : ∀ addr, Flat.convertValue cv ≠ .object addr :=
          convertValue_not_object cv hno
        rw [Flat_step?_deleteProp_nonobject_value _ _ _ hno_flat] at hstep
        simp at hstep; obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State := ⟨.lit (.bool true), sc.env, sc.heap,
          sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · -- Core step
          have hsc' : sc = { sc with expr := .deleteProp (.lit cv) prop } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          have := Core.step?_deleteProp_nonobject_val cv prop sc.env sc.heap sc.trace sc.funcs sc.callStack hno
          simp only [Core.pushTrace, sc'] at this ⊢; exact this
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF, ValueAddrWF]
        · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
          simp [sc', Flat.convertExpr, Flat.convertValue]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported obj hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .deleteProp (Flat.convertExpr obj scope envVar envMap st).fst prop } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .deleteProp sa.expr prop, env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_deleteProp_step sf prop _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .deleteProp (Flat.convertExpr obj scope envVar envMap st).fst prop } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : obj.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_arg : noCallFrameReturn obj = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr
      have hexprwf_arg : ExprAddrWF obj sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_arg hexprwf_arg (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.deleteProp sc_sub'.expr prop, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .deleteProp obj prop } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_deleteProp_step _ prop _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | typeof arg =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? arg with
    | some cv =>
      have hlit : arg = .lit cv := by
        cases arg <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr
      have hsf_eta : sf = { sf with expr := .typeof (.lit (Flat.convertValue cv)) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_typeof_value] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let coreResult := match cv with
        | .undefined => "undefined" | .null => "object" | .bool _ => "boolean"
        | .number _ => "number" | .string _ => "string" | .function _ => "function"
        | .object _ => "object"
      let sc' : Core.State := ⟨.lit (.string coreResult), sc.env, sc.heap,
        sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · have hsc' : sc = { sc with expr := .typeof (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; simp [Core.step?, Core.exprValue?, Core.pushTrace]
        simp only [sc', coreResult]; cases cv <;> rfl
      · simp only [sc']; simp [htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp only [sc']; simp [noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF, ValueAddrWF, coreResult]
      · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
        simp only [sc']; simp [Flat.convertExpr, Flat.convertValue, coreResult]
        cases cv <;> simp [Flat.convertValue]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr arg scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported arg hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .typeof (Flat.convertExpr arg scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .typeof sa.expr, env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_typeof_step sf _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .typeof (Flat.convertExpr arg scope envVar envMap st).fst } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : arg.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_arg : noCallFrameReturn arg = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr
      have hexprwf_arg : ExprAddrWF arg sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth arg.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst }
          { sc with expr := arg }
          ev sa scope st (Flat.convertExpr arg scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_arg hexprwf_arg (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.typeof sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .typeof arg } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_typeof_step _ _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | objectLit props =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcfnv : Core.firstNonValueProp props with
    | none =>
      -- All props are values: both Core and Flat allocate an object on heap.
      have hffnv := convertPropList_firstNonValueProp_none props scope envVar envMap st hcfnv
      have ⟨vs, hvs⟩ := firstNonValueProp_none_implies_values _ hffnv
      have hsf_eta : sf = { sf with expr := .objectLit (Flat.convertPropList props scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat.step?_objectLit_allValues _ _ _ hvs] at hstep
      simp only [Prod.mk.injEq, Option.some.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      have hna_eq : sc.heap.nextAddr = sf.heap.nextAddr := hinj.2.1
      have hfmatch := convertPropList_filterMap_eq props scope envVar envMap st hcfnv
      have hst_eq : (Flat.convertPropList props scope envVar envMap st).snd = st :=
        convertPropList_state_none props scope envVar envMap st hcfnv
      let caddr := sc.heap.nextAddr
      let cheapProps := props.filterMap fun (k, e) =>
        match Core.exprValue? e with | some v => some (k, v) | none => none
      let cheap' : Core.Heap := { objects := sc.heap.objects.push cheapProps, nextAddr := caddr + 1 }
      let sc' : Core.State := ⟨.lit (.object caddr), sc.env, cheap',
        sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      have hcstep : Core.step? sc = some (.silent, sc') := by
        have hsc' : sc = { sc with expr := .objectLit props } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        have := Core.step?_objectLit_val props sc.env sc.heap sc.trace sc.funcs sc.callStack hcfnv
        simp only [Core.pushTrace, sc', cheap', cheapProps, caddr] at this ⊢; exact this
      have hinj' : HeapInj injMap cheap' ⟨sf.heap.objects.push
          ((Flat.convertPropList props scope envVar envMap st).fst.filterMap fun (k, e) =>
            match Flat.exprValue? e with | some v => some (k, Flat.flatToCoreValue v) | none => none),
          sf.heap.nextAddr + 1⟩ := by
        simp only [cheap', cheapProps, caddr]
        rw [← hfmatch]; exact HeapInj_alloc_both hinj _
      have hheapvwf' : HeapValuesWF cheap' := by
        intro addr haddr props' hprops' kv hkv
        simp only [cheap', cheapProps, caddr, Array.size_push] at haddr
        rw [Array.getElem?_push] at hprops'
        split at hprops'
        · simp only [Option.some.injEq] at hprops'; subst hprops'
          have hwf_props : ExprAddrPropListWF props sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf
          obtain ⟨⟨k, e⟩, hmem, hfm⟩ := List.mem_filterMap.mp hkv
          cases he : Core.exprValue? e with
          | none => simp [he] at hfm
          | some v =>
            simp [he] at hfm; subst hfm
            have hlit : e = .lit v := by cases e <;> simp [Core.exprValue?] at he; subst he; rfl
            subst hlit
            suffices ∀ (ps : List (String × Core.Expr)),
              ExprAddrPropListWF ps sc.heap.objects.size →
              (k, Core.Expr.lit v) ∈ ps → ValueAddrWF v sc.heap.objects.size from
              ValueAddrWF_mono (this props hwf_props hmem) (by simp only [cheap', Array.size_push]; omega)
            intro ps hps hmem'
            induction ps with
            | nil => simp at hmem'
            | cons p ps' ih =>
              simp [ExprAddrPropListWF] at hps
              rcases List.mem_cons.mp hmem' with rfl | h
              · simp only [ExprAddrWF, ValueAddrWF] at hps; exact hps.1
              · exact ih hps.2 h
        · next hne =>
          have haddr' : addr < sc.heap.objects.size := by omega
          exact ValueAddrWF_mono (hheapvwf addr haddr' props' hprops' kv hkv) (by simp only [cheap', Array.size_push]; omega)
      refine ⟨injMap, sc', ⟨hcstep⟩, ?trace_, ?hinj_, ?envcorr_, ?envwf_, ?hvwf_,
        ?hna_, ?ncfr_, ?ewf_, ?ccst_, hfuncCorr⟩
      case trace_ => simp [sc', htrace]
      case hinj_ => exact hinj'
      case envcorr_ => exact henvCorr
      case envwf_ => exact EnvAddrWF_mono henvwf (by simp only [sc', cheap', Array.size_push]; omega)
      case hvwf_ => exact hheapvwf'
      case hna_ => simp only [sc', cheap', caddr, Array.size_push, hheapna]
      case ncfr_ => simp [sc', noCallFrameReturn]
      case ewf_ => simp only [sc', ExprAddrWF, ValueAddrWF, cheap', caddr, Array.size_push]; rw [hheapna]; omega
      case ccst_ => exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue, caddr, hna_eq],
        ⟨rfl, rfl⟩, by rw [hst, hst_eq]; exact ⟨rfl, rfl⟩⟩
    | some val =>
      obtain ⟨done_c, propName_c, target_c, rest_c⟩ := val
      have htarget_not_lit := Core.firstNonValueProp_not_lit hcfnv
      have htarget_novalue : Core.exprValue? target_c = none := by
        cases target_c with
        | lit v => exact absurd rfl (htarget_not_lit v)
        | _ => rfl
      have htarget_supp : target_c.supported = true :=
        propListSupported_firstNonValueProp_target hcfnv (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
      have hffnv := convertPropList_firstNonValueProp_some props scope envVar envMap st
          done_c propName_c target_c rest_c hcfnv htarget_novalue htarget_supp
      have hfnv_target : Flat.exprValue? (Flat.convertExpr target_c scope envVar envMap
          (Flat.convertPropList done_c scope envVar envMap st).snd).fst = none :=
        convertExpr_not_value_supported target_c htarget_novalue htarget_supp scope envVar envMap _
      have hsf_eta : sf = { sf with expr := .objectLit (Flat.convertPropList props scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
          Flat.step? { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertPropList done_c scope envVar envMap st).snd).fst } = some (ev, sa) ∧
          sf' = { expr := .objectLit ((Flat.convertPropList done_c scope envVar envMap st).fst ++
                    [(propName_c, sa.expr)] ++
                    (Flat.convertPropList rest_c scope envVar envMap
                      (Flat.convertExpr target_c scope envVar envMap
                        (Flat.convertPropList done_c scope envVar envMap st).snd).snd).fst),
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        have hvals := valuesFromExprList_none_of_firstNonValueProp hffnv
        match hm : Flat.step? { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertPropList done_c scope envVar envMap st).snd).fst } with
        | some (t, se) =>
          have heq := Flat_step?_objectLit_step sf _ _ propName_c _ _ hvals hffnv t se hm
          rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨se, rfl, hsf'eq.symm⟩
        | none =>
          have heq := Flat_step?_objectLit_none sf _ _ propName_c _ _ hvals hffnv hm
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : target_c.depth < n := by
        simp [Core.Expr.depth] at hd
        have := Core.firstNonValueProp_depth hcfnv; omega
      have ⟨hncfr_done, hncfr_target, hncfr_rest⟩ :=
        firstNonValueProp_propListNoCallFrameReturn hcfnv (by simp [noCallFrameReturn] at hncfr; exact hncfr)
      have hexprwf_target : ExprAddrWF target_c sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf
        exact ExprAddrPropListWF_firstNonValueProp_target hcfnv hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf',
              hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth target_c.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertPropList done_c scope envVar envMap st).snd).fst }
          { sc with expr := target_c }
          ev sa scope
          (Flat.convertPropList done_c scope envVar envMap st).snd
          (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertPropList done_c scope envVar envMap st).snd).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_target hexprwf_target htarget_supp
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.objectLit (done_c ++ [(propName_c, sc_sub'.expr)] ++ rest_c),
         sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · -- Core.step?
        show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .objectLit props } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        have hcstep_anon : Core.step? ⟨target_c, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ =
            some (ev, sc_sub') := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; exact hcstep_sub
        have hcore_step := Core.step_objectLit_step_prop props sc.env sc.heap sc.trace sc.funcs sc.callStack
            done_c propName_c target_c rest_c hcfnv ev sc_sub' hcstep_anon
        simp only [Core.pushTrace] at hcore_step
        have : sc' = { sc_sub' with
          expr := .objectLit (done_c ++ [(propName_c, sc_sub'.expr)] ++ rest_c),
          trace := sc.trace ++ [ev] } := by simp [sc']
        rw [this]; exact hcore_step
      · -- trace
        simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · -- noCallFrameReturn
        simp only [sc', noCallFrameReturn]
        rw [propListNoCallFrameReturn_append, propListNoCallFrameReturn_append]
        simp [propListNoCallFrameReturn, hncfr', hncfr_done, hncfr_rest]
      · -- ExprAddrWF objectLit: reconstruct from IH
        simp only [sc', ExprAddrWF]
        exact ExprAddrPropListWF_firstNonValueProp_reconstruct hcfnv
          (by simp [ExprAddrWF] at hexprwf; exact hexprwf) hexprwf'
          (Core_step_heap_size_mono hcstep_sub)
      · -- CCState agreement (objectLit sub-step)
        -- IH gives: hconv' at st_a, hAgreeIn : CCStateAgree (convertPropList done_c st).snd st_a
        --           hAgreeOut : CCStateAgree (convertExpr target_c (convertPropList done_c st).snd).snd st_a'
        have hsub_det := convertExpr_state_determined sc_sub'.expr scope envVar envMap
          (Flat.convertPropList done_c scope envVar envMap st).snd st_a hAgreeIn.1 hAgreeIn.2
        have hsa_fst : (Flat.convertExpr sc_sub'.expr scope envVar envMap
            (Flat.convertPropList done_c scope envVar envMap st).snd).fst = sa.expr :=
          hsub_det.1.trans (congrArg Prod.fst hconv').symm
        have hsa_snd_eq : (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' :=
          (congrArg Prod.snd hconv').symm
        have hstate_sub_agree : CCStateAgree
            (Flat.convertExpr sc_sub'.expr scope envVar envMap
              (Flat.convertPropList done_c scope envVar envMap st).snd).snd st_a' :=
          ⟨hsub_det.2.1.trans (hsa_snd_eq ▸ rfl), hsub_det.2.2.trans (hsa_snd_eq ▸ rfl)⟩
        have hrest_in_agree : CCStateAgree
            (Flat.convertExpr sc_sub'.expr scope envVar envMap
              (Flat.convertPropList done_c scope envVar envMap st).snd).snd
            (Flat.convertExpr target_c scope envVar envMap
              (Flat.convertPropList done_c scope envVar envMap st).snd).snd :=
          ⟨hstate_sub_agree.1.trans hAgreeOut.1.symm, hstate_sub_agree.2.trans hAgreeOut.2.symm⟩
        have hrest_det := convertPropList_state_determined rest_c scope envVar envMap
          _ _ hrest_in_agree.1 hrest_in_agree.2
        refine ⟨st, (Flat.convertPropList (done_c ++ [(propName_c, sc_sub'.expr)] ++ rest_c) scope envVar envMap st).snd,
          ?_, ⟨rfl, rfl⟩, ?_⟩
        · -- Conversion expression matches sf'.expr
          simp only [sc', Flat.convertExpr]
          congr 1
          rw [convertPropList_append, convertPropList_append, convertPropList_append_snd]
          simp only [Flat.convertPropList]
          rw [hsa_fst, hrest_det.1]
        · -- Output state agreement
          have hprops := firstNonValueProp_decompose hcfnv
          rw [hst, hprops]
          have h_lhs := convertPropList_append_snd (done_c ++ [(propName_c, target_c)]) rest_c scope envVar envMap st
          have h_lhs2 := convertPropList_append_snd done_c [(propName_c, target_c)] scope envVar envMap st
          have h_rhs := convertPropList_append_snd (done_c ++ [(propName_c, sc_sub'.expr)]) rest_c scope envVar envMap st
          have h_rhs2 := convertPropList_append_snd done_c [(propName_c, sc_sub'.expr)] scope envVar envMap st
          simp only [h_lhs, h_lhs2, h_rhs, h_rhs2, Flat.convertPropList]
          exact ⟨hrest_det.2.1.symm, hrest_det.2.2.symm⟩
  | arrayLit elems =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcfnv : Core.firstNonValueExpr elems with
    | none =>
      -- All elements are values: both Core and Flat allocate an array on heap.
      have hffnv := convertExprList_firstNonValueExpr_none elems scope envVar envMap st hcfnv
      have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values _ hffnv
      have hsf_eta : sf = { sf with expr := .arrayLit (Flat.convertExprList elems scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat.step?_arrayLit_allValues _ _ _ hvs] at hstep
      simp only [Prod.mk.injEq, Option.some.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      have hna_eq : sc.heap.nextAddr = sf.heap.nextAddr := hinj.2.1
      have hfmatch := convertExprList_zipIdx_filterMap_eq_mkIndexedProps elems 0 scope envVar envMap st hcfnv
      have hst_eq : (Flat.convertExprList elems scope envVar envMap st).snd = st :=
        convertExprList_state_none elems scope envVar envMap st hcfnv
      let caddr := sc.heap.nextAddr
      let cheapProps := Core.mkIndexedProps 0 elems
      let cheap' : Core.Heap := { objects := sc.heap.objects.push cheapProps, nextAddr := caddr + 1 }
      let sc' : Core.State := ⟨.lit (.object caddr), sc.env, cheap',
        sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      have hcstep : Core.step? sc = some (.silent, sc') := by
        have hsc' : sc = { sc with expr := .arrayLit elems } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        have := Core.step?_arrayLit_val elems sc.env sc.heap sc.trace sc.funcs sc.callStack hcfnv
        simp only [Core.pushTrace, sc', cheap', cheapProps, caddr] at this ⊢; exact this
      have hinj' : HeapInj injMap cheap' ⟨sf.heap.objects.push
          ((Flat.convertExprList elems scope envVar envMap st).fst.zipIdx.filterMap fun (e, i) =>
            match Flat.exprValue? e with | some v => some (toString i, Flat.flatToCoreValue v) | none => none),
          sf.heap.nextAddr + 1⟩ := by
        simp only [cheap', cheapProps, caddr]
        rw [← hfmatch]; exact HeapInj_alloc_both hinj _
      have hheapvwf' : HeapValuesWF cheap' := by
        intro addr haddr props' hprops' kv hkv
        simp only [cheap', cheapProps, caddr, Array.size_push] at haddr
        rw [Array.getElem?_push] at hprops'
        split at hprops'
        · simp only [Option.some.injEq] at hprops'; subst hprops'
          have hwf_elems : ExprAddrListWF elems sc.heap.objects.size := by
            simp [ExprAddrWF] at hexprwf; exact hexprwf
          suffices ∀ (es' : List Core.Expr) (idx : Nat),
            ExprAddrListWF es' sc.heap.objects.size →
            Core.firstNonValueExpr es' = none →
            ∀ kv' ∈ Core.mkIndexedProps idx es', ValueAddrWF kv'.2 sc.heap.objects.size from
            ValueAddrWF_mono (this elems 0 hwf_elems hcfnv kv hkv) (by simp only [cheap', Array.size_push]; omega)
          intro es' idx hes' hfnv kv' hkv'
          induction es' generalizing idx with
          | nil => simp [Core.mkIndexedProps] at hkv'
          | cons e' es'' ih =>
            cases e' with
            | lit w =>
              simp [Core.mkIndexedProps] at hkv'
              rcases hkv' with rfl | hmem
              · simp only [ExprAddrListWF, ExprAddrWF] at hes'; exact hes'.1
              · have hfnv' : Core.firstNonValueExpr es'' = none := by
                  unfold Core.firstNonValueExpr at hfnv
                  cases hrest : Core.firstNonValueExpr es'' with
                  | none => rfl
                  | some _ => simp [hrest] at hfnv
                simp only [ExprAddrListWF] at hes'
                exact ih (idx + 1) hes'.2 hfnv' hmem
            | _ => simp [Core.firstNonValueExpr] at hfnv
        · next hne =>
          have haddr' : addr < sc.heap.objects.size := by omega
          exact ValueAddrWF_mono (hheapvwf addr haddr' props' hprops' kv hkv) (by simp only [cheap', Array.size_push]; omega)
      refine ⟨injMap, sc', ⟨hcstep⟩, ?trace_, ?hinj_, ?envcorr_, ?envwf_, ?hvwf_,
        ?hna_, ?ncfr_, ?ewf_, ?ccst_, hfuncCorr⟩
      case trace_ => simp [sc', htrace]
      case hinj_ => exact hinj'
      case envcorr_ => exact henvCorr
      case envwf_ => exact EnvAddrWF_mono henvwf (by simp only [sc', cheap', Array.size_push]; omega)
      case hvwf_ => exact hheapvwf'
      case hna_ => simp only [sc', cheap', caddr, Array.size_push, hheapna]
      case ncfr_ => simp [sc', noCallFrameReturn]
      case ewf_ => simp only [sc', ExprAddrWF, ValueAddrWF, cheap', caddr, Array.size_push]; rw [hheapna]; omega
      case ccst_ => exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue, caddr, hna_eq],
        ⟨rfl, rfl⟩, by rw [hst, hst_eq]; exact ⟨rfl, rfl⟩⟩
    | some val =>
      obtain ⟨done_c, target_c, rest_c⟩ := val
      have htarget_not_lit := Core.firstNonValueExpr_not_lit hcfnv
      have htarget_novalue : Core.exprValue? target_c = none := by
        cases target_c with
        | lit v => exact absurd rfl (htarget_not_lit v)
        | _ => rfl
      have htarget_supp : target_c.supported = true :=
        listSupported_firstNonValueExpr_target hcfnv (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
      have hffnv := convertExprList_firstNonValueExpr_some elems scope envVar envMap st
          done_c target_c rest_c hcfnv htarget_novalue htarget_supp
      have hfnv_target : Flat.exprValue? (Flat.convertExpr target_c scope envVar envMap
          (Flat.convertExprList done_c scope envVar envMap st).snd).fst = none :=
        convertExpr_not_value_supported target_c htarget_novalue htarget_supp scope envVar envMap _
      have hsf_eta : sf = { sf with expr := .arrayLit (Flat.convertExprList elems scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa,
          Flat.step? { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).fst } = some (ev, sa) ∧
          sf' = { expr := .arrayLit ((Flat.convertExprList done_c scope envVar envMap st).fst ++
                    [sa.expr] ++
                    (Flat.convertExprList rest_c scope envVar envMap
                      (Flat.convertExpr target_c scope envVar envMap
                        (Flat.convertExprList done_c scope envVar envMap st).snd).snd).fst),
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        have hvals := valuesFromExprList_none_of_firstNonValueExpr hffnv
        match hm : Flat.step? { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).fst } with
        | some (t, se) =>
          have heq := Flat_step?_arrayLit_step sf _ _ _ _ hvals hffnv t se hm
          rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨se, rfl, hsf'eq.symm⟩
        | none =>
          have heq := Flat_step?_arrayLit_none sf _ _ _ _ hvals hffnv hm
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : target_c.depth < n := by
        simp [Core.Expr.depth] at hd
        have := Core.firstNonValueExpr_depth hcfnv; omega
      have ⟨hncfr_done, hncfr_target, hncfr_rest⟩ :=
        firstNonValueExpr_listNoCallFrameReturn hcfnv (by simp [noCallFrameReturn] at hncfr; exact hncfr)
      have hexprwf_target : ExprAddrWF target_c sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf
        exact ExprAddrListWF_firstNonValueExpr_target hcfnv hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf',
              hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth target_c.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).fst }
          { sc with expr := target_c }
          ev sa scope
          (Flat.convertExprList done_c scope envVar envMap st).snd
          (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_target hexprwf_target htarget_supp
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.arrayLit (done_c ++ [sc_sub'.expr] ++ rest_c),
         sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · -- Core.step?
        show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .arrayLit elems } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        have hcstep_anon : Core.step? ⟨target_c, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ =
            some (ev, sc_sub') := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; exact hcstep_sub
        have hcore_step := Core.step_arrayLit_step_elem elems sc.env sc.heap sc.trace sc.funcs sc.callStack
            done_c target_c rest_c hcfnv ev sc_sub' hcstep_anon
        simp only [Core.pushTrace] at hcore_step
        have : sc' = { sc_sub' with
          expr := .arrayLit (done_c ++ [sc_sub'.expr] ++ rest_c),
          trace := sc.trace ++ [ev] } := by simp [sc']
        rw [this]; exact hcore_step
      · -- trace
        simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · -- noCallFrameReturn
        simp only [sc', noCallFrameReturn]
        rw [listNoCallFrameReturn_append, listNoCallFrameReturn_append]
        simp [listNoCallFrameReturn, hncfr', hncfr_done, hncfr_rest]
      · -- ExprAddrWF arrayLit: reconstruct from IH
        simp only [sc', ExprAddrWF]
        exact ExprAddrListWF_firstNonValueExpr_reconstruct hcfnv
          (by simp [ExprAddrWF] at hexprwf; exact hexprwf) hexprwf'
          (Core_step_heap_size_mono hcstep_sub)
      · -- CCState agreement (arrayLit sub-step)
        -- IH gives: hconv' at st_a, hAgreeIn : CCStateAgree (convertExprList done_c st).snd st_a
        --           hAgreeOut : CCStateAgree (convertExpr target_c (convertExprList done_c st).snd).snd st_a'
        have hsub_det := convertExpr_state_determined sc_sub'.expr scope envVar envMap
          (Flat.convertExprList done_c scope envVar envMap st).snd st_a hAgreeIn.1 hAgreeIn.2
        have hsa_fst : (Flat.convertExpr sc_sub'.expr scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).fst = sa.expr :=
          hsub_det.1.trans (congrArg Prod.fst hconv').symm
        have hsa_snd_eq : (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' :=
          (congrArg Prod.snd hconv').symm
        have hstate_sub_agree : CCStateAgree
            (Flat.convertExpr sc_sub'.expr scope envVar envMap
              (Flat.convertExprList done_c scope envVar envMap st).snd).snd st_a' :=
          ⟨hsub_det.2.1.trans (hsa_snd_eq ▸ rfl), hsub_det.2.2.trans (hsa_snd_eq ▸ rfl)⟩
        have hrest_in_agree : CCStateAgree
            (Flat.convertExpr sc_sub'.expr scope envVar envMap
              (Flat.convertExprList done_c scope envVar envMap st).snd).snd
            (Flat.convertExpr target_c scope envVar envMap
              (Flat.convertExprList done_c scope envVar envMap st).snd).snd :=
          ⟨hstate_sub_agree.1.trans hAgreeOut.1.symm, hstate_sub_agree.2.trans hAgreeOut.2.symm⟩
        have hrest_det := convertExprList_state_determined rest_c scope envVar envMap
          _ _ hrest_in_agree.1 hrest_in_agree.2
        refine ⟨st, (Flat.convertExprList (done_c ++ [sc_sub'.expr] ++ rest_c) scope envVar envMap st).snd,
          ?_, ⟨rfl, rfl⟩, ?_⟩
        · -- Conversion expression matches sf'.expr
          simp only [sc', Flat.convertExpr]
          congr 1
          rw [convertExprList_append, convertExprList_append, convertExprList_append_snd]
          simp only [Flat.convertExprList]
          rw [hsa_fst, hrest_det.1]
        · -- Output state agreement
          have helems := firstNonValueExpr_decompose hcfnv
          rw [hst, helems]
          have h_lhs := convertExprList_append_snd (done_c ++ [target_c]) rest_c scope envVar envMap st
          have h_lhs2 := convertExprList_append_snd done_c [target_c] scope envVar envMap st
          have h_rhs := convertExprList_append_snd (done_c ++ [sc_sub'.expr]) rest_c scope envVar envMap st
          have h_rhs2 := convertExprList_append_snd done_c [sc_sub'.expr] scope envVar envMap st
          simp only [h_lhs, h_lhs2, h_rhs, h_rhs2, Flat.convertExprList]
          exact ⟨hrest_det.2.1.symm, hrest_det.2.2.symm⟩
  | functionDef fname params body isAsync isGen =>
    -- BLOCKED: functionDef case — FuncsCorr now available (wired into CC_SimRel).
    -- Still needs: (b) prove FuncsCorr maintained when adding closure,
    -- (c) multi-step Flat simulation (makeClosure+makeEnv is N steps vs Core's 1 step).
    -- hfuncCorr : FuncsCorr injMap sc.funcs sf.funcs t.functions
    sorry
  | throw val =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? val with
    | some cv =>
      have hlit : val = .lit cv := by
        cases val <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr
      have hsf_eta : sf = { sf with expr := .throw (.lit (Flat.convertValue cv)) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_throw_lit] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
        sc.trace ++ [.error (Core.valueToString cv)], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · rw [valueToString_convertValue]
        have hsc' : sc = { sc with expr := .throw (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_throw_lit _ _
      · simp [sc', htrace, valueToString_convertValue]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF, ValueAddrWF]
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      -- Sub-expression not a value; Flat steps the sub-expression
      have hfnv : Flat.exprValue? (Flat.convertExpr val scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported val hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .throw (Flat.convertExpr val scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Extract the Flat sub-step via case analysis on step? of sub-expression
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr val scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .throw sa.expr, env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr val scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_throw_step sf _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .throw (Flat.convertExpr val scope envVar envMap st).fst } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      -- Apply IH at smaller depth
      have hdepth : val.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_val : noCallFrameReturn val = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr
      have hexprwf_val : ExprAddrWF val sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth val.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr val scope envVar envMap st).fst }
          { sc with expr := val }
          ev sa scope st (Flat.convertExpr val scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_val hexprwf_val (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
          (by simp)
          ⟨hsubstep⟩
      -- Reconstruct Core step on throw
      let sc' : Core.State :=
        ⟨.throw sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · -- Core step
        show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .throw val } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_throw_step _ _ hcev _ _ hcstep_sub
      · -- trace
        simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | tryCatch body catchParam catchBody finally_ =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    let fbody := (Flat.convertExpr body scope envVar envMap st).fst
    let st1 := (Flat.convertExpr body scope envVar envMap st).snd
    let fcatch := (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st1).fst
    let st2 := (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st1).snd
    let ffin := (Flat.convertOptExpr finally_ scope envVar envMap st2).fst
    have hncf : catchParam ≠ "__call_frame_return__" := by
      unfold noCallFrameReturn at hncfr; simp at hncfr; exact hncfr.1.1.1
    have hncfr_body : noCallFrameReturn body = true := by
      unfold noCallFrameReturn at hncfr; simp at hncfr; exact hncfr.1.1.2
    have hncfr_catch : noCallFrameReturn catchBody = true := by
      unfold noCallFrameReturn at hncfr; simp at hncfr; exact hncfr.1.2
    cases hbv : Core.exprValue? body with
    | some v =>
      have hlit : body = .lit v := by
        cases body <;> simp [Core.exprValue?] at hbv; subst hbv; rfl
      subst hlit
      -- body = .lit v: convertExpr (.lit v) = (.lit (convertValue v), st), so st1 = st
      -- Prove needed simplifications for body = .lit v
      have hce_lit_fst : (Flat.convertExpr (Core.Expr.lit v) scope envVar envMap st).fst =
          Flat.Expr.lit (Flat.convertValue v) := by
        show (Flat.convertExpr (.lit v) scope envVar envMap st).fst = _
        simp only [Flat.convertExpr]
      have hce_lit_snd : (Flat.convertExpr (Core.Expr.lit v) scope envVar envMap st).snd = st := by
        show (Flat.convertExpr (.lit v) scope envVar envMap st).snd = _
        simp only [Flat.convertExpr]
      -- hconv was already simplified by simp [Flat.convertExpr].
      -- After subst body = .lit v, it contains convertExpr (.lit v) terms
      -- Rewrite to simplify those
      rw [hce_lit_fst, hce_lit_snd] at hconv
      cases finally_ with
      | none =>
        simp [Flat.convertOptExpr] at hconv
        obtain ⟨hsf_expr, hst'_eq⟩ := hconv
        have hsf_eta : sf = { sf with expr := (.tryCatch (.lit (Flat.convertValue v)) catchParam
            (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st).fst .none) } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        have hstep_rw := Flat_step?_tryCatch_body_value sf (Flat.convertValue v) catchParam
            (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st).fst hncf
        rw [hstep_rw] at hstep; clear hstep_rw
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev; subst hsf'
        let sc' : Core.State :=
          ⟨.lit v, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · show Core.step? sc = some (.silent, sc')
          have hsc' : sc = { sc with expr := .tryCatch (.lit v) catchParam catchBody none } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core.step_tryCatch_normal_noFinally _ _ _ _ _ _ _ _ hncf
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF, ValueAddrWF]
          simp [ExprAddrWF] at hexprwf; exact hexprwf.1
        · -- CCStateAgree: st' = (convertExpr catchBody ... st).snd, st_a' = st
          -- Output agreement CCStateAgree st' st requires catchBody to not change CCState.
          -- Same class as if-else/while_ CCStateAgree architectural issue.
          exact ⟨st, st, by simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, by rw [hst'_eq]; sorry⟩
          -- BLOCKED: CCStateAgree. st' = (convertExpr catchBody ... st).snd but st_a' = st.
          -- FIX: Change invariant to CCStateAgreeWeak; then output = convertExpr_state_mono catchBody.
      | some fin => sorry -- BLOCKED: CCStateAgree + tryCatch body-value with finally.
            -- Same CCStateAgree issue as the none case, compounded by finally_ conversion.
            -- FIX: Full proof exists (see git history); blocked only by CCStateAgreeWeak invariant change.
    | none =>
      -- Body is not a value; step the body via IH
      have hfnv : Flat.exprValue? fbody = none :=
        convertExpr_not_value_supported body hbv (by revert hsupp; cases finally_ <;> simp [Core.Expr.supported, Bool.and_eq_true] <;> intro h <;> (first | exact h.1.1 | exact h.1 | exact h | exact (fun _ => h) | exact (fun _ _ => h))) scope envVar envMap st
      have hexprwf_body : ExprAddrWF body sc.heap.objects.size := by
        cases finally_ <;> simp [ExprAddrWF] at hexprwf <;> exact hexprwf.1
      have hsf_eta : sf = { sf with expr := .tryCatch fbody catchParam fcatch ffin } := by
        cases sf; simp_all [fbody, fcatch, ffin, st1, st2]
      rw [hsf_eta] at hstep
      match hm : Flat.step? { sf with expr := fbody } with
      | some (t, sb) =>
        by_cases herr : ∃ msg, t = .error msg
        · -- Error: catch clause activated (scope mismatch blocks full proof)
          obtain ⟨msg, rfl⟩ := herr
          have heq := Flat_step?_tryCatch_body_error sf fbody catchParam fcatch ffin sb msg hncf hfnv hm
          rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨hev_eq, hsf'_eq⟩ := hstep; subst hev_eq; subst hsf'_eq
          -- Error case: apply IH to body sub-step, construct catch handler state
          have hdepth : body.depth < n := by
            have := tryCatch_body_depth_lt body catchParam catchBody finally_; omega
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf',
              hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
            ih_depth body.depth hdepth envVar envMap injMap
              { sf with expr := fbody }
              { sc with expr := body }
              (.error msg) sb scope st st1
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_body hexprwf_body (by revert hsupp; cases finally_ <;> simp [Core.Expr.supported, Bool.and_eq_true] <;> intro h <;> (first | exact h.1.1 | exact h.1 | exact h | exact (fun _ => h) | exact (fun _ _ => h)))
              (by simp [fbody, st1])
              ⟨hm⟩
          let handler := match finally_ with | some fin => Core.Expr.seq catchBody fin | none => catchBody
          let sc' : Core.State :=
            ⟨handler, Core.Env.extend sc_sub'.env catchParam (.string msg), sc_sub'.heap,
             sc.trace ++ [.error msg], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · -- Core step: tryCatch body error → catch handler
            show Core.step? sc = some (.error msg, sc')
            have hsc_rw : sc = { sc with expr := .tryCatch body catchParam catchBody finally_ } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc_rw]
            have h := Core.step_tryCatch_step_body_error body catchParam catchBody finally_
              sc.env sc.heap sc.trace sc.funcs sc.callStack hbv hncf msg sc_sub' hcstep_sub
            simp only [Core.pushTrace] at h
            exact h
          · simp [sc', htrace]
          · exact hinj'
          · exact EnvCorrInj_extend henvCorr' catchParam (.string msg)
          · exact EnvAddrWF_extend henvwf' catchParam (.string msg) (by simp [ValueAddrWF])
          · exact hheapvwf'
          · exact hheapna'
          · -- noCallFrameReturn
            simp only [sc', handler]
            cases finally_ with
            | none => exact hncfr_catch
            | some fin =>
              simp [noCallFrameReturn]
              exact ⟨hncfr_catch, by unfold noCallFrameReturn at hncfr; simp at hncfr; exact hncfr.2⟩
          · -- ExprAddrWF
            simp only [sc', handler]
            have hmono := Core_step_heap_size_mono hcstep_sub
            cases finally_ with
            | none =>
              exact ExprAddrWF_mono catchBody
                (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) hmono
            | some fin =>
              simp only [ExprAddrWF]
              exact ⟨ExprAddrWF_mono catchBody
                  (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.1) hmono,
                ExprAddrWF_mono fin
                  (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2) hmono⟩
          · -- CCStateAgree: convertExpr_scope_irrelevant solves scope mismatch
            -- but CCStateAgree st st1 remains (body conversion may change nextId/funcs.size)
            sorry -- BLOCKED: CCStateAgree. Need CCStateAgree st st_a where st_a accounts for
            -- body conversion state st1 = (convertExpr body ... st).snd, but body may contain
            -- functionDef nodes that change nextId/funcs.size.
            -- FIX: Change invariant to CCStateAgreeWeak; use st1 as witness with scope_irrelevant
            -- and convertExpr_state_mono body. Full proof skeleton:
            -- cases finally_ with
            -- | none => ⟨st1, (convertExpr catchBody scope ... st1).snd, by simp [...]; rw [scope_irrelevant],
            --   convertExpr_state_mono body ..., by rw [hconv.2]; simp [...]; rw [← scope_irrelevant]; le_refl⟩
            -- | some fin => analogous with (convertExpr fin ... (convertExpr catchBody ... st1).snd).snd
        · -- Non-error: body step preserves tryCatch wrapper
          simp only [not_exists] at herr
          have heq := Flat_step?_tryCatch_body_step sf fbody catchParam fcatch ffin sb t hncf hfnv hm herr
          rw [heq] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨hev_eq, hsf'_eq⟩ := hstep; subst hev_eq; subst hsf'_eq
          -- Apply IH to body sub-step
          have hdepth : body.depth < n := by
            have := tryCatch_body_depth_lt body catchParam catchBody finally_; omega
          obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf',
              hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
            ih_depth body.depth hdepth envVar envMap injMap
              { sf with expr := fbody }
              { sc with expr := body }
              t sb scope st st1
              (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_body hexprwf_body (by revert hsupp; cases finally_ <;> simp [Core.Expr.supported, Bool.and_eq_true] <;> intro h <;> (first | exact h.1.1 | exact h.1 | exact h | exact (fun _ => h) | exact (fun _ _ => h)))
              (by simp [fbody, st1])
              ⟨hm⟩
          let sc' : Core.State :=
            ⟨.tryCatch sc_sub'.expr catchParam catchBody finally_, sc_sub'.env, sc_sub'.heap,
             sc.trace ++ [t], sc_sub'.funcs, sc_sub'.callStack⟩
          refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
          · -- Core step
            show Core.step? sc = some (t, sc')
            have hsc_rw : sc = { sc with expr := .tryCatch body catchParam catchBody finally_ } := by
              obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
            rw [hsc_rw]
            have h := Core.step_tryCatch_step_body_nonError body catchParam catchBody finally_
              sc.env sc.heap sc.trace sc.funcs sc.callStack hbv t sc_sub' hcstep_sub herr
            simp only [Core.pushTrace] at h
            exact h
          · simp [sc', htrace, htrace_sub]
          · exact hinj'
          · exact henvCorr'
          · exact henvwf'
          · exact hheapvwf'
          · simp [sc', hheapna']
          · -- noCallFrameReturn
            simp only [sc']
            unfold noCallFrameReturn
            simp only [bne_iff_ne, Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨⟨hncf, hncfr'⟩, hncfr_catch⟩, ?_⟩
            · unfold noCallFrameReturn at hncfr; simp at hncfr
              cases finally_ with | none => trivial | some f => exact hncfr.2
          · -- ExprAddrWF
            simp only [sc']
            have hmono := Core_step_heap_size_mono hcstep_sub
            cases finally_ with
            | none =>
              simp only [ExprAddrWF]
              exact ⟨hexprwf', ExprAddrWF_mono catchBody (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2) hmono⟩
            | some fin =>
              simp only [ExprAddrWF]
              exact ⟨hexprwf',
                ExprAddrWF_mono catchBody (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.1) hmono,
                ExprAddrWF_mono fin (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2.2) hmono⟩
          · -- CCStateAgree: thread IH result through tryCatch sub-conversions
            have hconv'_fst : sb.expr = (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).fst :=
              congrArg Prod.fst hconv'
            have hconv'_snd : (Flat.convertExpr sc_sub'.expr scope envVar envMap st_a).snd = st_a' :=
              congrArg Prod.snd hconv'.symm
            have hAgreeOut_sym : st_a'.nextId = st1.nextId ∧ st_a'.funcs.size = st1.funcs.size :=
              ⟨hAgreeOut.1.symm, hAgreeOut.2.symm⟩
            have hsd_c := convertExpr_state_determined catchBody (catchParam :: scope) envVar envMap
              st_a' st1 hAgreeOut_sym.1 hAgreeOut_sym.2
            have hsd_f := convertOptExpr_state_determined finally_ scope envVar envMap
              (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st_a').snd
              st2 hsd_c.2.1 hsd_c.2.2
            refine ⟨st_a,
              (Flat.convertOptExpr finally_ scope envVar envMap
                (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st_a').snd).snd,
              ?_, hAgreeIn, by rw [hconv.2]; exact ⟨hsd_f.2.1.symm, hsd_f.2.2.symm⟩⟩
            simp only [sc', Flat.convertExpr, hconv'_fst, hconv'_snd, hsd_c.1, hsd_f.1, fcatch, ffin]
      | none =>
        have heq : Flat.step? { sf with expr := .tryCatch fbody catchParam fcatch ffin } = none := by
          simp only [Flat.step?, hfnv, hm]
        rw [heq] at hstep; exact absurd hstep (by simp)
  | while_ cond body =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    let fcond := (Flat.convertExpr cond scope envVar envMap st).fst
    let st_c := (Flat.convertExpr cond scope envVar envMap st).snd
    let fbody := (Flat.convertExpr body scope envVar envMap st_c).fst
    have hsf_eta : sf = { sf with expr := Flat.Expr.while_ fcond fbody } := by
      cases sf; simp_all [fcond, fbody, st_c]
    rw [hsf_eta] at hstep
    rw [Flat_step?_while] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State :=
      ⟨.«if» cond (.seq body (.while_ cond body)) (.lit .undefined),
       sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
    · show Core.step? sc = some (.silent, sc')
      have hsc' : sc = { sc with expr := .while_ cond body } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_while _ _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', hheapna]
    · simp [sc', noCallFrameReturn]; simp [noCallFrameReturn] at hncfr; exact ⟨hncfr.1, hncfr.2, hncfr.1, hncfr.2⟩
    · simp only [sc', ExprAddrWF, ValueAddrWF]; simp only [ExprAddrWF] at hexprwf
      exact ⟨hexprwf.1, ⟨hexprwf.2, hexprwf.1, hexprwf.2⟩, trivial⟩
    · -- Conversion relation: need convertExpr (.if cond (.seq body (.while_ cond body)) (.lit .undefined))
      -- to match sf'.expr. This requires CCState independence since while_ duplicates cond and body.
      sorry -- BLOCKED: CCStateAgree. while_ lowers to .if cond (.seq body (.while_ cond body)) (.lit .undefined)
      -- which duplicates cond and body, each needing independent CCState threading. The duplicated
      -- sub-expressions get different CCState inputs, breaking CCStateAgree.
  | forIn binding obj body =>
    rw [hsc] at hconv
    simp [Flat.convertExpr] at hconv
    have hsf_eta : sf = { sf with expr := .lit .undefined } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_lit] at hstep
    exact absurd hstep (fun h => nomatch h)
  | forOf binding iterable body =>
    rw [hsc] at hconv
    simp [Flat.convertExpr] at hconv
    have hsf_eta : sf = { sf with expr := .lit .undefined } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_lit] at hstep
    exact absurd hstep (fun h => nomatch h)
  | «break» label =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«break» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_break] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("break:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
    · have hsc' : sc = { sc with expr := .«break» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_break _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', hheapna]
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «continue» label =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«continue» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_continue] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("continue:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
    · have hsc' : sc = { sc with expr := .«continue» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_continue _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', hheapna]
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «return» val =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    cases val with
    | none =>
      simp [Flat.convertExpr, Flat.convertOptExpr] at hconv
      obtain ⟨hfexpr, hst⟩ := hconv
      have hsf_eta : sf = { sf with expr := .«return» none } := by cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_return_none] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
        sc.trace ++ [.error "return:undefined"], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · show Core.step? sc = some (.error "return:undefined", sc')
        have hsc' : sc = { sc with expr := .«return» none } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_return_none _
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF, ValueAddrWF]
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | some e =>
      simp [Flat.convertExpr, Flat.convertOptExpr] at hconv
      obtain ⟨hfexpr, hst⟩ := hconv
      cases hcev : Core.exprValue? e with
      | some cv =>
        have hlit : e = .lit cv := by
          cases e <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
        subst hlit
        simp [Flat.convertExpr] at hfexpr
        have hsf_eta : sf = { sf with expr := .«return» (some (.lit (Flat.convertValue cv))) } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        rw [Flat_step?_return_some_lit] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State := ⟨.lit cv, sc.env, sc.heap,
          sc.trace ++ [.error ("return:" ++ Core.valueToString cv)], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · rw [valueToString_convertValue]
          have hsc' : sc = { sc with expr := .«return» (some (.lit cv)) } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_return_some_lit _ _
        · simp [sc', htrace, valueToString_convertValue]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp only [sc']; simp [ExprAddrWF] at hexprwf ⊢; exact hexprwf
        · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
      | none =>
        -- Sub-expression not a value; Flat steps the sub-expression
        have hfnv : Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none :=
          convertExpr_not_value_supported e hcev (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2)) scope envVar envMap st
        have hsf_eta : sf = { sf with expr := .«return» (some (Flat.convertExpr e scope envVar envMap st).fst) } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        -- Extract the Flat sub-step via case analysis on step? of sub-expression
        obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst } = some (ev, sa) ∧
            sf' = { expr := .«return» (some sa.expr), env := sa.env, heap := sa.heap,
                    trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
          match hm : Flat.step? { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst } with
          | some (t, sa) =>
            have heq := Flat_step?_return_some_step sf _ hfnv t sa hm
            rw [heq] at hstep; simp at hstep
            obtain ⟨rfl, hsf'eq⟩ := hstep
            exact ⟨sa, rfl, hsf'eq.symm⟩
          | none =>
            have heq : Flat.step? { sf with expr := .«return» (some (Flat.convertExpr e scope envVar envMap st).fst) } = none := by
              simp only [Flat.step?, hfnv, hm]
            rw [heq] at hstep; exact absurd hstep (by simp)
        subst hsf'_eq
        -- Apply IH at smaller depth
        have hdepth : e.depth < n := by simp [Core.Expr.depth] at hd; omega
        have hncfr_val : noCallFrameReturn e = true := by
          simp [noCallFrameReturn] at hncfr; exact hncfr
        have hexprwf_val : ExprAddrWF e sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
          ih_depth e.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst }
            { sc with expr := e }
            ev sa scope st (Flat.convertExpr e scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_val hexprwf_val (by simp only [Core.Expr.supported, Bool.and_eq_true] at hsupp ⊢; first | exact hsupp | exact hsupp.1 | exact hsupp.2 | exact hsupp.1.1 | exact hsupp.1.2 | (simp only [Bool.and_eq_true] at hsupp; first | exact hsupp.1 | exact hsupp.2 | exact hsupp.2.1 | exact hsupp.2.2))
            (by simp)
            ⟨hsubstep⟩
        -- Reconstruct Core step on return
        let sc' : Core.State :=
          ⟨.«return» (some sc_sub'.expr), sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
        · show Core.step? sc = some (ev, sc')
          have hsc' : sc = { sc with expr := .«return» (some e) } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core_step?_return_some_step _ _ hcev _ _ hcstep_sub
        · simp [sc', htrace, htrace_sub]
        · exact hinj'
        · exact henvCorr'
        · exact henvwf'
        · exact hheapvwf'
        · exact hheapna'
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp [sc', ExprAddrWF]; exact hexprwf'
        · exact ⟨st_a, st_a', by
            simp [sc', Flat.convertExpr, Flat.convertOptExpr]
            exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | labeled label body =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst'⟩ := hconv
    have hsf_eta : sf = { sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).fst } := by
      cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_labeled] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State := ⟨body, sc.env, sc.heap,
      sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
    · have hsc' : sc = { sc with expr := .labeled label body } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_labeled _ _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', hheapna]
    · show noCallFrameReturn sc'.expr = true
      simp [sc']; exact hncfr
    · show ExprAddrWF sc'.expr sc'.heap.objects.size
      simp [sc']; exact hexprwf
    · exact ⟨st, (Flat.convertExpr body scope envVar envMap st).snd, by simp [sc'], ⟨rfl, rfl⟩, by first | (rw [hst']; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr] at hst'; subst hst'; exact ⟨rfl, rfl⟩)⟩
  | yield arg delegate =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    cases arg with
    | none =>
      simp [Flat.convertExpr, Flat.convertOptExpr] at hconv
      obtain ⟨hfexpr, hst⟩ := hconv
      have hsf_eta : sf = { sf with expr := .yield none delegate } := by cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_yield_none] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
        sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · show Core.step? sc = some (.silent, sc')
        have hsc' : sc = { sc with expr := .yield none delegate } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_yield_none _ _
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF, ValueAddrWF]
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | some e =>
      simp [Flat.convertExpr, Flat.convertOptExpr] at hconv
      obtain ⟨hfexpr, hst⟩ := hconv
      cases hcev : Core.exprValue? e with
      | some cv =>
        have hlit : e = .lit cv := by
          cases e <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
        subst hlit
        simp [Flat.convertExpr] at hfexpr
        have hsf_eta : sf = { sf with expr := .yield (some (.lit (Flat.convertValue cv))) delegate } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        rw [Flat_step?_yield_some_lit] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State := ⟨.lit cv, sc.env, sc.heap,
          sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
        · show Core.step? sc = some (.silent, sc')
          have hsc' : sc = { sc with expr := .yield (some (.lit cv)) delegate } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_yield_some_lit _ _ _
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', hheapna]
        · simp [sc', noCallFrameReturn]
        · simp only [sc']; simp [ExprAddrWF] at hexprwf ⊢; exact hexprwf
        · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
      | none =>
        -- Sub-expression not a value; Flat steps the sub-expression
        have hfnv : Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none :=
          convertExpr_not_value_supported e hcev (by simp only [Core.Expr.supported] at hsupp; exact absurd hsupp (by decide)) scope envVar envMap st
        have hsf_eta : sf = { sf with expr := .yield (some (Flat.convertExpr e scope envVar envMap st).fst) delegate } := by
          cases sf; simp_all
        rw [hsf_eta] at hstep
        -- Extract the Flat sub-step via case analysis on step? of sub-expression
        obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst } = some (ev, sa) ∧
            sf' = { expr := .yield (some sa.expr) delegate, env := sa.env, heap := sa.heap,
                    trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
          match hm : Flat.step? { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst } with
          | some (t, sa) =>
            have heq := Flat_step?_yield_some_step sf _ delegate hfnv t sa hm
            rw [heq] at hstep; simp at hstep
            obtain ⟨rfl, hsf'eq⟩ := hstep
            exact ⟨sa, rfl, hsf'eq.symm⟩
          | none =>
            have heq : Flat.step? { sf with expr := .yield (some (Flat.convertExpr e scope envVar envMap st).fst) delegate } = none := by
              simp only [Flat.step?, hfnv, hm]
            rw [heq] at hstep; exact absurd hstep (by simp)
        subst hsf'_eq
        -- Apply IH at smaller depth
        have hdepth : e.depth < n := by simp [Core.Expr.depth] at hd; omega
        have hncfr_val : noCallFrameReturn e = true := by
          simp [noCallFrameReturn] at hncfr; exact hncfr
        have hexprwf_val : ExprAddrWF e sc.heap.objects.size := by
          simp [ExprAddrWF] at hexprwf; exact hexprwf
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
          ih_depth e.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst }
            { sc with expr := e }
            ev sa scope st (Flat.convertExpr e scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_val hexprwf_val (by simp only [Core.Expr.supported] at hsupp; exact absurd hsupp (by decide))
            (by simp)
            ⟨hsubstep⟩
        -- Reconstruct Core step on yield
        let sc' : Core.State :=
          ⟨.yield (some sc_sub'.expr) delegate, sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
        · show Core.step? sc = some (ev, sc')
          have hsc' : sc = { sc with expr := .yield (some e) delegate } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']
          exact Core_step?_yield_some_step _ _ _ hcev _ _ hcstep_sub
        · simp [sc', htrace, htrace_sub]
        · exact hinj'
        · exact henvCorr'
        · exact henvwf'
        · exact hheapvwf'
        · exact hheapna'
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp [sc', ExprAddrWF]; exact hexprwf'
        · exact ⟨st_a, st_a', by
            simp [sc', Flat.convertExpr, Flat.convertOptExpr]
            exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | await arg =>
    rw [hsc] at hconv hncfr hexprwf hd hsupp
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? arg with
    | some cv =>
      have hlit : arg = .lit cv := by
        cases arg <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
      subst hlit
      simp [Flat.convertExpr] at hfexpr
      have hsf_eta : sf = { sf with expr := .await (.lit (Flat.convertValue cv)) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      rw [Flat_step?_await_lit] at hstep
      simp at hstep
      obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
      let sc' : Core.State := ⟨.lit cv, sc.env, sc.heap,
        sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr⟩
      · show Core.step? sc = some (.silent, sc')
        have hsc' : sc = { sc with expr := .await (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_await_lit _ _
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', hheapna]
      · simp [sc', noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF] at hexprwf ⊢; exact hexprwf
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      -- Sub-expression not a value; Flat steps the sub-expression
      have hfnv : Flat.exprValue? (Flat.convertExpr arg scope envVar envMap st).fst = none :=
        convertExpr_not_value_supported arg hcev (by simp only [Core.Expr.supported] at hsupp; exact absurd hsupp (by decide)) scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .await (Flat.convertExpr arg scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      -- Extract the Flat sub-step via case analysis on step? of sub-expression
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .await sa.expr, env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_await_step sf _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .await (Flat.convertExpr arg scope envVar envMap st).fst } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      -- Apply IH at smaller depth
      have hdepth : arg.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_val : noCallFrameReturn arg = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr
      have hexprwf_val : ExprAddrWF arg sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hheapna', hncfr', hexprwf', ⟨st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩, hfuncCorr_sub⟩ :=
        ih_depth arg.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst }
          { sc with expr := arg }
          ev sa scope st (Flat.convertExpr arg scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr hfuncCorr henvwf hheapvwf hheapna hncfr_val hexprwf_val (by simp only [Core.Expr.supported] at hsupp; exact absurd hsupp (by decide))
          (by simp)
          ⟨hsubstep⟩
      -- Reconstruct Core step on await
      let sc' : Core.State :=
        ⟨.await sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfuncCorr_sub⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .await arg } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_await_step _ _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · exact hheapna'
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
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
        next => split at h <;> simp at h
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
        next => split at h <;> simp at h
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
        next => split at h <;> simp at h
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
          unfold Flat.step? at h; simp only [hev, hstep] at h; obtain ⟨t, _⟩ := r; cases t <;> simp at h
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
          unfold Flat.step? at h; simp only [hev, hstep] at h; obtain ⟨t, _⟩ := r; cases t <;> simp at h
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
          unfold Flat.step? at h; simp only [hev, hstep] at h; obtain ⟨t, _⟩ := r; cases t <;> simp at h
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
          unfold Flat.step? at h; simp only [hev, hstep] at h; obtain ⟨t, _⟩ := r; cases t <;> simp at h
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
            unfold Flat.step? at h; simp only [hev, hstep] at h; obtain ⟨t, _⟩ := r; cases t <;> simp at h
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
            unfold Flat.step? at h; simp only [hev, hstep] at h; obtain ⟨t, _⟩ := r; cases t <;> simp at h
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
      next =>
        split at h
        next => simp at h
        next hevv =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨value, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hevv; simp [Flat.exprValue?] at hevv
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
      next =>
        split at h
        next => simp at h
        next hevi =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨idx, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hevi; simp [Flat.exprValue?] at hevi
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
      next =>
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
    | tryCatch body _catchParam _catchBody _finally_ =>
      exfalso; unfold Flat.step? at h
      split at h
      next =>
        split at h <;> (split at h <;> (try simp at h) <;> (try (split at h <;> simp at h)))
      next hev =>
        split at h
        next =>
          repeat split at h
          all_goals (dsimp only at h; split at h <;> simp at h <;> (try (split at h <;> simp at h)))
        next =>
          dsimp only at h; simp at h
        next hstep_none =>
          have hbd : body.depth ≤ k := by cases _finally_ <;> simp [Flat.Expr.depth] at hd <;> omega
          have ⟨v, hv⟩ := ih ⟨body, fenv, fheap, ftrace, ffuncs, fcallStack⟩ hbd hstep_none
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
          unfold Flat.step? at h; simp only [hevf, hstepf] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
        | none =>
          have ⟨v, hv⟩ := ih ⟨funcExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepf
          simp at hv; rw [hv] at hevf; simp [Flat.exprValue?] at hevf
      | some vf =>
        cases heve : Flat.exprValue? envExpr with
        | none =>
          cases hstepe : Flat.step? ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hevf, heve, hstepe] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepe
            simp at hv; rw [hv] at heve; simp [Flat.exprValue?] at heve
        | some ve =>
          unfold Flat.step? at h
          simp only [hevf, heve] at h
          cases hvfl : Flat.valuesFromExprList? args with
          | some argVals =>
            simp only [hvfl] at h
            cases vf <;> simp at h <;> (try done) <;>
              (split at h <;> (try simp at h) <;> (try (split at h <;> simp at h)))
          | none =>
            simp only [hvfl] at h
            cases hf : Flat.firstNonValueExpr args with
            | none =>
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values args hf
              simp [hvs] at hvfl
            | some val =>
              obtain ⟨done, target, remaining⟩ := val
              rw [show Flat.firstNonValueExpr args = some (done, target, remaining) from hf] at h
              cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
              | some r =>
                simp only [hstept] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
              | none =>
                have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩
                  (by simp [Flat.Expr.depth] at hd ⊢; have := Flat.firstNonValueExpr_depth hf; omega) hstept
                exact absurd hv (firstNonValueExpr_not_lit hf v)
    | newObj funcExpr envExpr args =>
      exfalso
      cases hevf : Flat.exprValue? funcExpr with
      | none =>
        cases hstepf : Flat.step? ⟨funcExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hevf, hstepf] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
        | none =>
          have ⟨v, hv⟩ := ih ⟨funcExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepf
          simp at hv; rw [hv] at hevf; simp [Flat.exprValue?] at hevf
      | some vf =>
        cases heve : Flat.exprValue? envExpr with
        | none =>
          cases hstepe : Flat.step? ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hevf, heve, hstepe] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace, ffuncs, fcallStack⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepe
            simp at hv; rw [hv] at heve; simp [Flat.exprValue?] at heve
        | some ve =>
          unfold Flat.step? at h; simp only [hevf, heve] at h
          cases hvfl : Flat.valuesFromExprList? args with
          | some argVals =>
            simp only [hvfl] at h; exact absurd h (by simp)
          | none =>
            simp only [hvfl] at h
            cases hf : Flat.firstNonValueExpr args with
            | none =>
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values args hf
              simp [hvs] at hvfl
            | some val =>
              obtain ⟨done, target, remaining⟩ := val
              rw [show Flat.firstNonValueExpr args = some (done, target, remaining) from hf] at h
              cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩ with
              | some r =>
                simp only [hstept] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
              | none =>
                have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace, ffuncs, fcallStack⟩
                  (by simp [Flat.Expr.depth] at hd ⊢; have := Flat.firstNonValueExpr_depth hf; omega) hstept
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
            simp only [hstept] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
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
            simp only [hstept] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
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
            simp only [hstept] at h; exact absurd h (by obtain ⟨t, _⟩ := r; cases t <;> simp)
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
  intro sf sc hrel hhalt hnoForIn hnoForOf
  obtain ⟨htrace, _, _hncfr, _hexprwf, _henvwf, _hheapvwf, _hheapna, _hsupp, _, scope, envVar, envMap, st, st', hconv⟩ := hrel
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
    (h_supp : s.body.supported = true)
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → Core.Behaves s b := by
  intro b ⟨sf, hsteps, hhalt⟩
  have hinit := closureConvert_init_related s t h h_wf h_addr_wf h_supp
  obtain ⟨sc, hcsteps, hrel⟩ :=
    closureConvert_steps_simulation s t h _ _ _ _ hinit hsteps
  have hnoFor := hnofor sc _ hcsteps
  exact ⟨sc, hcsteps,
    closureConvert_halt_preservation s t h _ _ hrel hhalt hnoFor.1 hnoFor.2⟩

/-- Closure conversion preserves behavior, assuming the source program
    never reaches a forIn/forOf expression (unimplemented in closure conversion)
    and the source body contains no "__call_frame_return__" catch parameters.
    NOTE: `supported` is assumed internally; will be added as explicit precondition
    when EndToEnd.lean is updated. -/
theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (h_supp : s.body.supported = true)
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact closureConvert_trace_reflection s t h h_wf h_addr_wf h_supp hnofor b hb

end VerifiedJS.Proofs
