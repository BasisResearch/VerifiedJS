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

/-! ### CCState determination: convertExpr output depends only on nextId and funcs.size.

  Two `CCState`s that agree on `nextId` and `funcs.size` produce the same
  output expression from `convertExpr`, and the resulting states again agree
  on `nextId` and `funcs.size`.  This is the key lemma needed for the
  CCState-threading sorry cases: after an inner sub-expression steps, the
  second sub-expression's conversion result is unchanged because only
  `nextId` and `funcs.size` matter. -/

private abbrev CCStateAgree (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId = st2.nextId ∧ st1.funcs.size = st2.funcs.size

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
mutual
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

/-- All object addresses in a list of Core expressions are valid heap addresses. -/
def ExprAddrListWF : List Core.Expr → Nat → Prop
  | [], _ => True
  | e :: es, n => ExprAddrWF e n ∧ ExprAddrListWF es n
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

private theorem ExprAddrListWF_mono : (es : List Core.Expr) → {n m : Nat} →
    ExprAddrListWF es n → (n ≤ m) → ExprAddrListWF es m
  | [], _, _, _, _ => trivial
  | e :: es, _, _, h, hle => ⟨ExprAddrWF_mono e h.1 hle, ExprAddrListWF_mono es h.2 hle⟩
  termination_by es => sizeOf es
  decreasing_by all_goals (try simp_wf) <;> omega
end

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .assign name fe } =
      some (t, { expr := .assign name sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .seq fe b } =
      some (t, { expr := .seq sa.expr b, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, hnv, hss]; rfl

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
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .«let» name fe body } =
      some (t, { expr := .«let» name sa.expr body, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  simp only [Flat.step?, hnv, hss]; rfl

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
  have hlv : Core.exprValue? (.lit lv) = some lv := rfl
  simp [Core.step?, hlv, hnv, hss, Core.pushTrace]

private theorem Flat_step?_binary_values (s : Flat.State) (op : Core.BinOp) (lv rv : Flat.Value) :
    Flat.step? { s with expr := .binary op (.lit lv) (.lit rv) } =
      some (.silent, { expr := .lit (Flat.evalBinary op lv rv), env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, Flat.exprValue?]; rfl

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
    (hnovalue : Core.exprValue? target = none) :
    Flat.firstNonValueExpr (Flat.convertExprList es scope envVar envMap st).fst =
      some ((Flat.convertExprList done scope envVar envMap st).fst,
            (Flat.convertExpr target scope envVar envMap
              (Flat.convertExprList done scope envVar envMap st).snd).fst,
            (Flat.convertExprList rest scope envVar envMap
              (Flat.convertExpr target scope envVar envMap
                (Flat.convertExprList done scope envVar envMap st).snd).snd).fst) := by
  induction es generalizing st done with
  | nil => simp [Core.firstNonValueExpr] at h
  | cons e rest_es ih =>
    unfold Core.firstNonValueExpr at h
    split at h
    · -- e = .lit v
      rename_i v
      match hrest : Core.firstNonValueExpr rest_es with
      | some (d, t, r) =>
        simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [Flat.convertExprList, Flat.convertExpr, Flat.firstNonValueExpr]
        exact ih _ _ hrest hnovalue
      | none => simp [hrest] at h
    · -- e is not .lit
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Flat.convertExprList]
      have hfnv : Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none :=
        convertExpr_not_value e hnovalue scope envVar envMap st
      have hnotlit : ∀ v, (Flat.convertExpr e scope envVar envMap st).fst ≠ .lit v := by
        intro v heq; rw [heq] at hfnv; simp [Flat.exprValue?] at hfnv
      -- firstNonValueExpr on a non-lit head returns immediately
      have hfnvhead : ∀ (fe : Flat.Expr) (rs : List Flat.Expr), (∀ v, fe ≠ .lit v) →
          Flat.firstNonValueExpr (fe :: rs) = some ([], fe, rs) := by
        intro fe rs h; cases fe with | lit v => exact absurd rfl (h v) | _ => rfl
      rw [hfnvhead _ _ hnotlit]
      simp [Flat.convertExprList]

private theorem valuesFromExprList_none_of_firstNonValueExpr
    {elems : List Flat.Expr} {done target rest}
    (h : Flat.firstNonValueExpr elems = some (done, target, rest)) :
    Flat.valuesFromExprList? elems = none := by
  induction elems with
  | nil => simp [Flat.firstNonValueExpr] at h
  | cons e es ih =>
    match he : e with
    | .lit v =>
      simp only [he, Flat.firstNonValueExpr] at h
      cases hrest : Flat.firstNonValueExpr es with
      | none => simp [hrest] at h
      | some val =>
        have htail : Flat.valuesFromExprList? es = none := ih (by simp only [hrest] at h; exact h)
        simp only [Flat.valuesFromExprList?, Flat.exprValue?, htail]; split <;> rfl
    | _ => simp only [Flat.valuesFromExprList?, Flat.exprValue?]

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
      EnvAddrWF sc.env sc.heap.objects.size →
      HeapValuesWF sc.heap →
      noCallFrameReturn sc.expr = true →
      ExprAddrWF sc.expr sc.heap.objects.size →
      (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st →
      Flat.Step sf ev sf' →
      ∃ (injMap' : Nat → Nat) (sc' : Core.State), Core.Step sc ev sc' ∧ sf'.trace = sc'.trace ∧
        HeapInj injMap' sc'.heap sf'.heap ∧ EnvCorrInj injMap' sc'.env sf'.env ∧
        EnvAddrWF sc'.env sc'.heap.objects.size ∧
        HeapValuesWF sc'.heap ∧
        noCallFrameReturn sc'.expr = true ∧
        ExprAddrWF sc'.expr sc'.heap.objects.size ∧
        (∃ (st_a st_a' : Flat.CCState),
          (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
          CCStateAgree st st_a ∧ CCStateAgree st' st_a') by
    intro sf sc ev sf' ⟨htrace, ⟨injMap, hinj, henv⟩, hncfr, hexprwf, henvwf, hheapvwf, scope, envVar, envMap, st, st', hconv⟩ hstep
    obtain ⟨injMap', sc', hcstep, htrace', hinj', henv', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', _, _⟩ :=
      this sc.expr.depth envVar envMap injMap sf sc ev sf' scope st st' rfl htrace hinj henv henvwf hheapvwf hncfr hexprwf hconv hstep
    exact ⟨sc', hcstep, htrace', ⟨injMap', hinj', henv'⟩, hncfr', hexprwf', henvwf', hheapvwf', scope, envVar, envMap, st_a, st_a', hconv'⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_depth =>
  intro envVar envMap injMap sf sc ev sf' scope st st' hd htrace hinj henvCorr henvwf hheapvwf hncfr hexprwf hconv ⟨hstep⟩
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
        · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «this» =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «let» name init body =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr
      · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2
      · have hscope := convertExpr_scope_irrelevant body scope (name :: scope) envVar envMap st
        exact ⟨st, (Flat.convertExpr body scope envVar envMap st).snd, by
          simp only [sc']; rw [hscope], ⟨rfl, rfl⟩, by
          rw [hconv.2, convertExpr_scope_irrelevant body (name :: scope) scope]; exact ⟨rfl, rfl⟩⟩
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr init scope envVar envMap st).fst = none :=
        convertExpr_not_value init hcev scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.let name (Flat.convertExpr init scope envVar envMap st).fst
          (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr init scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .«let» name sa.expr
                    (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr init scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_let_step sf name
            (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.let name (Flat.convertExpr init scope envVar envMap st).fst
              (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : init.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_init : noCallFrameReturn init = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1
      have hexprwf_init : ExprAddrWF init sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth init.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr init scope envVar envMap st).fst }
          { sc with expr := init }
          ev sa scope st (Flat.convertExpr init scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_init hexprwf_init
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.«let» name sc_sub'.expr body, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .«let» name init body } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_let_step _ name _ _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
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
  | assign name rhs =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hsc' : sc = { sc with expr := .assign name (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; simp [Core.step?, Core.exprValue?, Core.pushTrace]; rfl
      · simp only [sc']; simp [htrace]
      · exact hinj
      · exact EnvCorrInj_assign henvCorr name cv
      · exact EnvAddrWF_assign henvwf name cv (by simp [ExprAddrWF] at hexprwf; exact hexprwf)
      · exact hheapvwf
      · simp only [sc']; simp [noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF]; exact (by simp [ExprAddrWF] at hexprwf; exact hexprwf)
      · exact ⟨st, st, by simp only [sc']; simp [Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr rhs scope envVar envMap st).fst = none :=
        convertExpr_not_value rhs hcev scope envVar envMap st
      have hsf_eta : sf = { sf with expr := .assign name (Flat.convertExpr rhs scope envVar envMap st).fst } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .assign name sa.expr, env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_assign_step sf name _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .assign name (Flat.convertExpr rhs scope envVar envMap st).fst } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : rhs.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_rhs : noCallFrameReturn rhs = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr
      have hexprwf_rhs : ExprAddrWF rhs sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth rhs.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst }
          { sc with expr := rhs }
          ev sa scope st (Flat.convertExpr rhs scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_rhs hexprwf_rhs
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.assign name sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .assign name rhs } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_assign_step _ name _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | «if» cond then_ else_ =>
    rw [hsc] at hconv hncfr hexprwf hd
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
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr.1
        · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2.1
        · exact ⟨st, (Flat.convertExpr then_ scope envVar envMap st).snd, by
            simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, sorry⟩ -- CCState threading: st' includes else_ conversion but st_a' only then_
      | false =>
        rw [Flat_step?_if_false _ _ _ _ (by rw [toBoolean_convertValue, htb])] at hstep
        simp at hstep
        obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
        let sc' : Core.State :=
          ⟨else_, sc.env, sc.heap, sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr.2
        · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2.2
        · exact ⟨(Flat.convertExpr then_ scope envVar envMap st).snd,
            (Flat.convertExpr else_ scope envVar envMap (Flat.convertExpr then_ scope envVar envMap st).snd).snd, by
            simp [sc', Flat.convertExpr], sorry, sorry⟩
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr cond scope envVar envMap st).fst = none :=
        convertExpr_not_value cond hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth cond.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr cond scope envVar envMap st).fst }
          { sc with expr := cond }
          ev sa scope st (Flat.convertExpr cond scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_cond hexprwf_cond
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.«if» sc_sub'.expr then_ else_, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [sc', noCallFrameReturn] at hncfr ⊢; exact hncfr
      · simp [sc', ExprAddrWF] at hexprwf ⊢; exact hexprwf.2
      · exact ⟨st, (Flat.convertExpr b scope envVar envMap st).snd, by
          simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr a scope envVar envMap st).fst = none :=
        convertExpr_not_value a hcev scope envVar envMap st
      have hsf_eta : sf = { sf with expr := (Flat.Expr.seq (Flat.convertExpr a scope envVar envMap st).fst
          (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst) } := by
        cases sf; simp_all
      rw [hsf_eta] at hstep
      obtain ⟨sa, hsubstep, hsf'_eq⟩ : ∃ sa, Flat.step? { sf with expr := (Flat.convertExpr a scope envVar envMap st).fst } = some (ev, sa) ∧
          sf' = { expr := .seq sa.expr
                    (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst,
                  env := sa.env, heap := sa.heap,
                  trace := sf.trace ++ [ev], funcs := sf.funcs, callStack := sf.callStack } := by
        match hm : Flat.step? { sf with expr := (Flat.convertExpr a scope envVar envMap st).fst } with
        | some (t, sa) =>
          have heq := Flat_step?_seq_step sf
            (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst
            _ hfnv t sa hm
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := (Flat.Expr.seq (Flat.convertExpr a scope envVar envMap st).fst
              (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).snd).fst) } = none := by
            simp only [Flat.step?, hfnv, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : a.depth < n := by simp [Core.Expr.depth] at hd; omega
      have hncfr_a : noCallFrameReturn a = true := by
        simp [noCallFrameReturn] at hncfr; exact hncfr.1
      have hexprwf_a : ExprAddrWF a sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf; exact hexprwf.1
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth a.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr a scope envVar envMap st).fst }
          { sc with expr := a }
          ev sa scope st (Flat.convertExpr a scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_a hexprwf_a
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.seq sc_sub'.expr b, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .seq a b } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        exact Core_step?_seq_step _ _ _ hcev _ _ hcstep_sub
      · simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
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
  | unary op arg =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hsc' : sc = { sc with expr := .unary op (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; simp [Core.step?, Core.exprValue?, Core.pushTrace]; rfl
      · simp only [sc']; simp [htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp only [sc']; simp [noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF]; exact evalUnary_valueAddrWF op cv sc.heap.objects.size (by simp [ExprAddrWF] at hexprwf; exact hexprwf)
      · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
        show (Flat.Expr.lit (Flat.evalUnary op (Flat.convertValue cv)), st) = Flat.convertExpr (.lit (Core.evalUnary op cv)) scope envVar envMap st
        rw [evalUnary_convertValue]; simp [Flat.convertExpr]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr arg scope envVar envMap st).fst = none :=
        convertExpr_not_value arg hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth arg.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst }
          { sc with expr := arg }
          ev sa scope st (Flat.convertExpr arg scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_arg hexprwf_arg
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.unary op sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | binary op lhs rhs =>
    rw [hsc] at hconv hncfr hexprwf hd
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
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · simp [sc', noCallFrameReturn]
        · simp [sc', ExprAddrWF]; exact evalBinary_valueAddrWF op lv rv sc.heap.objects.size
            (by simp [ExprAddrWF] at hexprwf; exact hexprwf.1)
            (by simp [ExprAddrWF] at hexprwf; exact hexprwf.2)
        · exact ⟨st, st, by
            simp [sc', Flat.convertExpr, evalBinary_convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
      | none =>
        -- rhs stepping, lhs is a value
        have hfnv : Flat.exprValue? (Flat.convertExpr rhs scope envVar envMap st).fst = none :=
          convertExpr_not_value rhs hrv scope envVar envMap st
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
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
          ih_depth rhs.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr rhs scope envVar envMap st).fst }
            { sc with expr := rhs }
            ev sa scope st (Flat.convertExpr rhs scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_rhs hexprwf_rhs
            (by simp)
            ⟨hsubstep⟩
        let sc' : Core.State :=
          ⟨.binary op (.lit lv) sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp only [sc']; simp only [ExprAddrWF]; exact ⟨by
            exact ValueAddrWF_mono (by simp [ExprAddrWF] at hexprwf; exact hexprwf.1) (Core_step_heap_size_mono hcstep_sub), hexprwf'⟩
        · exact ⟨st_a, st_a', by
            simp [sc', Flat.convertExpr, Flat.exprValue?]
            exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
    | none =>
      -- lhs stepping
      have hfnv : Flat.exprValue? (Flat.convertExpr lhs scope envVar envMap st).fst = none :=
        convertExpr_not_value lhs hlv scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth lhs.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr lhs scope envVar envMap st).fst }
          { sc with expr := lhs }
          ev sa scope st (Flat.convertExpr lhs scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_lhs hexprwf_lhs
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.binary op sc_sub'.expr rhs, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? f with
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr f scope envVar envMap st).fst = none :=
        convertExpr_not_value f hcev scope envVar envMap st
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
             hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth f.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr f scope envVar envMap st).fst }
          { sc with expr := f }
          ev sa scope st (Flat.convertExpr f scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_f hexprwf_f
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.call sc_sub'.expr args, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    | some cv => sorry -- callee is value: arg stepping or call execution
  | newObj f args => sorry
  | getProp obj prop =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv => sorry -- value sub-case (heap reasoning needed)
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value obj hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_arg hexprwf_arg
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.getProp sc_sub'.expr prop, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | setProp obj prop value =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv => sorry -- value sub-case (heap reasoning needed)
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value obj hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_obj hexprwf_obj
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.setProp sc_sub'.expr prop value, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv => sorry -- value sub-case (heap reasoning needed, skip for now)
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value obj hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_arg hexprwf_arg
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.getIndex sc_sub'.expr idx, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv => sorry -- value sub-case (heap reasoning needed)
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value obj hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_obj hexprwf_obj
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.setIndex sc_sub'.expr idx value, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcev : Core.exprValue? obj with
    | some cv => sorry -- value sub-case (heap reasoning needed, skip for now)
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr obj scope envVar envMap st).fst = none :=
        convertExpr_not_value obj hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth obj.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr obj scope envVar envMap st).fst }
          { sc with expr := obj }
          ev sa scope st (Flat.convertExpr obj scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_arg hexprwf_arg
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.deleteProp sc_sub'.expr prop, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | typeof arg =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hsc' : sc = { sc with expr := .typeof (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; simp [Core.step?, Core.exprValue?, Core.pushTrace]
        simp only [sc', coreResult]; cases cv <;> rfl
      · simp only [sc']; simp [htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp only [sc']; simp [noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF, ValueAddrWF, coreResult]
      · refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
        simp only [sc']; simp [Flat.convertExpr, Flat.convertValue, coreResult]
        cases cv <;> simp [Flat.convertValue]
    | none =>
      have hfnv : Flat.exprValue? (Flat.convertExpr arg scope envVar envMap st).fst = none :=
        convertExpr_not_value arg hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth arg.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst }
          { sc with expr := arg }
          ev sa scope st (Flat.convertExpr arg scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_arg hexprwf_arg
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.typeof sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | objectLit props => sorry
  | arrayLit elems =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    cases hcfnv : Core.firstNonValueExpr elems with
    | none =>
      sorry -- all elements are values: heap allocation (same class as other value sub-cases)
    | some val =>
      obtain ⟨done_c, target_c, rest_c⟩ := val
      have htarget_not_lit := Core.firstNonValueExpr_not_lit hcfnv
      have htarget_novalue : Core.exprValue? target_c = none := by
        cases target_c with
        | lit v => exact absurd rfl (htarget_not_lit v)
        | _ => rfl
      have hffnv := convertExprList_firstNonValueExpr_some elems scope envVar envMap st
          done_c target_c rest_c hcfnv htarget_novalue
      have hfnv_target : Flat.exprValue? (Flat.convertExpr target_c scope envVar envMap
          (Flat.convertExprList done_c scope envVar envMap st).snd).fst = none :=
        convertExpr_not_value target_c htarget_novalue scope envVar envMap _
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
        have hvals : Flat.valuesFromExprList? (Flat.convertExprList elems scope envVar envMap st).fst = none :=
          valuesFromExprList_none_of_firstNonValueExpr hffnv
        match hm : Flat.step? { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).fst } with
        | some (t, sa) =>
          have heq : Flat.step? { sf with expr := .arrayLit (Flat.convertExprList elems scope envVar envMap st).fst } =
              some (t, { expr := .arrayLit ((Flat.convertExprList done_c scope envVar envMap st).fst ++
                          [sa.expr] ++
                          (Flat.convertExprList rest_c scope envVar envMap
                            (Flat.convertExpr target_c scope envVar envMap
                              (Flat.convertExprList done_c scope envVar envMap st).snd).snd).fst),
                        env := sa.env, heap := sa.heap,
                        trace := sf.trace ++ [t], funcs := sf.funcs, callStack := sf.callStack }) := by
            simp only [Flat.step?, hvals, hffnv, hfnv_target, hm, Flat.pushTrace]
          rw [heq] at hstep; simp at hstep
          obtain ⟨rfl, hsf'eq⟩ := hstep
          exact ⟨sa, rfl, hsf'eq.symm⟩
        | none =>
          have heq : Flat.step? { sf with expr := .arrayLit (Flat.convertExprList elems scope envVar envMap st).fst } = none := by
            simp only [Flat.step?, hvals, hffnv, hfnv_target, hm]
          rw [heq] at hstep; exact absurd hstep (by simp)
      subst hsf'_eq
      have hdepth : target_c.depth < n := by
        simp [Core.Expr.depth] at hd
        have := Core.firstNonValueExpr_depth hcfnv; omega
      have ⟨hncfr_done, hncfr_target, hncfr_rest⟩ :=
        firstNonValueExpr_listNoCallFrameReturn hcfnv (by simp [noCallFrameReturn] at hncfr; exact hncfr)
      have hexprwf_target : ExprAddrWF target_c sc.heap.objects.size := by
        simp [ExprAddrWF] at hexprwf ⊢; trivial
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf',
              hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth target_c.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).fst }
          { sc with expr := target_c }
          ev sa scope
          (Flat.convertExprList done_c scope envVar envMap st).snd
          (Flat.convertExpr target_c scope envVar envMap
            (Flat.convertExprList done_c scope envVar envMap st).snd).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_target hexprwf_target
          (by simp)
          ⟨hsubstep⟩
      let sc' : Core.State :=
        ⟨.arrayLit (done_c ++ [sc_sub'.expr] ++ rest_c),
         sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- Core.step?
        show Core.step? sc = some (ev, sc')
        have hsc' : sc = { sc with expr := .arrayLit elems } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']
        have hcore_step := Core.step_arrayLit_step_elem elems sc.env sc.heap sc.trace sc.funcs sc.callStack
            done_c target_c rest_c hcfnv ev
            { expr := sc_sub'.expr, env := sc_sub'.env, heap := sc_sub'.heap,
              trace := sc.trace, funcs := sc_sub'.funcs, callStack := sc_sub'.callStack }
            (by convert hcstep_sub using 1 <;> simp)
        simp only [Core.pushTrace] at hcore_step
        convert hcore_step using 1
        simp [sc']
      · -- trace
        simp [sc', htrace, htrace_sub]
      · exact hinj'
      · exact henvCorr'
      · exact henvwf'
      · exact hheapvwf'
      · -- noCallFrameReturn
        simp only [sc', noCallFrameReturn]
        rw [listNoCallFrameReturn_append, listNoCallFrameReturn_append]
        simp [listNoCallFrameReturn, hncfr', hncfr_done, hncfr_rest]
      · -- ExprAddrWF (arrayLit is always True)
        simp [sc', ExprAddrWF]
      · -- CCState agreement
        -- Abbreviations for key intermediate states
        let st_done := (Flat.convertExprList done_c scope envVar envMap st).snd
        -- (a) convertExpr sc_sub'.expr with st_done gives same .fst as with st_a (from IH)
        have hconv_det := convertExpr_state_determined sc_sub'.expr scope envVar envMap
            st_done st_a hAgreeIn.1 hAgreeIn.2
        -- (b) Both target_c and sc_sub'.expr output states agree with st_a', hence with each other
        have hrest_agree : CCStateAgree
            (Flat.convertExpr target_c scope envVar envMap st_done).snd
            (Flat.convertExpr sc_sub'.expr scope envVar envMap st_done).snd :=
          ⟨hAgreeOut.1.trans hconv_det.2.1.symm, hAgreeOut.2.trans hconv_det.2.2.symm⟩
        -- (c) convertExprList rest_c gives same .fst/.snd agreement with both input states
        have hrest_det := convertExprList_state_determined rest_c scope envVar envMap _ _
            hrest_agree.1 hrest_agree.2
        -- (d) Decompose elems = done_c ++ [target_c] ++ rest_c
        have helems := firstNonValueExpr_decompose hcfnv
        -- Now construct: ∃ st_a st_a', (sf'.expr, st_a') = convertExpr sc'.expr ... st_a ∧ ...
        refine ⟨st,
          (Flat.convertExprList (done_c ++ [sc_sub'.expr] ++ rest_c) scope envVar envMap st).snd,
          ?_, ⟨rfl, rfl⟩, ?_⟩
        · -- (sf'.expr, st_a') = convertExpr (.arrayLit ...) ... st
          simp only [sc', Flat.convertExpr]
          constructor
          · -- sf'.expr = .arrayLit (convertExprList (done_c ++ [sc_sub'.expr] ++ rest_c) ... st).fst
            rw [convertExprList_append, convertExprList_append]
            simp only [Flat.convertExprList]
            rw [convertExprList_append_snd]
            -- Now need: sa.expr = (convertExpr sc_sub'.expr ... st_done).fst
            rw [show (Flat.convertExpr sc_sub'.expr scope envVar envMap st_done).fst = sa.expr from
              hconv_det.1.trans (congrArg Prod.fst hconv').symm]
            -- And: rest_c parts match
            rw [show (Flat.convertExprList rest_c scope envVar envMap
                (Flat.convertExpr sc_sub'.expr scope envVar envMap st_done).snd).fst =
              (Flat.convertExprList rest_c scope envVar envMap
                (Flat.convertExpr target_c scope envVar envMap st_done).snd).fst from
              hrest_det.1]
          · -- st_a' = (convertExprList (done_c ++ [sc_sub'.expr] ++ rest_c) ... st).snd
            rfl
        · -- CCStateAgree st' st_a'_outer
          rw [hst, helems]
          rw [convertExprList_append_snd, convertExprList_append_snd]
          simp only [Flat.convertExprList]
          rw [convertExprList_append_snd, convertExprList_append_snd]
          simp only [Flat.convertExprList]
          exact ⟨(convertExprList_state_determined rest_c scope envVar envMap _ _
            hrest_agree.1 hrest_agree.2).2.1,
            (convertExprList_state_determined rest_c scope envVar envMap _ _
            hrest_agree.1 hrest_agree.2).2.2⟩
  | functionDef fname params body isAsync isGen => sorry
  | throw val =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [valueToString_convertValue]
        have hsc' : sc = { sc with expr := .throw (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_throw_lit _ _
      · simp [sc', htrace, valueToString_convertValue]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', noCallFrameReturn]
      · simp [sc', ExprAddrWF, ValueAddrWF]
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      -- Sub-expression not a value; Flat steps the sub-expression
      have hfnv : Flat.exprValue? (Flat.convertExpr val scope envVar envMap st).fst = none :=
        convertExpr_not_value val hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth val.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr val scope envVar envMap st).fst }
          { sc with expr := val }
          ev sa scope st (Flat.convertExpr val scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_val hexprwf_val
          (by simp)
          ⟨hsubstep⟩
      -- Reconstruct Core step on throw
      let sc' : Core.State :=
        ⟨.throw sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simp [sc', noCallFrameReturn]; exact hncfr'
      · simp [sc', ExprAddrWF]; exact hexprwf'
      · exact ⟨st_a, st_a', by
          simp [sc', Flat.convertExpr]
          exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | tryCatch body catchParam catchBody finally_ => sorry
  | while_ cond body =>
    rw [hsc] at hconv hncfr hexprwf hd
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
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Core.step? sc = some (.silent, sc')
      have hsc' : sc = { sc with expr := .while_ cond body } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_while _ _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', noCallFrameReturn]; simp [noCallFrameReturn] at hncfr; exact ⟨hncfr.1, hncfr.2, hncfr.1, hncfr.2⟩
    · simp only [sc', ExprAddrWF, ValueAddrWF]; simp only [ExprAddrWF] at hexprwf
      exact ⟨hexprwf.1, ⟨hexprwf.2, hexprwf.1, hexprwf.2⟩, trivial⟩
    · -- Conversion relation: need convertExpr (.if cond (.seq body (.while_ cond body)) (.lit .undefined))
      -- to match sf'.expr. This requires CCState independence since while_ duplicates cond and body.
      sorry -- CCState threading: while_ lowering duplicates sub-expressions with different CCState
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
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«break» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_break] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("break:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hsc' : sc = { sc with expr := .«break» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_break _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «continue» label =>
    rw [hsc] at hconv hncfr hexprwf hd
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, hst⟩ := hconv
    have hsf_eta : sf = { sf with expr := .«continue» label } := by cases sf; simp_all
    rw [hsf_eta] at hstep
    rw [Flat_step?_continue] at hstep
    simp at hstep
    obtain ⟨hev, hsf'⟩ := hstep; subst hev hsf'
    let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
      sc.trace ++ [.error ("continue:" ++ label.getD "")], sc.funcs, sc.callStack⟩
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hsc' : sc = { sc with expr := .«continue» label } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_continue _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · simp [sc', noCallFrameReturn]
    · simp [sc', ExprAddrWF, ValueAddrWF]
    · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
  | «return» val =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Core.step? sc = some (.error "return:undefined", sc')
        have hsc' : sc = { sc with expr := .«return» none } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_return_none _
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
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
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [valueToString_convertValue]
          have hsc' : sc = { sc with expr := .«return» (some (.lit cv)) } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_return_some_lit _ _
        · simp [sc', htrace, valueToString_convertValue]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', noCallFrameReturn]
        · simp only [sc']; simp [ExprAddrWF] at hexprwf ⊢; exact hexprwf
        · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
      | none =>
        -- Sub-expression not a value; Flat steps the sub-expression
        have hfnv : Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none :=
          convertExpr_not_value e hcev scope envVar envMap st
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
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
          ih_depth e.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst }
            { sc with expr := e }
            ev sa scope st (Flat.convertExpr e scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_val hexprwf_val
            (by simp)
            ⟨hsubstep⟩
        -- Reconstruct Core step on return
        let sc' : Core.State :=
          ⟨.«return» (some sc_sub'.expr), sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp [sc', ExprAddrWF]; exact hexprwf'
        · exact ⟨st_a, st_a', by
            simp [sc', Flat.convertExpr, Flat.convertOptExpr]
            exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | labeled label body =>
    rw [hsc] at hconv hncfr hexprwf hd
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
    refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hsc' : sc = { sc with expr := .labeled label body } := by
        obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
      rw [hsc']; exact Core_step?_labeled _ _ _
    · simp [sc', htrace]
    · exact hinj
    · exact henvCorr
    · exact henvwf
    · exact hheapvwf
    · show noCallFrameReturn sc'.expr = true
      simp [sc']; exact hncfr
    · show ExprAddrWF sc'.expr sc'.heap.objects.size
      simp [sc']; exact hexprwf
    · exact ⟨st, (Flat.convertExpr body scope envVar envMap st).snd, by simp [sc'], ⟨rfl, rfl⟩, by first | (rw [hst']; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr] at hst'; subst hst'; exact ⟨rfl, rfl⟩)⟩
  | yield arg delegate =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Core.step? sc = some (.silent, sc')
        have hsc' : sc = { sc with expr := .yield none delegate } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_yield_none _ _
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
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
        refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show Core.step? sc = some (.silent, sc')
          have hsc' : sc = { sc with expr := .yield (some (.lit cv)) delegate } := by
            obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
          rw [hsc']; exact Core_step?_yield_some_lit _ _ _
        · simp [sc', htrace]
        · exact hinj
        · exact henvCorr
        · exact henvwf
        · exact hheapvwf
        · simp [sc', noCallFrameReturn]
        · simp only [sc']; simp [ExprAddrWF] at hexprwf ⊢; exact hexprwf
        · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
      | none =>
        -- Sub-expression not a value; Flat steps the sub-expression
        have hfnv : Flat.exprValue? (Flat.convertExpr e scope envVar envMap st).fst = none :=
          convertExpr_not_value e hcev scope envVar envMap st
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
        obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
          ih_depth e.depth hdepth envVar envMap injMap
            { sf with expr := (Flat.convertExpr e scope envVar envMap st).fst }
            { sc with expr := e }
            ev sa scope st (Flat.convertExpr e scope envVar envMap st).snd
            (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_val hexprwf_val
            (by simp)
            ⟨hsubstep⟩
        -- Reconstruct Core step on yield
        let sc' : Core.State :=
          ⟨.yield (some sc_sub'.expr) delegate, sc_sub'.env, sc_sub'.heap,
           sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
        refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · simp [sc', noCallFrameReturn]; exact hncfr'
        · simp [sc', ExprAddrWF]; exact hexprwf'
        · exact ⟨st_a, st_a', by
            simp [sc', Flat.convertExpr, Flat.convertOptExpr]
            exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩
  | await arg =>
    rw [hsc] at hconv hncfr hexprwf hd
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
      refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Core.step? sc = some (.silent, sc')
        have hsc' : sc = { sc with expr := .await (.lit cv) } := by
          obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
        rw [hsc']; exact Core_step?_await_lit _ _
      · simp [sc', htrace]
      · exact hinj
      · exact henvCorr
      · exact henvwf
      · exact hheapvwf
      · simp [sc', noCallFrameReturn]
      · simp only [sc']; simp [ExprAddrWF] at hexprwf ⊢; exact hexprwf
      · exact ⟨st, st, by simp [sc', Flat.convertExpr, Flat.convertValue], ⟨rfl, rfl⟩, by first | (subst hst_eq; exact ⟨rfl, rfl⟩) | (simp [Flat.convertExpr, Flat.convertValue, Flat.convertOptExpr] at hst; subst hst; exact ⟨rfl, rfl⟩) | (rw [hst]; exact ⟨rfl, rfl⟩) | (rw [hconv.2]; exact ⟨rfl, rfl⟩)⟩
    | none =>
      -- Sub-expression not a value; Flat steps the sub-expression
      have hfnv : Flat.exprValue? (Flat.convertExpr arg scope envVar envMap st).fst = none :=
        convertExpr_not_value arg hcev scope envVar envMap st
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
      obtain ⟨injMap', sc_sub', ⟨hcstep_sub⟩, htrace_sub, hinj', henvCorr', henvwf', hheapvwf', hncfr', hexprwf', st_a, st_a', hconv', hAgreeIn, hAgreeOut⟩ :=
        ih_depth arg.depth hdepth envVar envMap injMap
          { sf with expr := (Flat.convertExpr arg scope envVar envMap st).fst }
          { sc with expr := arg }
          ev sa scope st (Flat.convertExpr arg scope envVar envMap st).snd
          (by simp [Core.Expr.depth]) htrace hinj henvCorr henvwf hheapvwf hncfr_val hexprwf_val
          (by simp)
          ⟨hsubstep⟩
      -- Reconstruct Core step on await
      let sc' : Core.State :=
        ⟨.await sc_sub'.expr, sc_sub'.env, sc_sub'.heap,
         sc.trace ++ [ev], sc_sub'.funcs, sc_sub'.callStack⟩
      refine ⟨injMap', sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
                simp only [hstept] at h; exact absurd h (by simp)
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
                simp only [hstept] at h; exact absurd h (by simp)
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
