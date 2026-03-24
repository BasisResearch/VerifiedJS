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

/-- evalBinary commutes with convertValue for operators where Flat matches Core.
    NOTE: This is NOT true for all operators — Flat.evalBinary is simplified
    (e.g., .add with mixed string/non-string, .eq uses == not abstractEq,
    .lt uses numeric not abstractLt, bitwise/mod/exp/instanceof/in return .undefined).
    BLOCKED: waiting for wasmspec to align Flat.evalBinary with Core. -/
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
    cases a <;> cases b <;> simp [Core.evalBinary, Flat.evalBinary, Flat.convertValue, toNumber_convertValue, valueToString_convertValue]
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
    simp only [Core.evalBinary, Flat.evalBinary]
    congr 1; cases a <;> cases b <;> simp [Flat.convertValue, Flat.abstractEq, Core.abstractEq, Flat.toNumber, Core.toNumber]
  | neq =>
    simp only [Core.evalBinary, Flat.evalBinary]
    congr 1; congr 1; cases a <;> cases b <;> simp [Flat.convertValue, Flat.abstractEq, Core.abstractEq, Flat.toNumber, Core.toNumber]
  | lt =>
    simp only [Core.evalBinary, Flat.evalBinary]
    congr 1; cases a <;> cases b <;> simp [Flat.convertValue, Flat.abstractLt, Core.abstractLt, Flat.toNumber, Core.toNumber]
  | gt =>
    simp only [Core.evalBinary, Flat.evalBinary]
    congr 1; cases a <;> cases b <;> simp [Flat.convertValue, Flat.abstractLt, Core.abstractLt, Flat.toNumber, Core.toNumber]
  | le =>
    simp only [Core.evalBinary, Flat.evalBinary]
    congr 1; congr 1; cases a <;> cases b <;> simp [Flat.convertValue, Flat.abstractLt, Core.abstractLt, Flat.toNumber, Core.toNumber]
  | ge =>
    simp only [Core.evalBinary, Flat.evalBinary]
    congr 1; congr 1; cases a <;> cases b <;> simp [Flat.convertValue, Flat.abstractLt, Core.abstractLt, Flat.toNumber, Core.toNumber]
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
        subst this; simp [beq_comm] at hne ⊢; exact hne
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
  · have hne' : (name == other) = false := by simp [beq_comm] at hne ⊢; exact hne
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
    simp only [Flat.convertExpr]
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
  decreasing_by all_goals (try cases ‹Option Core.Expr›) <;> simp_all <;> omega

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
  decreasing_by all_goals simp_all <;> omega

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
  decreasing_by all_goals simp_all <;> omega

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

/-- Returns true if the expression never uses "__call_frame_return__" as a tryCatch catchParam.
    Source programs from `elaborate` satisfy this predicate since "__call_frame_return__" is only
    introduced by the Core interpreter for call-frame returns. -/
mutual
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
  · simp only [Array.size_push]; rw [hsize]
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

/-- All object addresses in a Core value are valid heap addresses. -/
private def ValueAddrWF (v : Core.Value) (heapSize : Nat) : Prop :=
  match v with
  | .object addr => addr < heapSize
  | _ => True

/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
private def ExprAddrWF : Core.Expr → Nat → Prop
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

private theorem ExprAddrWF_mono {e : Core.Expr} {n m : Nat}
    (h : ExprAddrWF e n) (hle : n ≤ m) : ExprAddrWF e m := by
  sorry

/-- Simulation relation for closure conversion: Flat and Core states
    have matching traces, environment correspondence, and expression
    correspondence through the conversion. -/
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  EnvCorr sc.env sf.env ∧
  HeapCorr sc.heap sf.heap ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st

private theorem closureConvert_init_related
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1 := by trivial) :
    CC_SimRel s t (Flat.initialState t) (Core.initialState s) := by
  unfold CC_SimRel Flat.initialState Core.initialState
  refine ⟨rfl, ?_, HeapCorr_refl _, h_wf, ?_, ?_⟩
  · -- EnvCorr: both envs have exactly one binding: "console" → .object 0
    have h_empty : EnvCorr Core.Env.empty Flat.Env.empty := by
      constructor <;> intro _ _ h <;> simp [Core.Env.empty, Core.Env.lookup, Flat.Env.empty, Flat.Env.lookup] at h
    exact EnvCorr_extend h_empty "console" (.object 0)
  · -- ExprAddrWF: source programs don't contain .object addresses
    exact h_addr_wf
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
  cases e <;> simp [Core.exprValue?] at h <;> simp [Flat.convertExpr, Flat.exprValue?]
  all_goals (first | rfl | (try split) <;> simp [Flat.exprValue?])

private theorem closureConvert_step_simulation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State),
      CC_SimRel s t sf sc → Flat.Step sf ev sf' →
      ∃ sc', Core.Step sc ev sc' ∧ CC_SimRel s t sf' sc' := by
  -- Strong induction on expression depth enables proving stepping sub-cases.
  -- envVar and envMap are universally quantified in the suffices so that ih_depth
  -- preserves them across recursive calls (needed for compound stepping sub-cases).
  suffices ∀ (n : Nat) (envVar : String) (envMap : Flat.EnvMapping)
      (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State),
      sc.expr.depth = n → sf.trace = sc.trace → EnvCorr sc.env sf.env →
      HeapCorr sc.heap sf.heap → noCallFrameReturn sc.expr = true →
      ExprAddrWF sc.expr sc.heap.objects.size →
      (∃ (scope : List String) (st st' : Flat.CCState),
        (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st) →
      Flat.Step sf ev sf' →
      ∃ sc', Core.Step sc ev sc' ∧ sf'.trace = sc'.trace ∧ EnvCorr sc'.env sf'.env ∧
        HeapCorr sc'.heap sf'.heap ∧ noCallFrameReturn sc'.expr = true ∧
        ExprAddrWF sc'.expr sc'.heap.objects.size ∧
        (∃ (scope : List String) (st st' : Flat.CCState),
          (sf'.expr, st') = Flat.convertExpr sc'.expr scope envVar envMap st) by
    intro sf sc ev sf' ⟨htrace, henvCorr, hheap, hncfr, hexprwf, scope, envVar, envMap, st, st', hconv⟩ hstep
    obtain ⟨sc', hcstep, htrace', henv', hheap', hncfr', hexprwf', scope', st_a, st_a', hconv'⟩ :=
      this sc.expr.depth envVar envMap sf sc ev sf' rfl htrace henvCorr hheap hncfr hexprwf ⟨scope, st, st', hconv⟩ hstep
    exact ⟨sc', hcstep, htrace', henv', hheap', hncfr', hexprwf', scope', envVar, envMap, st_a, st_a', hconv'⟩
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_depth =>
  intro envVar envMap sf sc ev sf' hd htrace henvCorr hheap hncfr hexprwf ⟨scope, st, st', hconv⟩ ⟨hstep⟩
  -- Case analysis on the Core expression sc.expr.
  -- convertExpr maps sc.expr to sf.expr; step? sf = some (ev, sf').
  cases hsc : sc.expr with
  | lit v =>
    -- convertExpr (.lit v) = (.lit (convertValue v), st)
    -- Flat.step? on .lit = none, contradicting hstep
    exfalso
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have := (Prod.mk.inj hconv).1
    have hsf : sf.expr = .lit (Flat.convertValue v) := by cases sf; simp_all
    have : Flat.step? sf = none := by rw [show sf = { sf with expr := .lit (Flat.convertValue v) } from by cases sf; simp_all]; exact Flat.step?_lit_none sf (Flat.convertValue v)
    simp [this] at hstep
  | forIn _binding _obj _body =>
    -- convertExpr (.forIn ..) = (.lit .undefined, st)
    -- Flat.step? on .lit = none, contradicting hstep
    exfalso
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf : sf.expr = .lit .undefined := by cases sf; simp_all [(Prod.mk.inj hconv).1]
    have : Flat.step? sf = none := by rw [show sf = { sf with expr := .lit .undefined } from by cases sf; simp_all]; exact Flat.step?_lit_none sf .undefined
    simp [this] at hstep
  | forOf _binding _iterable _body =>
    -- Same as forIn
    exfalso
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf : sf.expr = .lit .undefined := by cases sf; simp_all [(Prod.mk.inj hconv).1]
    have : Flat.step? sf = none := by rw [show sf = { sf with expr := .lit .undefined } from by cases sf; simp_all]; exact Flat.step?_lit_none sf .undefined
    simp [this] at hstep
  -- All remaining constructors: env/heap correspondence needed for full proof.
  -- CC_SimRel currently only tracks trace + expression correspondence.
  -- TODO: Strengthen CC_SimRel to include env/heap/funcs correspondence,
  -- then prove each constructor case. Key architectural issue: the convertExpr
  -- correspondence breaks after control-flow unrolling (e.g., while_ → if/seq/while)
  -- because re-converting the unrolled expression may produce different fresh names.
  -- Fix: either (a) prove convertExpr is state-independent for functionDef-free exprs,
  -- (b) use a weaker structural bisimulation instead of convertExpr correspondence, or
  -- (c) use a logical/step-indexed relation.
  -- Remaining constructors require env/heap/funcs correspondence in CC_SimRel.
  -- Currently CC_SimRel only tracks trace + expression conversion correspondence.
  -- Need to strengthen CC_SimRel before these cases can be proved.
  | «break» label =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .«break» label := by cases sf; simp_all [(Prod.mk.inj hconv).1]
    obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.error ("break:" ++ (label.getD "")), sc') := by
      rw [show sc = {sc with expr := .«break» label} from by cases sc; simp_all]
      simp only [Core.step?]; cases label <;> exact ⟨_, rfl⟩
    have hflat_ev : ev = .error ("break:" ++ (label.getD "")) := by
      rw [show sf = {sf with expr := .«break» label} from by cases sf; simp_all] at hstep
      simp only [Flat.step?] at hstep; exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
    subst hflat_ev
    refine ⟨sc', ⟨hcstep⟩, ?_⟩
    have hsf'_expr : sf'.expr = .lit .undefined := by
      have h0 := hstep
      rw [show sf = {sf with expr := .«break» label} from by cases sf; simp_all] at h0
      simp only [Flat.step?] at h0
      exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
    have hsc'_expr : sc'.expr = .lit .undefined := by
      have h0 := hcstep
      rw [show sc = {sc with expr := .«break» label} from by cases sc; simp_all] at h0
      simp only [Core.step?] at h0
      cases label <;> (exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl)
    have hsf'_trace_eq_sc'_trace : sf'.trace = sc'.trace := by
      have hf := hstep; have hc := hcstep
      rw [show sf = {sf with expr := .«break» label} from by cases sf; simp_all] at hf
      rw [show sc = {sc with expr := .«break» label} from by cases sc; simp_all] at hc
      cases label with
      | some l =>
        simp only [Flat.step?, Option.getD] at hf; simp only [Core.step?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      | none =>
        simp only [Flat.step?, Option.getD, String.append_empty] at hf
        simp only [Core.step?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
    have henv' : EnvCorr sc'.env sf'.env := by
      have hsf'_env : sf'.env = sf.env := by
        have h0 := hstep
        rw [show sf = {sf with expr := .«break» label} from by cases sf; simp_all] at h0
        simp only [Flat.step?] at h0
        have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
      have hsc'_env : sc'.env = sc.env := by
        have h0 := hcstep
        rw [show sc = {sc with expr := .«break» label} from by cases sc; simp_all] at h0
        simp only [Core.step?] at h0
        cases label <;> (have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl)
      rw [hsc'_env, hsf'_env]; exact henvCorr
    have hheap' : HeapCorr sc'.heap sf'.heap := by
      have h0 := hstep
      rw [show sf = {sf with expr := .«break» label} from by cases sf; simp_all] at h0
      simp only [Flat.step?] at h0
      have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
      have h0 := hcstep
      rw [show sc = {sc with expr := .«break» label} from by cases sc; simp_all] at h0
      simp only [Core.step?] at h0
      cases label <;> (have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap)
    exact ⟨hsf'_trace_eq_sc'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st', st', by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
  | «continue» label =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .«continue» label := by cases sf; simp_all [(Prod.mk.inj hconv).1]
    obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.error ("continue:" ++ (label.getD "")), sc') := by
      rw [show sc = {sc with expr := .«continue» label} from by cases sc; simp_all]
      simp only [Core.step?]; cases label <;> exact ⟨_, rfl⟩
    have hflat_ev : ev = .error ("continue:" ++ (label.getD "")) := by
      rw [show sf = {sf with expr := .«continue» label} from by cases sf; simp_all] at hstep
      simp only [Flat.step?] at hstep; exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
    subst hflat_ev
    refine ⟨sc', ⟨hcstep⟩, ?_⟩
    have hsf'_expr : sf'.expr = .lit .undefined := by
      have h0 := hstep
      rw [show sf = {sf with expr := .«continue» label} from by cases sf; simp_all] at h0
      simp only [Flat.step?] at h0
      exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
    have hsc'_expr : sc'.expr = .lit .undefined := by
      have h0 := hcstep
      rw [show sc = {sc with expr := .«continue» label} from by cases sc; simp_all] at h0
      simp only [Core.step?] at h0
      cases label <;> (exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl)
    have hsf'_trace_eq_sc'_trace : sf'.trace = sc'.trace := by
      have hf := hstep; have hc := hcstep
      rw [show sf = {sf with expr := .«continue» label} from by cases sf; simp_all] at hf
      rw [show sc = {sc with expr := .«continue» label} from by cases sc; simp_all] at hc
      cases label with
      | some l =>
        simp only [Flat.step?, Option.getD] at hf; simp only [Core.step?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      | none =>
        simp only [Flat.step?, Option.getD, String.append_empty] at hf
        simp only [Core.step?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
    have henv' : EnvCorr sc'.env sf'.env := by
      have hsf'_env : sf'.env = sf.env := by
        have h0 := hstep
        rw [show sf = {sf with expr := .«continue» label} from by cases sf; simp_all] at h0
        simp only [Flat.step?] at h0
        have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
      have hsc'_env : sc'.env = sc.env := by
        have h0 := hcstep
        rw [show sc = {sc with expr := .«continue» label} from by cases sc; simp_all] at h0
        simp only [Core.step?] at h0
        cases label <;> (have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl)
      rw [hsc'_env, hsf'_env]; exact henvCorr
    have hheap' : HeapCorr sc'.heap sf'.heap := by
      have h0 := hstep
      rw [show sf = {sf with expr := .«continue» label} from by cases sf; simp_all] at h0
      simp only [Flat.step?] at h0
      have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
      have h0 := hcstep
      rw [show sc = {sc with expr := .«continue» label} from by cases sc; simp_all] at h0
      simp only [Core.step?] at h0
      cases label <;> (have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap)
    exact ⟨hsf'_trace_eq_sc'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st', st', by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
  | labeled label body =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    -- convertExpr (.labeled label body) = (.labeled label body', st1)
    -- where (body', st1) = convertExpr body scope envVar envMap st
    have hsf_expr : sf.expr = .labeled label (Flat.convertExpr body scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    -- Flat.step? on .labeled produces .silent and steps to body'
    have hflat_ev : ev = .silent := by
      rw [show sf = {sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).1} from by cases sf; simp_all] at hstep
      simp only [Flat.step?] at hstep; exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
    subst hflat_ev
    -- Core.step? on .labeled produces .silent and steps to body
    obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
      rw [show sc = {sc with expr := .labeled label body} from by cases sc; simp_all]
      simp only [Core.step?]; exact ⟨_, rfl⟩
    refine ⟨sc', ⟨hcstep⟩, ?_⟩
    -- Show CC_SimRel for resulting states
    have hsf'_expr : sf'.expr = (Flat.convertExpr body scope envVar envMap st).1 := by
      have h0 := hstep
      rw [show sf = {sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).1} from by cases sf; simp_all] at h0
      simp only [Flat.step?] at h0
      exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
    have hsc'_expr : sc'.expr = body := by
      have h0 := hcstep
      rw [show sc = {sc with expr := .labeled label body} from by cases sc; simp_all] at h0
      simp only [Core.step?] at h0
      exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
    have hsf'_trace_eq_sc'_trace : sf'.trace = sc'.trace := by
      have hf := hstep; have hc := hcstep
      rw [show sf = {sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).1} from by cases sf; simp_all] at hf
      rw [show sc = {sc with expr := .labeled label body} from by cases sc; simp_all] at hc
      simp only [Flat.step?] at hf; simp only [Core.step?] at hc
      have heqf := (Prod.mk.inj (Option.some.inj hf)).2
      have heqc := (Prod.mk.inj (Option.some.inj hc)).2
      subst heqf; subst heqc
      show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
    have henv' : EnvCorr sc'.env sf'.env := by
      have hsf'_env : sf'.env = sf.env := by
        have h0 := hstep
        rw [show sf = {sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).1} from by cases sf; simp_all] at h0
        simp only [Flat.step?] at h0
        have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
      have hsc'_env : sc'.env = sc.env := by
        have h0 := hcstep
        rw [show sc = {sc with expr := .labeled label body} from by cases sc; simp_all] at h0
        simp only [Core.step?] at h0
        have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
      rw [hsc'_env, hsf'_env]; exact henvCorr
    have hheap' : HeapCorr sc'.heap sf'.heap := by
      have h0 := hstep
      rw [show sf = {sf with expr := .labeled label (Flat.convertExpr body scope envVar envMap st).1} from by cases sf; simp_all] at h0
      simp only [Flat.step?] at h0
      have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
      have h0 := hcstep
      rw [show sc = {sc with expr := .labeled label body} from by cases sc; simp_all] at h0
      simp only [Core.step?] at h0
      have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
    exact ⟨hsf'_trace_eq_sc'_trace, henv', hheap', by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn] at h; rw [hsc'_expr]; exact h, sorry /- ExprAddrWF -/, scope, st,
      (Flat.convertExpr body scope envVar envMap st).2,
      by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
  -- Remaining cases require env/heap correspondence in CC_SimRel.
  -- ARCHITECTURAL NOTE: `.return`, `.yield`, `.await` produce DIFFERENT events
  -- in Core (.error) vs Flat (.silent), so step_simulation as stated is FALSE
  -- for those cases. Need observable-trace equivalence instead.
  | var name =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    -- Case split on whether the variable is captured
    cases hlookup : Flat.lookupEnv envMap name with
    | some idx =>
      -- Captured variable: convertExpr produces .getEnv (.var envVar) idx
      -- Needs heap correspondence to prove — leave for later
      sorry
    | none =>
      -- In-scope variable: convertExpr produces .var name
      have hsf_expr : sf.expr = .var name := by
        rw [hlookup] at hconv; cases sf; simp_all [(Prod.mk.inj hconv).1]
      -- Case split on Flat env lookup
      cases hfenv : sf.env.lookup name with
      | some fv =>
        -- EnvCorr gives Core also has this variable
        obtain ⟨cv, hcenv, hfv_eq⟩ := henvCorr.1 name fv hfenv
        -- Flat produces .silent, Core produces .silent
        have hflat_ev : ev = .silent := by
          rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at hstep
          simp only [Flat.step?, hfenv] at hstep
          exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
        subst hflat_ev
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
          rw [show sc = {sc with expr := .var name} from by cases sc; simp_all]
          simp only [Core.step?, hcenv]; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        have hsf'_trace : sf'.trace = sc'.trace := by
          have hf := hstep; have hc := hcstep
          rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at hf
          rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at hc
          simp only [Flat.step?, hfenv] at hf; simp only [Core.step?, hcenv] at hc
          have heqf := (Prod.mk.inj (Option.some.inj hf)).2
          have heqc := (Prod.mk.inj (Option.some.inj hc)).2
          subst heqf; subst heqc
          show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
        have henv' : EnvCorr sc'.env sf'.env := by
          have hsf'_env : sf'.env = sf.env := by
            have h0 := hstep
            rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at h0
            simp only [Flat.step?, hfenv] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          have hsc'_env : sc'.env = sc.env := by
            have h0 := hcstep
            rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at h0
            simp only [Core.step?, hcenv] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          rw [hsc'_env, hsf'_env]; exact henvCorr
        have hsf'_expr : sf'.expr = .lit fv := by
          have h0 := hstep
          rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at h0
          simp only [Flat.step?, hfenv] at h0
          exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hsc'_expr : sc'.expr = .lit cv := by
          have h0 := hcstep
          rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at h0
          simp only [Core.step?, hcenv] at h0
          exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hheap' : HeapCorr sc'.heap sf'.heap := by
          have h0 := hstep
          rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at h0
          simp only [Flat.step?, hfenv] at h0
          have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
          have h0 := hcstep
          rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at h0
          simp only [Core.step?, hcenv] at h0
          have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
        exact ⟨hsf'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st,
          (Flat.convertExpr (.lit cv) scope envVar envMap st).2,
          by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr, hfv_eq]⟩
      | none =>
        -- Flat doesn't find var → produces ReferenceError
        have hflat_ev : ev = .error ("ReferenceError: " ++ name) := by
          rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at hstep
          simp only [Flat.step?, hfenv] at hstep
          exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
        subst hflat_ev
        cases hcenv : sc.env.lookup name with
        | none =>
          -- Both produce ReferenceError
          obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.error ("ReferenceError: " ++ name), sc') := by
            rw [show sc = {sc with expr := .var name} from by cases sc; simp_all]
            simp only [Core.step?, hcenv]; exact ⟨_, rfl⟩
          refine ⟨sc', ⟨hcstep⟩, ?_⟩
          have hsf'_trace : sf'.trace = sc'.trace := by
            have hf := hstep; have hc := hcstep
            rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at hf
            rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at hc
            simp only [Flat.step?, hfenv] at hf; simp only [Core.step?, hcenv] at hc
            have heqf := (Prod.mk.inj (Option.some.inj hf)).2
            have heqc := (Prod.mk.inj (Option.some.inj hc)).2
            subst heqf; subst heqc
            show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
          have henv' : EnvCorr sc'.env sf'.env := by
            have hsf'_env : sf'.env = sf.env := by
              have h0 := hstep
              rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at h0
              simp only [Flat.step?, hfenv] at h0
              have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
            have hsc'_env : sc'.env = sc.env := by
              have h0 := hcstep
              rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at h0
              simp only [Core.step?, hcenv] at h0
              have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
            rw [hsc'_env, hsf'_env]; exact henvCorr
          have hsf'_expr : sf'.expr = .lit .undefined := by
            have h0 := hstep
            rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at h0
            simp only [Flat.step?, hfenv] at h0
            exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
          have hsc'_expr : sc'.expr = .lit .undefined := by
            have h0 := hcstep
            rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at h0
            simp only [Core.step?, hcenv] at h0
            exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
          have hheap' : HeapCorr sc'.heap sf'.heap := by
            have h0 := hstep
            rw [show sf = {sf with expr := .var name} from by cases sf; simp_all] at h0
            simp only [Flat.step?, hfenv] at h0
            have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
            have h0 := hcstep
            rw [show sc = {sc with expr := .var name} from by cases sc; simp_all] at h0
            simp only [Core.step?, hcenv] at h0
            have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
          exact ⟨hsf'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
            by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
        | some cv =>
          -- Core has the var but Flat doesn't → contradiction via EnvCorr.2
          exfalso
          obtain ⟨fv, hfenv', _⟩ := henvCorr.2 name cv hcenv
          simp [hfenv] at hfenv'
  | «let» name init body =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .«let» name (Flat.convertExpr init scope envVar envMap st).fst
        (Flat.convertExpr body (name :: scope) envVar envMap (Flat.convertExpr init scope envVar envMap st).snd).fst := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? init with
    | some v =>
      have ha_lit : init = .lit v := by cases init <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      -- sf.expr = .let name (.lit (convertValue v)) (convertExpr body (name::scope) ... st).1
      -- Both step to body/body' with env extended, event .silent
      have hsf_rw : sf = ⟨Flat.Expr.«let» name (.lit (Flat.convertValue v)) (Flat.convertExpr body (name :: scope) envVar envMap st).fst, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.«let» name (.lit v) body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env.extend name (Flat.convertValue v) := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env.extend name v := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact EnvCorr_extend henvCorr name v
      have hsf'_expr : sf'.expr = (Flat.convertExpr body (name :: scope) envVar envMap st).fst := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?, Flat.exprValue?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = body := by
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?, Core.exprValue?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      exact ⟨hsf'_trace, henv', by
        have h0 := hstep; rw [hsf_rw] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := hcstep; rw [hsc_rw] at h1; simp only [Core.step?, Core.exprValue?] at h1
        have := (Prod.mk.inj (Option.some.inj h0)).2; have := (Prod.mk.inj (Option.some.inj h1)).2
        subst_vars; exact hheap, name :: scope, st,
        (Flat.convertExpr body (name :: scope) envVar envMap st).snd,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
    | none =>
      -- Stepping sub-case: init is not a value
      set init' := (Flat.convertExpr init scope envVar envMap st).1 with hinit'_def
      set st1 := (Flat.convertExpr init scope envVar envMap st).2 with hst1_def
      set body' := (Flat.convertExpr body (name :: scope) envVar envMap st1).1 with hbody'_def
      have hinit'_nv : Flat.exprValue? init' = none := convertExpr_not_value init hval scope envVar envMap st
      have hsf_rw : sf = ⟨.«let» name init' body', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hdepth : Core.Expr.depth init < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hinit'_nv] at hstep
      cases hsubstep : Flat.step? ⟨init', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨init', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth init) hdepth envVar envMap
          ⟨init', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨init, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hinit'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        have hcore_let : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .«let» name sc_arg.expr body, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.«let» name init body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_let_step_init name init body sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨init, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := init } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .«let» name sc_arg.expr body, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_let⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .«let» name sa_flat.expr body' := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .«let» name sc_arg.expr body := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          refine ⟨scope', st_a, ?_, ?_⟩
          · exact (Flat.convertExpr body (name :: scope') envVar envMap
              (Flat.convertExpr sc_arg.expr scope' envVar envMap st_a).2).2
          · simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
            congr 1
            · congr 1
              · congr 1
                rw [hbody'_def, hst1_def]
                rw [convertExpr_scope_irrelevant body (name :: scope) (name :: scope') envVar envMap
                  (Flat.convertExpr init scope envVar envMap st).2]
                rfl
              · rw [hbody'_def, hst1_def]
                rw [convertExpr_scope_irrelevant body (name :: scope) (name :: scope') envVar envMap
                  (Flat.convertExpr init scope envVar envMap st).2]
                rfl
            · rw [hbody'_def, hst1_def]
              rw [convertExpr_scope_irrelevant body (name :: scope) (name :: scope') envVar envMap
                (Flat.convertExpr init scope envVar envMap st).2]
              rfl
  | assign name value =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .assign name (Flat.convertExpr value scope envVar envMap st).fst := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? value with
    | some v =>
      have ha_lit : value = .lit v := by cases value <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      -- sf.expr = .assign name (.lit (convertValue v))
      -- Both step with .silent, env gets assigned
      have hsf_rw : sf = ⟨Flat.Expr.assign name (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.assign name (.lit v), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env.assign name (Flat.convertValue v) := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env.assign name v := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact EnvCorr_assign henvCorr name v
      have hsf'_expr : sf'.expr = .lit (Flat.convertValue v) := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?, Flat.exprValue?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = .lit v := by
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?, Core.exprValue?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      exact ⟨hsf'_trace, henv', by
        have h0 := hstep; rw [hsf_rw] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := hcstep; rw [hsc_rw] at h1; simp only [Core.step?, Core.exprValue?] at h1
        have := (Prod.mk.inj (Option.some.inj h0)).2; have := (Prod.mk.inj (Option.some.inj h1)).2
        subst_vars; exact hheap, by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st,
        (Flat.convertExpr (.lit v) scope envVar envMap st).snd,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
    | none =>
      -- value' is the converted sub-expression
      set value' := (Flat.convertExpr value scope envVar envMap st).1 with hvalue'_def
      set st1 := (Flat.convertExpr value scope envVar envMap st).2 with hst1_def
      have hvalue'_nv : Flat.exprValue? value' = none := convertExpr_not_value value hval scope envVar envMap st
      have hsf_rw : sf = ⟨.assign name value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      -- Depth of value < n
      have hdepth : Core.Expr.depth value < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      -- Extract Flat sub-step: step? on .assign name value' with non-value value' delegates to step? value'
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hvalue'_nv] at hstep
      -- Case split on step? of value'
      cases hsubstep : Flat.step? ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        -- Flat.Step for sub-expression
        have hflat_step_sub : Flat.Step ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        -- Apply IH (envVar/envMap carried through induction)
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth value) hdepth envVar envMap
          ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp only [noCallFrameReturn] at h; exact h) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hvalue'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        -- Construct Core step on .assign name value using step_assign_step_rhs
        have hcore_assign : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .assign name sc_arg.expr, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.assign name value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_assign_step_rhs name value sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := value } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .assign name sc_arg.expr, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_assign⟩, ?_⟩
        constructor
        · -- Trace
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]
          show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]
          rw [htrace]
        constructor
        · -- EnvCorr
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]
          convert henvCorr_arg using 1
          rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · -- Expression correspondence
          refine ⟨scope', st_a, st_a', ?_⟩
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .assign name sa_flat.expr := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .assign name sc_arg.expr := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          simp only [Flat.convertExpr]
          rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
            (sa_flat.expr, st_a') from hconv_arg.symm]
  | «if» cond then_ else_ =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .«if» (Flat.convertExpr cond scope envVar envMap st).1
        (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).2).1
        (Flat.convertExpr else_ scope envVar envMap
          (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).2).2).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? cond with
    | some v =>
      have hcond_lit : cond = .lit v := by
        cases cond <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst hcond_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.«if» (.lit (Flat.convertValue v))
          (Flat.convertExpr then_ scope envVar envMap st).fst
          (Flat.convertExpr else_ scope envVar envMap
            (Flat.convertExpr then_ scope envVar envMap st).snd).fst,
          sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.«if» (.lit v) then_ else_, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      have hbool_eq : Flat.toBoolean (Flat.convertValue v) = Core.toBoolean v :=
        toBoolean_convertValue v
      have hsf'_expr : sf'.expr = if Flat.toBoolean (Flat.convertValue v)
          then (Flat.convertExpr then_ scope envVar envMap st).fst
          else (Flat.convertExpr else_ scope envVar envMap
            (Flat.convertExpr then_ scope envVar envMap st).snd).fst := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?, Flat.exprValue?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = if Core.toBoolean v then then_ else else_ := by
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?, Core.exprValue?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hheap' : HeapCorr sc'.heap sf'.heap := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?, Core.exprValue?] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
      cases hb : Core.toBoolean v with
      | true =>
        simp only [hbool_eq, hb, ite_true] at hsf'_expr hsc'_expr
        exact ⟨hsf'_trace, henv', hheap', by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; rw [hsc'_expr]; exact h.2.1, sorry /- ExprAddrWF -/, scope, st,
          (Flat.convertExpr then_ scope envVar envMap st).snd,
          by rw [hsc'_expr]; simp [hsf'_expr]⟩
      | false =>
        simp only [hbool_eq, hb, ite_false] at hsf'_expr hsc'_expr
        exact ⟨hsf'_trace, henv', hheap', by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; rw [hsc'_expr]; exact h.2.2, sorry /- ExprAddrWF -/, scope,
          (Flat.convertExpr then_ scope envVar envMap st).snd,
          (Flat.convertExpr else_ scope envVar envMap
            (Flat.convertExpr then_ scope envVar envMap st).snd).snd,
          by rw [hsc'_expr]; simp [hsf'_expr]⟩
    | none =>
      -- Stepping sub-case: cond is not a value, need recursive step simulation
      set cond' := (Flat.convertExpr cond scope envVar envMap st).1 with hcond'_def
      set st1 := (Flat.convertExpr cond scope envVar envMap st).2 with hst1_def
      set then' := (Flat.convertExpr then_ scope envVar envMap st1).1 with hthen'_def
      set else' := (Flat.convertExpr else_ scope envVar envMap
        (Flat.convertExpr then_ scope envVar envMap st1).2).1 with helse'_def
      have hcond'_nv : Flat.exprValue? cond' = none := convertExpr_not_value cond hval scope envVar envMap st
      have hsf_rw : sf = ⟨.«if» cond' then' else', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      -- Depth of cond < n
      have hdepth : Core.Expr.depth cond < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      -- Extract Flat sub-step
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hcond'_nv] at hstep
      cases hsubstep : Flat.step? ⟨cond', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨cond', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        -- Apply IH
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth cond) hdepth envVar envMap
          ⟨cond', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨cond, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hcond'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        -- Construct Core step using step_if_step_cond
        have hcore_if : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .«if» sc_arg.expr then_ else_, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.«if» cond then_ else_, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_if_step_cond cond then_ else_ sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨cond, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := cond } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .«if» sc_arg.expr then_ else_, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_if⟩, ?_⟩
        constructor
        · -- Trace
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]
          show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]
          rw [htrace]
        constructor
        · -- EnvCorr
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]
          convert henvCorr_arg using 1
          rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · -- Expression correspondence
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .«if» sa_flat.expr then' else' := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .«if» sc_arg.expr then_ else_ := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          refine ⟨scope', st_a, ?_, ?_⟩
          · exact (Flat.convertExpr else_ scope' envVar envMap
              (Flat.convertExpr then_ scope' envVar envMap
                (Flat.convertExpr sc_arg.expr scope' envVar envMap st_a).2).2).2
          · simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
            congr 1
            · congr 1
              · congr 1
                rw [hthen'_def, hst1_def]
                rw [convertExpr_scope_irrelevant then_ scope scope' envVar envMap
                  (Flat.convertExpr cond scope envVar envMap st).2]
                rfl
              · rw [helse'_def, hst1_def]
                rw [convertExpr_scope_irrelevant else_ scope scope' envVar envMap _]
                congr 1
                rw [convertExpr_scope_irrelevant then_ scope scope' envVar envMap
                  (Flat.convertExpr cond scope envVar envMap st).2]
                rfl
            · rw [helse'_def, hst1_def]
              rw [convertExpr_scope_irrelevant else_ scope scope' envVar envMap _]
              congr 1
              rw [convertExpr_scope_irrelevant then_ scope scope' envVar envMap
                (Flat.convertExpr cond scope envVar envMap st).2]
              rfl
  | seq a b =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .seq (Flat.convertExpr a scope envVar envMap st).1
        (Flat.convertExpr b scope envVar envMap (Flat.convertExpr a scope envVar envMap st).2).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    -- Case split on whether a is already a value
    cases hval : Core.exprValue? a with
    | some v =>
      -- a is .lit v
      have ha_lit : a = .lit v := by cases a <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      -- After subst, convertExpr (.lit v) = (.lit (convertValue v), st)
      simp only [Flat.convertExpr] at hsf_expr hconv
      -- Now sf.expr = .seq (.lit (convertValue v)) b' where b' = convertExpr b ... st
      -- hsf_expr: sf.expr = .seq (.lit (convertValue v)) (convertExpr b ... st).1
      -- Reconstruct sf with known expr for rewriting
      have hsf_rw : sf = ⟨Flat.Expr.seq (.lit (Flat.convertValue v)) (Flat.convertExpr b scope envVar envMap st).fst, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.seq (.lit v) b, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      -- Flat event is .silent
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      -- Core step
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      -- Trace preservation
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      -- Env preservation
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      -- Expression correspondence
      have hsf'_expr : sf'.expr = (Flat.convertExpr b scope envVar envMap st).fst := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?, Flat.exprValue?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = b := by
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?, Core.exprValue?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      exact ⟨hsf'_trace, henv', by
        have h0 := hstep; rw [hsf_rw] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := hcstep; rw [hsc_rw] at h1; simp only [Core.step?, Core.exprValue?] at h1
        have := (Prod.mk.inj (Option.some.inj h0)).2; have := (Prod.mk.inj (Option.some.inj h1)).2
        subst_vars; exact hheap, by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; rw [hsc'_expr]; exact h.2, sorry /- ExprAddrWF -/, scope, st,
        (Flat.convertExpr b scope envVar envMap st).2,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
    | none =>
      -- Stepping sub-case: a is not a value, need recursive step simulation
      -- a' is the converted sub-expression, b' is the converted continuation
      set a' := (Flat.convertExpr a scope envVar envMap st).1 with ha'_def
      set st1 := (Flat.convertExpr a scope envVar envMap st).2 with hst1_def
      set b' := (Flat.convertExpr b scope envVar envMap st1).1 with hb'_def
      have ha'_nv : Flat.exprValue? a' = none := convertExpr_not_value a hval scope envVar envMap st
      have hsf_rw : sf = ⟨.seq a' b', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      -- Depth of a < n
      have hdepth : Core.Expr.depth a < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      -- Extract Flat sub-step: step? on .seq a' b' with non-value a' delegates to step? a'
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, ha'_nv] at hstep
      -- Case split on step? of a'
      cases hsubstep : Flat.step? ⟨a', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        -- Flat.Step for sub-expression
        have hflat_step_sub : Flat.Step ⟨a', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        -- Apply IH (envVar/envMap carried through induction)
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth a) hdepth envVar envMap
          ⟨a', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨a, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [ha'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        -- Construct Core step on .seq a b using step_seq_nonvalue_lhs
        have hcore_seq : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .seq sc_arg.expr b, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.seq a b, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_seq_nonvalue_lhs a b sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨a, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := a } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .seq sc_arg.expr b, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_seq⟩, ?_⟩
        constructor
        · -- Trace
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]
          show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]
          rw [htrace]
        constructor
        · -- EnvCorr
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]
          convert henvCorr_arg using 1
          rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · -- Expression correspondence
          -- sf'.expr = .seq sa_flat.expr b' (from Flat step?)
          -- sc'.expr = .seq sc_arg.expr b (from Core pushTrace)
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .seq sa_flat.expr b' := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .seq sc_arg.expr b := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          -- Need: (.seq sa_flat.expr b', st???) = convertExpr (.seq sc_arg.expr b) scope??? envVar envMap st???
          -- convertExpr (.seq e b) = let (e', s1) := convertExpr e ...; let (b'', s2) := convertExpr b ... s1; (.seq e' b'', s2)
          -- From IH: (sa_flat.expr, st_a') = convertExpr sc_arg.expr scope' envVar envMap st_a
          -- Strategy: use scope' and st_a as witnesses, need b' = (convertExpr b scope' envVar envMap st_a').1
          -- This requires (convertExpr b scope envVar envMap st1).1 = (convertExpr b scope' envVar envMap st_a').1
          -- By scope irrelevance, scope doesn't matter. The state issue: st1 vs st_a' may differ.
          -- For non-functionDef expressions this is trivially true (state passes through unchanged).
          refine ⟨scope', st_a, ?_, ?_⟩
          · -- st' witness: the state after converting both sub-exprs
            exact (Flat.convertExpr b scope' envVar envMap st_a').2
          · simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
            -- Now goal is: (.seq sa_flat.expr b', _) = (.seq sa_flat.expr (convertExpr b scope' envVar envMap st_a').1, _)
            -- Need: b' = (convertExpr b scope' envVar envMap st_a').1
            -- b' = (convertExpr b scope envVar envMap st1).1 by definition
            -- By scope irrelevance: (convertExpr b scope envVar envMap st1) = (convertExpr b scope' envVar envMap st1)
            -- Need: st1 = st_a' (state after converting a = state after converting stepped a)
            -- This holds when the step doesn't change the number of functionDefs in a.
            congr 1
            · congr 1
              rw [hb'_def]
              rw [convertExpr_scope_irrelevant b scope scope' envVar envMap st1]
              rfl
            · rw [hb'_def]
              rw [convertExpr_scope_irrelevant b scope scope' envVar envMap st1]
              rfl
  | call _ _ => sorry -- needs env/heap/funcs correspondence
  | newObj _ _ => sorry -- needs env/heap correspondence
  | getProp obj prop =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .getProp (Flat.convertExpr obj scope envVar envMap st).1 prop := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? obj with
    | some v =>
      have ha_lit : obj = .lit v := by cases obj <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨.getProp (.lit (Flat.convertValue v)) prop, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨.getProp (.lit v) prop, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        cases v <;> simp at hstep <;> exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      -- Expression correspondence: need to relate Flat getProp result to Core getProp result
      have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
      simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
      have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
      simp only [Core.step?, Core.exprValue?] at hsc'_sub
      have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
      have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
      subst heqf; subst heqc
      refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr, ?_⟩
      -- heap correspondence
      constructor
      · exact hheap
      -- Now need: convertExpr of Core result = Flat result
      -- Case split on v to match both step functions
      refine ⟨sorry /- ExprAddrWF -/, scope, st, st, ?_⟩
      cases v with
      | object addr =>
        -- Both look up property in heap via HeapCorr
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]
        rw [heapObjectAt?_eq]
        -- ExprAddrWF gives addr < sc.heap.objects.size
        have hlt : addr < sc.heap.objects.size := by
          have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF, ValueAddrWF] at h; exact h
        rw [show sf.heap.objects[addr]? = sc.heap.objects[addr]? from (hheap.2 addr hlt).symm]
        cases h_lookup : sc.heap.objects[addr]? with
        | none => rfl
        | some props =>
          cases h_find : props.find? (fun kv => kv.fst == prop) with
          | none => rfl
          | some kv => simp only [coreToFlatValue_eq_convertValue]; rfl
      | string str =>
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | null =>
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | undefined =>
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | bool b =>
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | number n =>
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | function idx =>
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
    | none =>
      -- Non-value case: step the sub-expression (same pattern as typeof)
      set obj' := (Flat.convertExpr obj scope envVar envMap st).1 with hobj'_def
      set st1 := (Flat.convertExpr obj scope envVar envMap st).2 with hst1_def
      have hobj'_nv : Flat.exprValue? obj' = none := convertExpr_not_value obj hval scope envVar envMap st
      have hsf_rw : sf = ⟨.getProp obj' prop, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hdepth : Core.Expr.depth obj < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hobj'_nv] at hstep
      cases hsubstep : Flat.step? ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth obj) hdepth envVar envMap
          ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp only [noCallFrameReturn] at h; exact h) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hobj'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        have hcore_gp : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .getProp sc_arg.expr prop, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.getProp obj prop, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_getProp_step_obj obj prop sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := obj } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .getProp sc_arg.expr prop, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_gp⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · refine ⟨scope', st_a, st_a', ?_⟩
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .getProp sa_flat.expr prop := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .getProp sc_arg.expr prop := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          simp only [Flat.convertExpr]
          rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
            (sa_flat.expr, st_a') from hconv_arg.symm]
  | setProp obj prop value =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    set obj' := (Flat.convertExpr obj scope envVar envMap st).1 with hobj'_def
    set st1 := (Flat.convertExpr obj scope envVar envMap st).2 with hst1_def
    set value' := (Flat.convertExpr value scope envVar envMap st1).1 with hvalue'_def
    set st2 := (Flat.convertExpr value scope envVar envMap st1).2 with hst2_def
    have hsf_expr : sf.expr = .setProp obj' prop value' := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval_o : Core.exprValue? obj with
    | none =>
      -- Step the obj sub-expression
      have hobj'_nv : Flat.exprValue? obj' = none := convertExpr_not_value obj hval_o scope envVar envMap st
      have hsf_rw : sf = ⟨.setProp obj' prop value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hdepth : Core.Expr.depth obj < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hobj'_nv] at hstep
      cases hsubstep : Flat.step? ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat := ⟨hsubstep⟩
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth obj) hdepth envVar envMap
          ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hobj'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        have hcore_sp : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .setProp sc_arg.expr prop value, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.setProp obj prop value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_setProp_step_obj obj prop value sc.env sc.heap sc.trace sc.funcs sc.callStack hval_o ev_sub sc_arg
            (by rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := obj } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .setProp sc_arg.expr prop value, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_sp⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · refine ⟨scope', st_a, ?_, ?_⟩
          · exact (Flat.convertExpr value scope' envVar envMap st_a').2
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .setProp sa_flat.expr prop value' := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .setProp sc_arg.expr prop value := by simp [sc', Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]; simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
            congr 1
            · congr 1
              rw [hvalue'_def, hst1_def]
              rw [convertExpr_scope_irrelevant value scope scope' envVar envMap
                (Flat.convertExpr obj scope envVar envMap st).2]; rfl
            · rw [hvalue'_def, hst1_def]
              rw [convertExpr_scope_irrelevant value scope scope' envVar envMap
                (Flat.convertExpr obj scope envVar envMap st).2]; rfl
    | some ov =>
      -- obj is a value
      have ho_lit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o <;> exact congrArg _ hval_o
      subst ho_lit
      simp only [Flat.convertExpr] at hobj'_def hst1_def hconv hsf_expr
      -- obj' = .lit (convertValue ov), st1 = st
      cases hval_v : Core.exprValue? value with
      | some vv =>
        -- Both sub-expressions are values
        have hv_lit : value = .lit vv := by cases value <;> simp [Core.exprValue?] at hval_v <;> exact congrArg _ hval_v
        subst hv_lit
        simp only [Flat.convertExpr] at hvalue'_def hst2_def hconv hsf_expr
        have hsf_rw : sf = ⟨.setProp (.lit (Flat.convertValue ov)) prop (.lit (Flat.convertValue vv)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all
        have hsc_rw : sc = ⟨.setProp (.lit ov) prop (.lit vv), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
          cases sc; simp only [] at hsc ⊢; congr
        have hflat_ev : ev = .silent := by
          rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
          cases ov <;> simp at hstep <;> exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
        subst hflat_ev
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
          rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
        simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
        have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
        simp only [Core.step?, Core.exprValue?] at hsc'_sub
        have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
        have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
        subst heqf; subst heqc
        refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr, ?_⟩
        constructor
        · -- Heap correspondence: setProp modifies heap identically
          -- For .object addr: both update heap with flatToCoreValue (convertValue vv) = vv
          -- For non-object: both leave heap unchanged
          cases ov with
          | object addr =>
            -- HeapCorr preserved through setProp mutation
            rw [heapObjectAt?_eq]
            rcases Nat.lt_or_ge addr sc.heap.objects.size with hlt | hge
            · rw [show sf.heap.objects[addr]? = sc.heap.objects[addr]? from (hheap.2 addr hlt).symm]
              cases sc.heap.objects[addr]? with
              | none => exact hheap
              | some props =>
                rw [flatToCoreValue_convertValue]
                constructor
                · simp [Array.size_set!]; exact hheap.1
                · intro i hi
                  simp only [Array.size_set!] at hi
                  simp only [Array.set!, Array.setIfInBounds]
                  split <;> split <;> simp_all [Array.getElem?_def]
                  · omega
                  · omega
                  · exact hheap.2 i hi
            · have : sc.heap.objects[addr]? = none := by simp [Array.getElem?_def]; omega
              rw [this]
              cases hsf : sf.heap.objects[addr]? with
              | none => exact hheap
              | some props =>
                -- Flat mutates at addr outside Core range, HeapCorr preserved
                constructor
                · simp [Array.size_set!]; exact hheap.1
                · intro i hi
                  have hne : i ≠ addr := by omega
                  simp only [Array.set!, Array.setIfInBounds]
                  split
                  · simp [Array.getElem?_def]
                    split <;> simp_all
                    · exact hheap.2 i hi
                    · omega
                  · exact hheap.2 i hi
          | _ => exact hheap
        refine ⟨scope, st, st, ?_⟩
        cases ov with
        | object => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | string => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | null => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | undefined => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | bool => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | number => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | function => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | none =>
        -- obj is a value, value is not: step the value sub-expression
        have hvalue'_nv : Flat.exprValue? value' = none := convertExpr_not_value value hval_v scope envVar envMap st1
        have hsf_rw : sf = ⟨.setProp (.lit (Flat.convertValue ov)) prop value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all
        have hdepth : Core.Expr.depth value < n := by
          rw [← hd, hsc]; simp [Core.Expr.depth]; omega
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        -- Need to handle the obj-value case in Flat.step? for setProp
        -- Flat matches on convertValue ov, then on exprValue? value'
        -- Since value' is not a value: step value'
        -- Case split on convertValue ov to determine the Flat branch
        cases ov <;> simp only [Flat.convertValue, hvalue'_nv] at hstep <;> (
          cases hsubstep : Flat.step? ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
          | none => simp [hsubstep] at hstep
          | some p =>
            obtain ⟨ev_sub, sa_flat⟩ := p
            simp only [hsubstep] at hstep
            have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
            subst hev_eq
            have hflat_step_sub : Flat.Step ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat := ⟨hsubstep⟩
            obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
              ih_depth (Core.Expr.depth value) hdepth envVar envMap
              ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
              ⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.2) (sorry /- ExprAddrWF -/)
              ⟨scope, st1, st2, by simp only [hvalue'_def, hst2_def]; exact (Prod.eta _).symm⟩
              hflat_step_sub
            have hsc_rw : sc = ⟨.setProp (.lit ov) prop value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
              cases sc; simp only [] at hsc ⊢; congr
            obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (ev_sub, sc') := by
              rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]
              rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := value } from by cases sc; simp_all]
              rw [hcore_substep]; simp; exact ⟨_, rfl⟩
            refine ⟨sc', ⟨hcstep⟩, ?_⟩
            constructor
            · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
            constructor
            · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_env : sc'.env = sc_arg.env := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := value } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.env (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
            constructor
            · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_heap : sc'.heap = sc_arg.heap := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := value } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.heap (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_heap]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
            · refine ⟨scope', st_a, st_a', ?_⟩
              have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsf'_expr : sf'.expr = .setProp (.lit (Flat.convertValue ov)) prop sa_flat.expr := by rw [← hsf'_eq]; rfl
              have hsc'_expr : sc'.expr = .setProp (.lit ov) prop sc_arg.expr := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := value } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_expr, hsf'_expr]
              simp only [Flat.convertExpr]
              rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
                (sa_flat.expr, st_a') from hconv_arg.symm])
  | getIndex obj idx =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    set obj' := (Flat.convertExpr obj scope envVar envMap st).1 with hobj'_def
    set st1 := (Flat.convertExpr obj scope envVar envMap st).2 with hst1_def
    set idx' := (Flat.convertExpr idx scope envVar envMap st1).1 with hidx'_def
    set st2 := (Flat.convertExpr idx scope envVar envMap st1).2 with hst2_def
    have hsf_expr : sf.expr = .getIndex obj' idx' := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval_o : Core.exprValue? obj with
    | none =>
      -- Step the obj sub-expression
      have hobj'_nv : Flat.exprValue? obj' = none := convertExpr_not_value obj hval_o scope envVar envMap st
      have hsf_rw : sf = ⟨.getIndex obj' idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hdepth : Core.Expr.depth obj < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hobj'_nv] at hstep
      cases hsubstep : Flat.step? ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat := ⟨hsubstep⟩
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth obj) hdepth envVar envMap
          ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hobj'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        have hcore_gi : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .getIndex sc_arg.expr idx, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.getIndex obj idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_getIndex_step_obj obj idx sc.env sc.heap sc.trace sc.funcs sc.callStack hval_o ev_sub sc_arg
            (by rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := obj } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .getIndex sc_arg.expr idx, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_gi⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · refine ⟨scope', st_a, ?_, ?_⟩
          · exact (Flat.convertExpr idx scope' envVar envMap st_a').2
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .getIndex sa_flat.expr idx' := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .getIndex sc_arg.expr idx := by simp [sc', Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]; simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
            congr 1
            · congr 1
              rw [hidx'_def, hst1_def]
              rw [convertExpr_scope_irrelevant idx scope scope' envVar envMap
                (Flat.convertExpr obj scope envVar envMap st).2]; rfl
            · rw [hidx'_def, hst1_def]
              rw [convertExpr_scope_irrelevant idx scope scope' envVar envMap
                (Flat.convertExpr obj scope envVar envMap st).2]; rfl
    | some ov =>
      -- obj is a value
      have ho_lit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o <;> exact congrArg _ hval_o
      subst ho_lit
      simp only [Flat.convertExpr] at hobj'_def hst1_def hconv hsf_expr
      -- obj' = .lit (convertValue ov), st1 = st
      cases hval_i : Core.exprValue? idx with
      | some iv =>
        -- Both sub-expressions are values
        have hi_lit : idx = .lit iv := by cases idx <;> simp [Core.exprValue?] at hval_i <;> exact congrArg _ hval_i
        subst hi_lit
        simp only [Flat.convertExpr] at hidx'_def hst2_def hconv hsf_expr
        have hsf_rw : sf = ⟨.getIndex (.lit (Flat.convertValue ov)) (.lit (Flat.convertValue iv)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all
        have hsc_rw : sc = ⟨.getIndex (.lit ov) (.lit iv), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
          cases sc; simp only [] at hsc ⊢; congr
        have hflat_ev : ev = .silent := by
          rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
          cases ov <;> simp at hstep <;> exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
        subst hflat_ev
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
          rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
        simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
        have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
        simp only [Core.step?, Core.exprValue?] at hsc'_sub
        have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
        have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
        subst heqf; subst heqc
        refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr, ?_⟩
        constructor
        · exact hheap
        refine ⟨sorry /- ExprAddrWF -/, scope, st, st, ?_⟩
        -- Case split on ov to match both step functions
        cases ov with
        | object addr =>
          simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]
          rw [heapObjectAt?_eq, valueToString_convertValue]
          -- ExprAddrWF gives addr < sc.heap.objects.size
          have hlt : addr < sc.heap.objects.size := by
            have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF, ValueAddrWF] at h; exact h.1
          rw [show sf.heap.objects[addr]? = sc.heap.objects[addr]? from (hheap.2 addr hlt).symm]
          cases h_lookup : sc.heap.objects[addr]? with
          | none => rfl
          | some props =>
            cases h_find : props.find? (fun kv => kv.fst == Core.valueToString iv) with
            | none => rfl
            | some kv => simp only [coreToFlatValue_eq_convertValue]; rfl
        | string str =>
          simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace, valueToString_convertValue]
          cases iv <;> simp only [Flat.convertValue, Core.valueToString, Flat.valueToString] <;> rfl
        | null =>
          simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | undefined =>
          simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | bool b =>
          simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | number n =>
          simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | function idx =>
          simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | none =>
        -- obj is a value, idx is not: step the idx sub-expression
        have hidx'_nv : Flat.exprValue? idx' = none := convertExpr_not_value idx hval_i scope envVar envMap st1
        have hsf_rw : sf = ⟨.getIndex (.lit (Flat.convertValue ov)) idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all
        have hdepth : Core.Expr.depth idx < n := by
          rw [← hd, hsc]; simp [Core.Expr.depth]; omega
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        -- Case split on convertValue ov to find the Flat branch for stepping idx
        cases ov <;> simp only [Flat.convertValue, hidx'_nv] at hstep <;> (
          cases hsubstep : Flat.step? ⟨idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
          | none => simp [hsubstep] at hstep
          | some p =>
            obtain ⟨ev_sub, sa_flat⟩ := p
            simp only [hsubstep] at hstep
            have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
            subst hev_eq
            have hflat_step_sub : Flat.Step ⟨idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat := ⟨hsubstep⟩
            obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
              ih_depth (Core.Expr.depth idx) hdepth envVar envMap
              ⟨idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
              ⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.2) (sorry /- ExprAddrWF -/)
              ⟨scope, st1, st2, by simp only [hidx'_def, hst2_def]; exact (Prod.eta _).symm⟩
              hflat_step_sub
            have hsc_rw : sc = ⟨.getIndex (.lit ov) idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
              cases sc; simp only [] at hsc ⊢; congr
            obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (ev_sub, sc') := by
              rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]
              rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := idx } from by cases sc; simp_all]
              rw [hcore_substep]; simp; exact ⟨_, rfl⟩
            refine ⟨sc', ⟨hcstep⟩, ?_⟩
            constructor
            · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
            constructor
            · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_env : sc'.env = sc_arg.env := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := idx } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.env (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
            constructor
            · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_heap : sc'.heap = sc_arg.heap := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := idx } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.heap (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_heap]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
            · refine ⟨scope', st_a, st_a', ?_⟩
              have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsf'_expr : sf'.expr = .getIndex (.lit (Flat.convertValue ov)) sa_flat.expr := by rw [← hsf'_eq]; rfl
              have hsc'_expr : sc'.expr = .getIndex (.lit ov) sc_arg.expr := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := idx } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_expr, hsf'_expr]
              simp only [Flat.convertExpr]
              rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
                (sa_flat.expr, st_a') from hconv_arg.symm])
  | setIndex obj idx value =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    set obj' := (Flat.convertExpr obj scope envVar envMap st).1 with hobj'_def
    set st1 := (Flat.convertExpr obj scope envVar envMap st).2 with hst1_def
    set idx' := (Flat.convertExpr idx scope envVar envMap st1).1 with hidx'_def
    set st2 := (Flat.convertExpr idx scope envVar envMap st1).2 with hst2_def
    set value' := (Flat.convertExpr value scope envVar envMap st2).1 with hvalue'_def
    set st3 := (Flat.convertExpr value scope envVar envMap st2).2 with hst3_def
    have hsf_expr : sf.expr = .setIndex obj' idx' value' := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval_o : Core.exprValue? obj with
    | none =>
      -- Step the obj sub-expression
      have hobj'_nv : Flat.exprValue? obj' = none := convertExpr_not_value obj hval_o scope envVar envMap st
      have hsf_rw : sf = ⟨.setIndex obj' idx' value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hdepth : Core.Expr.depth obj < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hobj'_nv] at hstep
      cases hsubstep : Flat.step? ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat := ⟨hsubstep⟩
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth obj) hdepth envVar envMap
          ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1.1) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hobj'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        have hsc_rw : sc = ⟨.setIndex obj idx value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
          cases sc; simp only [] at hsc ⊢; congr
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (ev_sub, sc') := by
          rw [hsc_rw]; simp only [Core.step?, Core.exprValue?, hval_o]
          rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
            { sc with expr := obj } from by cases sc; simp_all]
          rw [hcore_substep]; simp; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by
            have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?, hval_o] at h0
            rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := obj } from by cases sc; simp_all] at h0
            rw [hcore_substep] at h0; simp at h0
            exact congrArg Core.State.env (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
          rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_heap : sc'.heap = sc_arg.heap := by
            have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?, hval_o] at h0
            rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := obj } from by cases sc; simp_all] at h0
            rw [hcore_substep] at h0; simp at h0
            exact congrArg Core.State.heap (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
          rw [hsc'_heap]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · refine ⟨scope', st_a, ?_, ?_⟩
          · exact (Flat.convertExpr idx scope' envVar envMap st_a').2 |>
              (fun st_idx => (Flat.convertExpr value scope' envVar envMap
                (Flat.convertExpr idx scope' envVar envMap st_a').2).2)
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .setIndex sa_flat.expr idx' value' := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .setIndex sc_arg.expr idx value := by
              have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?, hval_o] at h0
              rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := obj } from by cases sc; simp_all] at h0
              rw [hcore_substep] at h0; simp at h0
              exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]; simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
            congr 1
            · congr 1
              · congr 1
                rw [hidx'_def, hst1_def]
                rw [convertExpr_scope_irrelevant idx scope scope' envVar envMap
                  (Flat.convertExpr obj scope envVar envMap st).2]; rfl
              · rw [hidx'_def, hst1_def]
                rw [convertExpr_scope_irrelevant idx scope scope' envVar envMap
                  (Flat.convertExpr obj scope envVar envMap st).2]; rfl
            · congr 1
              rw [hvalue'_def, hst2_def, hidx'_def, hst1_def]
              rw [convertExpr_scope_irrelevant idx scope scope' envVar envMap
                (Flat.convertExpr obj scope envVar envMap st).2]
              rw [convertExpr_scope_irrelevant value scope scope' envVar envMap
                (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr obj scope envVar envMap st).2).2]; rfl
    | some ov =>
      -- obj is a value
      have ho_lit : obj = .lit ov := by cases obj <;> simp [Core.exprValue?] at hval_o <;> exact congrArg _ hval_o
      subst ho_lit
      simp only [Flat.convertExpr] at hobj'_def hst1_def hconv hsf_expr
      cases hval_i : Core.exprValue? idx with
      | none =>
        -- obj value, idx not value: step idx
        have hidx'_nv : Flat.exprValue? idx' = none := convertExpr_not_value idx hval_i scope envVar envMap st1
        have hsf_rw : sf = ⟨.setIndex (.lit (Flat.convertValue ov)) idx' value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all
        have hdepth : Core.Expr.depth idx < n := by
          rw [← hd, hsc]; simp [Core.Expr.depth]; omega
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        cases ov <;> simp only [Flat.convertValue, hidx'_nv] at hstep <;> (
          cases hsubstep : Flat.step? ⟨idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
          | none => simp [hsubstep] at hstep
          | some p =>
            obtain ⟨ev_sub, sa_flat⟩ := p
            simp only [hsubstep] at hstep
            have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
            subst hev_eq
            have hflat_step_sub : Flat.Step ⟨idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat := ⟨hsubstep⟩
            obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
              ih_depth (Core.Expr.depth idx) hdepth envVar envMap
              ⟨idx', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
              ⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1.2) (sorry /- ExprAddrWF -/)
              ⟨scope, st1, st2, by simp only [hidx'_def, hst2_def]; exact (Prod.eta _).symm⟩
              hflat_step_sub
            have hsc_rw : sc = ⟨.setIndex (.lit ov) idx value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
              cases sc; simp only [] at hsc ⊢; congr
            obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (ev_sub, sc') := by
              rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]
              rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := idx } from by cases sc; simp_all]
              rw [hcore_substep]; simp; exact ⟨_, rfl⟩
            refine ⟨sc', ⟨hcstep⟩, ?_⟩
            constructor
            · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
            constructor
            · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_env : sc'.env = sc_arg.env := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := idx } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.env (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
            constructor
            · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_heap : sc'.heap = sc_arg.heap := by
                have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := idx } from by cases sc; simp_all] at h0
                rw [hcore_substep] at h0; simp at h0
                exact congrArg Core.State.heap (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
              rw [hsc'_heap]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
            · refine ⟨scope', st_a, ?_, ?_⟩
              · exact (Flat.convertExpr value scope' envVar envMap st_a').2
              · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
                have hsf'_expr : sf'.expr = .setIndex (.lit (Flat.convertValue ov)) sa_flat.expr value' := by rw [← hsf'_eq]; rfl
                have hsc'_expr : sc'.expr = .setIndex (.lit ov) sc_arg.expr value := by
                  have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                  rw [show (⟨idx, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                    { sc with expr := idx } from by cases sc; simp_all] at h0
                  rw [hcore_substep] at h0; simp at h0
                  exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
                rw [hsc'_expr, hsf'_expr]; simp only [Flat.convertExpr]
                rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
                  (sa_flat.expr, st_a') from hconv_arg.symm]
                congr 1
                · congr 1
                  rw [hvalue'_def, hst2_def, hidx'_def, hst1_def]
                  rw [convertExpr_scope_irrelevant idx scope scope' envVar envMap
                    (Flat.convertExpr (.lit ov) scope envVar envMap st).2]
                  rw [convertExpr_scope_irrelevant value scope scope' envVar envMap
                    (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr (.lit ov) scope envVar envMap st).2).2]; rfl
                · rw [hvalue'_def, hst2_def, hidx'_def, hst1_def]
                  rw [convertExpr_scope_irrelevant idx scope scope' envVar envMap
                    (Flat.convertExpr (.lit ov) scope envVar envMap st).2]
                  rw [convertExpr_scope_irrelevant value scope scope' envVar envMap
                    (Flat.convertExpr idx scope envVar envMap (Flat.convertExpr (.lit ov) scope envVar envMap st).2).2]; rfl)
      | some iv =>
        -- obj value, idx value
        have hi_lit : idx = .lit iv := by cases idx <;> simp [Core.exprValue?] at hval_i <;> exact congrArg _ hval_i
        subst hi_lit
        simp only [Flat.convertExpr] at hidx'_def hst2_def hconv hsf_expr
        cases hval_v : Core.exprValue? value with
        | some vv =>
          -- All three are values
          have hv_lit : value = .lit vv := by cases value <;> simp [Core.exprValue?] at hval_v <;> exact congrArg _ hval_v
          subst hv_lit
          simp only [Flat.convertExpr] at hvalue'_def hst3_def hconv hsf_expr
          have hsf_rw : sf = ⟨.setIndex (.lit (Flat.convertValue ov)) (.lit (Flat.convertValue iv)) (.lit (Flat.convertValue vv)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
            cases sf; simp_all
          have hsc_rw : sc = ⟨.setIndex (.lit ov) (.lit iv) (.lit vv), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
            cases sc; simp only [] at hsc ⊢; congr
          have hflat_ev : ev = .silent := by
            rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
            cases ov <;> simp at hstep <;> exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
          subst hflat_ev
          obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
            rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
          refine ⟨sc', ⟨hcstep⟩, ?_⟩
          have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
          simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
          have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
          simp only [Core.step?, Core.exprValue?] at hsc'_sub
          have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
          have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
          subst heqf; subst heqc
          refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr, ?_⟩
          constructor
          · -- Heap correspondence for setIndex
            cases ov with
            | object addr =>
              -- HeapCorr preserved through setIndex mutation
              rw [heapObjectAt?_eq, flatToCoreValue_convertValue, valueToString_convertValue]
              rcases Nat.lt_or_ge addr sc.heap.objects.size with hlt | hge
              · rw [show sf.heap.objects[addr]? = sc.heap.objects[addr]? from (hheap.2 addr hlt).symm]
                cases sc.heap.objects[addr]? with
                | none => exact hheap
                | some props =>
                  constructor
                  · simp [Array.size_set!]; exact hheap.1
                  · intro i hi
                    simp only [Array.size_set!] at hi
                    simp only [Array.set!, Array.setIfInBounds]
                    split <;> split <;> simp_all [Array.getElem?_def]
                    · omega
                    · omega
                    · exact hheap.2 i hi
              · have : sc.heap.objects[addr]? = none := by simp [Array.getElem?_def]; omega
                rw [this]
                cases hsf : sf.heap.objects[addr]? with
                | none => exact hheap
                | some props =>
                  constructor
                  · simp [Array.size_set!]; exact hheap.1
                  · intro i hi
                    have hne : i ≠ addr := by omega
                    simp only [Array.set!, Array.setIfInBounds]
                    split
                    · simp [Array.getElem?_def]
                      split <;> simp_all
                      · exact hheap.2 i hi
                      · omega
                    · exact hheap.2 i hi
            | _ => exact hheap
          refine ⟨scope, st, st, ?_⟩
          cases ov with
          | object => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
          | string => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
          | null => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
          | undefined => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
          | bool => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
          | number => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
          | function => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
        | none =>
          -- obj value, idx value, value not value: step value
          have hvalue'_nv : Flat.exprValue? value' = none := convertExpr_not_value value hval_v scope envVar envMap st2
          have hsf_rw : sf = ⟨.setIndex (.lit (Flat.convertValue ov)) (.lit (Flat.convertValue iv)) value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
            cases sf; simp_all
          have hdepth : Core.Expr.depth value < n := by
            rw [← hd, hsc]; simp [Core.Expr.depth]; omega
          rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
          cases ov <;> simp only [Flat.convertValue, hvalue'_nv] at hstep <;> (
            cases hsubstep : Flat.step? ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
            | none => simp [hsubstep] at hstep
            | some p =>
              obtain ⟨ev_sub, sa_flat⟩ := p
              simp only [hsubstep] at hstep
              have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
              subst hev_eq
              have hflat_step_sub : Flat.Step ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat := ⟨hsubstep⟩
              obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
                ih_depth (Core.Expr.depth value) hdepth envVar envMap
                ⟨value', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
                ⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
                ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.2) (sorry /- ExprAddrWF -/)
                ⟨scope, st2, st3, by simp only [hvalue'_def, hst3_def]; exact (Prod.eta _).symm⟩
                hflat_step_sub
              have hsc_rw : sc = ⟨.setIndex (.lit ov) (.lit iv) value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
                cases sc; simp only [] at hsc ⊢; congr
              obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (ev_sub, sc') := by
                rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]
                rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                  { sc with expr := value } from by cases sc; simp_all]
                rw [hcore_substep]; simp; exact ⟨_, rfl⟩
              refine ⟨sc', ⟨hcstep⟩, ?_⟩
              constructor
              · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
                rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
              constructor
              · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
                have hsc'_env : sc'.env = sc_arg.env := by
                  have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                  rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                    { sc with expr := value } from by cases sc; simp_all] at h0
                  rw [hcore_substep] at h0; simp at h0
                  exact congrArg Core.State.env (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
                rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
              constructor
              · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
                have hsc'_heap : sc'.heap = sc_arg.heap := by
                  have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                  rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                    { sc with expr := value } from by cases sc; simp_all] at h0
                  rw [hcore_substep] at h0; simp at h0
                  exact congrArg Core.State.heap (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
                rw [hsc'_heap]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
              · refine ⟨scope', st_a, st_a', ?_⟩
                have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
                have hsf'_expr : sf'.expr = .setIndex (.lit (Flat.convertValue ov)) (.lit (Flat.convertValue iv)) sa_flat.expr := by rw [← hsf'_eq]; rfl
                have hsc'_expr : sc'.expr = .setIndex (.lit ov) (.lit iv) sc_arg.expr := by
                  have h0 := hcstep; rw [hsc_rw] at h0; simp only [Core.step?, Core.exprValue?] at h0
                  rw [show (⟨value, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                    { sc with expr := value } from by cases sc; simp_all] at h0
                  rw [hcore_substep] at h0; simp at h0
                  exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ by simp [Core.pushTrace]
                rw [hsc'_expr, hsf'_expr]
                simp only [Flat.convertExpr]
                rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
                  (sa_flat.expr, st_a') from hconv_arg.symm])
  | deleteProp obj prop =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .deleteProp (Flat.convertExpr obj scope envVar envMap st).1 prop := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? obj with
    | some v =>
      have ha_lit : obj = .lit v := by cases obj <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨.deleteProp (.lit (Flat.convertValue v)) prop, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨.deleteProp (.lit v) prop, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        cases v <;> simp at hstep <;> exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
      simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
      have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
      simp only [Core.step?, Core.exprValue?] at hsc'_sub
      have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
      have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
      subst heqf; subst heqc
      refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr, ?_⟩
      -- Heap correspondence: deleteProp modifies heap identically on both sides
      constructor
      · -- HeapCorr preserved through deleteProp mutation
        cases v with
        | object addr =>
          simp only [Flat.convertValue]
          rw [heapObjectAt?_eq]
          rcases Nat.lt_or_ge addr sc.heap.objects.size with hlt | hge
          · rw [show sf.heap.objects[addr]? = sc.heap.objects[addr]? from (hheap.2 addr hlt).symm]
            cases sc.heap.objects[addr]? with
            | none => exact hheap
            | some props =>
              constructor
              · simp [Array.size_set!]; exact hheap.1
              · intro i hi
                simp only [Array.size_set!] at hi
                simp only [Array.set!, Array.setIfInBounds]
                split <;> split <;> simp_all [Array.getElem?_def]
                · omega
                · omega
                · exact hheap.2 i hi
          · have : sc.heap.objects[addr]? = none := by simp [Array.getElem?_def]; omega
            rw [this]
            cases hsf : sf.heap.objects[addr]? with
            | none => exact hheap
            | some props =>
              constructor
              · simp [Array.size_set!]; exact hheap.1
              · intro i hi
                have hne : i ≠ addr := by omega
                simp only [Array.set!, Array.setIfInBounds]
                split
                · simp [Array.getElem?_def]
                  split <;> simp_all
                  · exact hheap.2 i hi
                  · omega
                · exact hheap.2 i hi
        | _ => exact hheap
      refine ⟨scope, st, st, ?_⟩
      cases v with
      | object addr =>
        simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | string => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | null => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | undefined => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | bool => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | number => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | function => simp only [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
    | none =>
      set obj' := (Flat.convertExpr obj scope envVar envMap st).1 with hobj'_def
      set st1 := (Flat.convertExpr obj scope envVar envMap st).2 with hst1_def
      have hobj'_nv : Flat.exprValue? obj' = none := convertExpr_not_value obj hval scope envVar envMap st
      have hsf_rw : sf = ⟨.deleteProp obj' prop, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hdepth : Core.Expr.depth obj < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hobj'_nv] at hstep
      cases hsubstep : Flat.step? ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth obj) hdepth envVar envMap
          ⟨obj', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hobj'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        have hcore_dp : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .deleteProp sc_arg.expr prop, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.deleteProp obj prop, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_deleteProp_step_obj obj prop sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨obj, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := obj } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .deleteProp sc_arg.expr prop, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_dp⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · refine ⟨scope', st_a, st_a', ?_⟩
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .deleteProp sa_flat.expr prop := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .deleteProp sc_arg.expr prop := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          simp only [Flat.convertExpr]
          rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
            (sa_flat.expr, st_a') from hconv_arg.symm]
  | typeof arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .typeof (Flat.convertExpr arg scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? arg with
    | some v =>
      have ha_lit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.typeof (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.typeof (.lit v), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      -- Expression correspondence: subst sf' and sc', then cases v
      have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
      simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
      have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
      simp only [Core.step?, Core.exprValue?] at hsc'_sub
      -- After simp: hsf'_sub and hsc'_sub give concrete sf' and sc'
      have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
      have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
      subst heqf; subst heqc
      -- Now need: CC_SimRel with typeofValue (convertValue v) vs .string (core_typeof_result)
      -- cases v to let kernel reduce typeofValue (convertValue v)
      refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr,
        scope, st, st, ?_⟩
      cases v with
      | null => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | undefined => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | bool => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | number => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | string => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | function => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | object => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
    | none =>
      -- arg' is the converted sub-expression
      set arg' := (Flat.convertExpr arg scope envVar envMap st).1 with harg'_def
      set st1 := (Flat.convertExpr arg scope envVar envMap st).2 with hst1_def
      have harg'_nv : Flat.exprValue? arg' = none := convertExpr_not_value arg hval scope envVar envMap st
      have hsf_rw : sf = ⟨.typeof arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      -- Depth of arg < n
      have hdepth : Core.Expr.depth arg < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      -- Extract Flat sub-step: step? on .typeof arg' with non-value arg' delegates to step? arg'
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, harg'_nv] at hstep
      -- Case split on step? of arg'
      cases hsubstep : Flat.step? ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        -- Flat.Step for sub-expression
        have hflat_step_sub : Flat.Step ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        -- Apply IH (envVar/envMap carried through induction)
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth arg) hdepth envVar envMap
          ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [harg'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        -- Construct Core step on .typeof arg using step_typeof_step_arg
        have hcore_typeof : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .typeof sc_arg.expr, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.typeof arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_typeof_step_arg arg sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := arg } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .typeof sc_arg.expr, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_typeof⟩, ?_⟩
        constructor
        · -- Trace: sf'.trace = sc'.trace
          -- sf' = { .typeof sa_flat.expr, sa_flat.env, sa_flat.heap, sf.trace ++ [ev_sub] }
          -- sc' = pushTrace {sc_arg with expr := .typeof sc_arg.expr, trace := sc.trace} ev_sub
          --      = {sc_arg with expr := .typeof sc_arg.expr, trace := sc.trace ++ [ev_sub]}
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]
          show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]
          rw [htrace]
        constructor
        · -- EnvCorr: pushTrace doesn't change env
          -- sc'.env = sc_arg.env (pushTrace only changes trace)
          -- sf'.env = sa_flat.env (from Flat step? decomposition)
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]
          convert henvCorr_arg using 1
          -- Need: sf'.env = sa_flat.env
          rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · -- Expression correspondence
          refine ⟨scope', st_a, st_a', ?_⟩
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          -- sf'.expr = .typeof sa_flat.expr (from Flat step?)
          -- sc'.expr = .typeof sc_arg.expr (from Core pushTrace)
          have hsf'_expr : sf'.expr = .typeof sa_flat.expr := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .typeof sc_arg.expr := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          -- Need: (.typeof sa_flat.expr, st_a') = Flat.convertExpr (.typeof sc_arg.expr) scope' envVar envMap st_a
          -- convertExpr (.typeof e) = let (e', st1) := convertExpr e scope envVar envMap st; (.typeof e', st1)
          simp only [Flat.convertExpr]
          -- From hconv_arg: (sa_flat.expr, st_a') = convertExpr sc_arg.expr scope' envVar envMap st_a
          rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
            (sa_flat.expr, st_a') from hconv_arg.symm]
  | unary op arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .unary op (Flat.convertExpr arg scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? arg with
    | some v =>
      have ha_lit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.unary op (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.unary op (.lit v), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
      simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
      have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
      simp only [Core.step?, Core.exprValue?] at hsc'_sub
      have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
      have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
      subst heqf; subst heqc
      refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr,
        scope, st, st, ?_⟩
      -- Expression correspondence via evalUnary_convertValue
      show (Flat.Expr.lit (Flat.evalUnary op (Flat.convertValue v)), st) =
           Flat.convertExpr (.lit (Core.evalUnary op v)) scope envVar envMap st
      simp only [Flat.convertExpr]
      congr 1; exact congrArg _ (evalUnary_convertValue op v)
    | none =>
      -- Stepping sub-case for unary: same pattern as typeof
      set arg' := (Flat.convertExpr arg scope envVar envMap st).1 with harg'_def
      set st1 := (Flat.convertExpr arg scope envVar envMap st).2 with hst1_def
      have harg'_nv : Flat.exprValue? arg' = none := convertExpr_not_value arg hval scope envVar envMap st
      have hsf_rw : sf = ⟨.unary op arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by cases sf; simp_all
      have hdepth : Core.Expr.depth arg < n := by rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      -- Decompose Flat step?
      rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?, harg'_nv] at hstep
      cases hsubstep : Flat.step? ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        -- Apply IH (envVar/envMap carried through induction)
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth arg) hdepth envVar envMap
          ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [harg'_def, hst1_def]; exact (Prod.eta _).symm⟩
          ⟨hsubstep⟩
        -- Construct Core step on .unary op arg
        have hcore_unary : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .unary op sc_arg.expr, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.unary op arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_unary_step_arg op arg sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := arg } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .unary op sc_arg.expr, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_unary⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · refine ⟨scope', st_a, st_a', ?_⟩
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .unary op sa_flat.expr := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .unary op sc_arg.expr := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          simp only [Flat.convertExpr]
          rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
            (sa_flat.expr, st_a') from hconv_arg.symm]
  | binary op lhs rhs =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    cases hval_l : Core.exprValue? lhs with
    | some lv =>
      cases hval_r : Core.exprValue? rhs with
      | some rv =>
        -- VALUE SUB-CASE: both operands are values
        have hlhs_lit : lhs = .lit lv := by
          cases lhs <;> simp [Core.exprValue?] at hval_l <;> exact congrArg _ hval_l
        have hrhs_lit : rhs = .lit rv := by
          cases rhs <;> simp [Core.exprValue?] at hval_r <;> exact congrArg _ hval_r
        subst hlhs_lit; subst hrhs_lit
        simp only [Flat.convertExpr] at hconv
        have hsf_rw : sf = ⟨Flat.Expr.binary op (.lit (Flat.convertValue lv)) (.lit (Flat.convertValue rv)),
            sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all [(Prod.mk.inj hconv).1]
        have hsc_rw : sc = ⟨Core.Expr.binary op (.lit lv) (.lit rv),
            sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
          cases sc; simp only [] at hsc ⊢; congr
        -- Both produce .silent
        have hflat_ev : ev = .silent := by
          rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
          exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
        subst hflat_ev
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
          rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        -- Trace correspondence
        have hsf'_sub := hstep; rw [hsf_rw] at hsf'_sub
        simp only [Flat.step?, Flat.exprValue?] at hsf'_sub
        have hsc'_sub := hcstep; rw [hsc_rw] at hsc'_sub
        simp only [Core.step?, Core.exprValue?] at hsc'_sub
        have heqf := (Prod.mk.inj (Option.some.inj hsf'_sub)).2
        have heqc := (Prod.mk.inj (Option.some.inj hsc'_sub)).2
        subst heqf; subst heqc
        -- Now sf' has expr .lit (Flat.evalBinary ...) and sc' has expr .lit (Core.evalBinary ...)
        refine ⟨by show sf.trace ++ _ = sc.trace ++ _; rw [htrace], henvCorr,
          scope, st, st, ?_⟩
        -- Expression correspondence via evalBinary_convertValue
        show (Flat.Expr.lit (Flat.evalBinary op (Flat.convertValue lv) (Flat.convertValue rv)), st) =
             Flat.convertExpr (.lit (Core.evalBinary op lv rv)) scope envVar envMap st
        simp only [Flat.convertExpr]
        congr 1; exact congrArg _ (evalBinary_convertValue op lv rv)
      | none =>
        -- rhs needs evaluation, lhs is value (.lit lv)
        have hlhs_lit : lhs = .lit lv := by
          cases lhs <;> simp [Core.exprValue?] at hval_l <;> exact congrArg _ hval_l
        subst hlhs_lit
        simp only [Flat.convertExpr] at hconv
        set rhs' := (Flat.convertExpr rhs scope envVar envMap st).1 with hrhs'_def
        set st1 := (Flat.convertExpr rhs scope envVar envMap st).2 with hst1_def
        have hrhs'_nv : Flat.exprValue? rhs' = none := convertExpr_not_value rhs hval_r scope envVar envMap st
        have hsf_rw : sf = ⟨.binary op (.lit (Flat.convertValue lv)) rhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all [(Prod.mk.inj hconv).1]
        have hdepth : Core.Expr.depth rhs < n := by
          rw [← hd, hsc]; simp [Core.Expr.depth]; omega
        rw [hsf_rw] at hstep
        simp only [Flat.step?, Flat.exprValue?, hrhs'_nv] at hstep
        cases hsubstep : Flat.step? ⟨rhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
        | none => simp [hsubstep] at hstep
        | some p =>
          obtain ⟨ev_sub, sa_flat⟩ := p
          simp only [hsubstep] at hstep
          have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
          subst hev_eq
          have hflat_step_sub : Flat.Step ⟨rhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
            ⟨hsubstep⟩
          obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
            ih_depth (Core.Expr.depth rhs) hdepth envVar envMap
            ⟨rhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
            ⟨rhs, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.2) (sorry /- ExprAddrWF -/)
            ⟨scope, st, st1, by simp only [hrhs'_def, hst1_def]; exact (Prod.eta _).symm⟩
            hflat_step_sub
          -- Need Core step helper for binary with value lhs, non-value rhs
          have hcore_binary : Core.step? sc =
            some (ev_sub, Core.pushTrace { sc_arg with expr := .binary op (.lit lv) sc_arg.expr, trace := sc.trace } ev_sub) := by
            rw [show sc = ⟨.binary op (.lit lv) rhs, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all]
            simp [Core.step?, Core.exprValue?, hval_r, hcore_substep]
          set sc' := Core.pushTrace { sc_arg with expr := .binary op (.lit lv) sc_arg.expr, trace := sc.trace } ev_sub
          refine ⟨sc', ⟨hcore_binary⟩, ?_⟩
          constructor
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
          constructor
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
            rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
          constructor
          · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .binary op (.lit (Flat.convertValue lv)) sa_flat.expr := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .binary op (.lit lv) sc_arg.expr := by simp [sc', Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]
            refine ⟨scope', st_a, st_a', ?_⟩
            simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
    | none =>
      -- lhs needs evaluation
      set lhs' := (Flat.convertExpr lhs scope envVar envMap st).1 with hlhs'_def
      set st1 := (Flat.convertExpr lhs scope envVar envMap st).2 with hst1_def
      set rhs' := (Flat.convertExpr rhs scope envVar envMap st1).1 with hrhs'_def
      have hlhs'_nv : Flat.exprValue? lhs' = none := convertExpr_not_value lhs hval_l scope envVar envMap st
      have hsf_rw : sf = ⟨.binary op lhs' rhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all [(Prod.mk.inj hconv).1]
      have hdepth : Core.Expr.depth lhs < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hlhs'_nv] at hstep
      cases hsubstep : Flat.step? ⟨lhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        have hflat_step_sub : Flat.Step ⟨lhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth lhs) hdepth envVar envMap
          ⟨lhs', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨lhs, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.1) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [hlhs'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        have hcore_binary : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .binary op sc_arg.expr rhs, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.binary op lhs rhs, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_binary_nonvalue_lhs op lhs rhs sc.env sc.heap sc.trace sc.funcs sc.callStack hval_l ev_sub sc_arg
            (by rw [show (⟨lhs, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := lhs } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .binary op sc_arg.expr rhs, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_binary⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .binary op sa_flat.expr rhs' := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .binary op sc_arg.expr rhs := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          refine ⟨scope', st_a, ?_, ?_⟩
          · exact (Flat.convertExpr rhs scope' envVar envMap
              (Flat.convertExpr sc_arg.expr scope' envVar envMap st_a).2).2
          · simp only [Flat.convertExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
            congr 1
            · congr 1
              rw [hrhs'_def, hst1_def]
              rw [convertExpr_scope_irrelevant rhs scope scope' envVar envMap
                (Flat.convertExpr lhs scope envVar envMap st).2]
              rfl
            · rw [hrhs'_def, hst1_def]
              rw [convertExpr_scope_irrelevant rhs scope scope' envVar envMap
                (Flat.convertExpr lhs scope envVar envMap st).2]
              rfl
  | objectLit _ => sorry -- needs env/heap correspondence
  | arrayLit _ => sorry -- needs env/heap correspondence
  | functionDef _ _ _ _ _ => sorry -- needs env/heap/funcs + CC state
  | throw arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .throw (Flat.convertExpr arg scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? arg with
    | some v =>
      have ha_lit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.throw (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.throw (.lit v), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      -- Both produce .error (valueToString v)
      have hflat_ev : ev = .error (Flat.valueToString (Flat.convertValue v)) := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      rw [valueToString_convertValue] at hflat_ev
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.error (Core.valueToString v), sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _
        rw [htrace, valueToString_convertValue]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      have hsf'_expr : sf'.expr = .lit .undefined := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?, Flat.exprValue?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = .lit .undefined := by
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?, Core.exprValue?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      exact ⟨hsf'_trace, henv', by
        have h0 := hstep; rw [hsf_rw] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := hcstep; rw [hsc_rw] at h1; simp only [Core.step?, Core.exprValue?] at h1
        have := (Prod.mk.inj (Option.some.inj h0)).2; have := (Prod.mk.inj (Option.some.inj h1)).2
        subst_vars; exact hheap, by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
        by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
    | none =>
      -- Stepping sub-case for throw: same pattern as typeof/unary
      set arg' := (Flat.convertExpr arg scope envVar envMap st).1 with harg'_def
      set st1 := (Flat.convertExpr arg scope envVar envMap st).2 with hst1_def
      have harg'_nv : Flat.exprValue? arg' = none := convertExpr_not_value arg hval scope envVar envMap st
      have hsf_rw : sf = ⟨.throw arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by cases sf; simp_all
      have hdepth : Core.Expr.depth arg < n := by rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?, harg'_nv] at hstep
      cases hsubstep : Flat.step? ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        -- Apply IH (envVar/envMap carried through induction)
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth arg) hdepth envVar envMap
          ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [harg'_def, hst1_def]; exact (Prod.eta _).symm⟩
          ⟨hsubstep⟩
        have hcore_throw : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .throw sc_arg.expr, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.throw arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_throw_step_arg arg sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := arg } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .throw sc_arg.expr, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_throw⟩, ?_⟩
        constructor
        · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
        constructor
        · have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · refine ⟨scope', st_a, st_a', ?_⟩
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .throw sa_flat.expr := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .throw sc_arg.expr := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          simp only [Flat.convertExpr]
          rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
            (sa_flat.expr, st_a') from hconv_arg.symm]
  | tryCatch body catchParam catchBody finally_ =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    -- Set up sub-expression names
    set body' := (Flat.convertExpr body scope envVar envMap st).1 with hbody'_def
    set st1 := (Flat.convertExpr body scope envVar envMap st).2 with hst1_def
    set catchBody' := (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st1).1 with hcatchBody'_def
    set st2 := (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st1).2 with hst2_def
    set finally' := (Flat.convertOptExpr finally_ scope envVar envMap st2).1 with hfinally'_def
    set _st3 := (Flat.convertOptExpr finally_ scope envVar envMap st2).2 with _hst3_def
    have hsf_expr : sf.expr = .tryCatch body' catchParam catchBody' finally' := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    -- Case split on whether body is already a value
    cases hval : Core.exprValue? body with
    | some v =>
      -- Body is a value: tryCatch normal completion.
      -- Requires catchParam ≠ "__call_frame_return__" for Core semantics match.
      -- body = .lit v, body' = .lit (convertValue v)
      have ha_lit : body = .lit v := by cases body <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv hbody'_def
      have hsf_rw : sf = ⟨.tryCatch (.lit (Flat.convertValue v)) catchParam catchBody' finally', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      -- Case split on isCallFrame
      by_cases hcf : catchParam = "__call_frame_return__"
      · -- isCallFrame = true: contradiction with noCallFrameReturn
        exfalso
        have hncfr_tc : noCallFrameReturn (.tryCatch body catchParam catchBody finally_) = true := by
          rw [hsc] at hncfr; exact hncfr
        simp [noCallFrameReturn] at hncfr_tc
        exact absurd hcf (by rw [bne_iff_ne] at hncfr_tc; exact hncfr_tc.1)
      · -- isCallFrame = false: Core matches Flat behavior
        -- Case split on finally_
        cases hfin : finally_ with
        | none =>
          -- Both step to .lit v / .lit (convertValue v) with .silent
          have hflat_ev : ev = .silent := by
            rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
            exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
          subst hflat_ev
          obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
            rw [show sc = ⟨.tryCatch (.lit v) catchParam catchBody none, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all]
            exact ⟨_, Core.step_tryCatch_normal_noFinally v catchParam catchBody sc.env sc.heap sc.trace sc.funcs sc.callStack hcf⟩
          refine ⟨sc', ⟨hcstep⟩, ?_⟩
          have hsf'_trace : sf'.trace = sc'.trace := by
            have hf := hstep; have hc := hcstep
            rw [hsf_rw] at hf
            rw [show sc = ⟨.tryCatch (.lit v) catchParam catchBody none, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all] at hc
            simp only [Flat.step?, Flat.exprValue?] at hf
            simp only [Core.step?, Core.exprValue?, hcf] at hc
            have heqf := (Prod.mk.inj (Option.some.inj hf)).2; subst heqf
            have heqc := (Prod.mk.inj (Option.some.inj hc)).2; subst heqc
            show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
          have henv' : EnvCorr sc'.env sf'.env := by
            have hsf'_env : sf'.env = sf.env := by
              rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
              exact congrArg Flat.State.env (Prod.mk.inj (Option.some.inj hstep)).2 ▸ rfl
            have hsc'_env : sc'.env = sc.env := by
              rw [show sc = ⟨.tryCatch (.lit v) catchParam catchBody none, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
                from by cases sc; simp_all] at hcstep
              simp only [Core.step?, Core.exprValue?, hcf] at hcstep
              exact congrArg Core.State.env (Prod.mk.inj (Option.some.inj hcstep)).2 ▸ rfl
            rw [hsc'_env, hsf'_env]; exact henvCorr
          exact ⟨hsf'_trace, henv', by
            rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
            rw [show sc = ⟨.tryCatch (.lit v) catchParam catchBody none, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all] at hcstep
            simp only [Core.step?, Core.exprValue?, hcf] at hcstep
            have := (Prod.mk.inj (Option.some.inj hstep)).2; have := (Prod.mk.inj (Option.some.inj hcstep)).2
            subst_vars; exact hheap, by simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
            by simp [Flat.convertExpr, Flat.convertValue]; rfl⟩
        | some fin =>
          -- Both step to .seq fin (.lit v) / .seq fin' (.lit (convertValue v)) with .silent
          have hflat_ev : ev = .silent := by
            rw [hsf_rw] at hstep
            simp only [Flat.step?, Flat.exprValue?] at hstep
            rw [show finally' = (Flat.convertOptExpr (some fin) scope envVar envMap st2).1 from hfinally'_def] at hstep
            simp only [Flat.convertOptExpr] at hstep
            exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
          subst hflat_ev
          -- Core step
          have hsc_rw : sc = ⟨.tryCatch (.lit v) catchParam catchBody (some fin), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
            cases sc; simp_all
          obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
            rw [hsc_rw]; simp only [Core.step?, Core.exprValue?, hcf]; exact ⟨_, rfl⟩
          refine ⟨sc', ⟨hcstep⟩, ?_⟩
          have hsf'_trace : sf'.trace = sc'.trace := by
            have hf := hstep; have hc := hcstep
            rw [hsf_rw] at hf; rw [hsc_rw] at hc
            simp only [Flat.step?, Flat.exprValue?] at hf
            simp only [Core.step?, Core.exprValue?, hcf] at hc
            have heqf := (Prod.mk.inj (Option.some.inj hf)).2; subst heqf
            have heqc := (Prod.mk.inj (Option.some.inj hc)).2; subst heqc
            show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
          have henv' : EnvCorr sc'.env sf'.env := by
            have hsf'_env : sf'.env = sf.env := by
              rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
              exact congrArg Flat.State.env (Prod.mk.inj (Option.some.inj hstep)).2 ▸ rfl
            have hsc'_env : sc'.env = sc.env := by
              rw [hsc_rw] at hcstep; simp only [Core.step?, Core.exprValue?, hcf] at hcstep
              exact congrArg Core.State.env (Prod.mk.inj (Option.some.inj hcstep)).2 ▸ rfl
            rw [hsc'_env, hsf'_env]; exact henvCorr
          exact ⟨hsf'_trace, henv', by
            rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
            rw [hsc_rw] at hcstep; simp only [Core.step?, Core.exprValue?, hcf] at hcstep
            have := (Prod.mk.inj (Option.some.inj hstep)).2; have := (Prod.mk.inj (Option.some.inj hcstep)).2
            subst_vars; exact hheap, by
              have h := hncfr; rw [hsc] at h; subst ha_lit; simp [noCallFrameReturn, Bool.and_eq_true] at h
              rw [hfin] at h; simp [noCallFrameReturn, Bool.and_eq_true]; exact h.2.2, sorry /- ExprAddrWF -/, scope, st, (Flat.convertExpr fin scope envVar envMap st).2,
            by simp only [Flat.convertExpr]
               rw [hfinally'_def]; simp [Flat.convertOptExpr]; rfl⟩
    | none =>
      -- Body is not a value: sub-step
      have hbody'_nv : Flat.exprValue? body' = none := convertExpr_not_value body hval scope envVar envMap st
      have hsf_rw : sf = ⟨.tryCatch body' catchParam catchBody' finally', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hdepth : Core.Expr.depth body < n := by rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      -- Extract the Flat sub-step
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, hbody'_nv] at hstep
      cases hsubstep : Flat.step? ⟨body', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        -- Case split on whether this is an error event (catch) or normal event (wrap)
        cases ev_sub with
        | error msg =>
          -- Error from body: catch handler fires
          -- In Core, isCallFrame check determines behavior.
          -- Event is .error msg
          have hev_eq : ev = .error msg := (Prod.mk.inj (Option.some.inj hstep)).1
          subst hev_eq
          -- Apply IH to body step
          obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
            ih_depth (Core.Expr.depth body) hdepth envVar envMap
            ⟨body', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
            ⟨body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            (.error msg) sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.2.1) (sorry /- ExprAddrWF -/)
            ⟨scope, st, st1, by simp only [hbody'_def, hst1_def]; exact (Prod.eta _).symm⟩
            ⟨hsubstep⟩
          by_cases hcf : catchParam = "__call_frame_return__"
          · -- isCallFrame = true: contradiction with noCallFrameReturn
            exfalso
            have hncfr_tc : noCallFrameReturn (.tryCatch body catchParam catchBody finally_) = true := by
              rw [hsc] at hncfr; exact hncfr
            simp [noCallFrameReturn] at hncfr_tc
            exact absurd hcf (by rw [bne_iff_ne] at hncfr_tc; exact hncfr_tc.1)
          · -- isCallFrame = false: Core catches error same as Flat
            -- Determine the handler based on finally_
            set handler_core := (match finally_ with | some fin => Core.Expr.seq catchBody fin | none => catchBody)
            set handler_flat := (match finally' with | some fin => Flat.Expr.seq catchBody' fin | none => catchBody')
            -- Core step
            have hsc_rw : sc = ⟨Core.Expr.tryCatch body catchParam catchBody finally_, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
              cases sc; simp_all
            have hcore_err : Core.step? sc =
              some (.error msg, Core.pushTrace { sc_arg with expr := handler_core,
                env := sc_arg.env.extend catchParam (.string msg), trace := sc.trace } (.error msg)) := by
              rw [hsc_rw]; simp only [Core.step?, Core.exprValue?, hval]
              rw [show (⟨body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := body } from by cases sc; simp_all]
              rw [hcore_substep]
              simp only [BEq.beq, decide_eq_true_eq, hcf, ite_false, ↓reduceIte, Bool.and_self, Bool.false_and]
              rfl
            set sc' := Core.pushTrace { sc_arg with expr := handler_core,
              env := sc_arg.env.extend catchParam (.string msg), trace := sc.trace } (.error msg)
            refine ⟨sc', ⟨hcore_err⟩, ?_⟩
            constructor
            · -- Trace
              have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              rw [← hsf'_eq]; show sf.trace ++ [.error msg] = sc.trace ++ [.error msg]; rw [htrace]
            constructor
            · -- EnvCorr: both extend with catchParam → .string msg
              have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_env : sc'.env = sc_arg.env.extend catchParam (.string msg) := by simp [sc', Core.pushTrace]
              have hsf'_env : sf'.env = sa_flat.env.extend catchParam (Flat.Value.string msg) := by
                rw [← hsf'_eq]; rfl
              rw [hsc'_env, hsf'_env]
              exact EnvCorr_extend henvCorr_arg catchParam (.string msg)
            constructor
            · -- Heap
              have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsc'_heap : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
              rw [hsc'_heap]; convert hheap_arg using 1; rw [← hsf'_eq]; rfl
            · -- Expression correspondence
              have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
              have hsf'_expr : sf'.expr = handler_flat := by rw [← hsf'_eq]; rfl
              have hsc'_expr : sc'.expr = handler_core := by simp [sc', Core.pushTrace]
              rw [hsc'_expr, hsf'_expr]
              -- Case split on finally_ to determine handler shape
              cases hfin : finally_ with
              | none =>
                -- handler_core = catchBody, handler_flat = catchBody'
                simp only [hfin, handler_core, handler_flat]
                have hfin' : finally' = none := by
                  rw [hfinally'_def, hfin]; simp [Flat.convertOptExpr]
                simp only [hfin']
                refine ⟨catchParam :: scope, st1, ?_, ?_⟩
                · exact (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap st1).2
                · rw [hcatchBody'_def]; rfl
              | some fin =>
                -- handler_core = .seq catchBody fin, handler_flat = .seq catchBody' finally'
                simp only [hfin, handler_core, handler_flat]
                have hfin' : ∃ fin', finally' = some fin' := by
                  rw [hfinally'_def, hfin]; simp [Flat.convertOptExpr]; exact ⟨_, rfl⟩
                obtain ⟨fin', hfin'⟩ := hfin'
                simp only [hfin']
                refine ⟨scope, st1, ?_, ?_⟩
                · exact (Flat.convertExpr fin scope envVar envMap
                    (Flat.convertExpr catchBody scope envVar envMap st1).2).2
                · simp only [Flat.convertExpr]
                  rw [hcatchBody'_def,
                    convertExpr_scope_irrelevant catchBody (catchParam :: scope) scope envVar envMap st1]
                  congr 1
                  · congr 1
                    rw [hfinally'_def, hfin]; simp only [Flat.convertOptExpr]
                    rw [hst2_def, convertExpr_scope_irrelevant catchBody (catchParam :: scope) scope envVar envMap st1]
                  · rw [hfinally'_def, hfin]; simp only [Flat.convertOptExpr]
                    rw [hst2_def, convertExpr_scope_irrelevant catchBody (catchParam :: scope) scope envVar envMap st1]
        | silent =>
          -- Silent step in body: both Flat and Core wrap in tryCatch
          have hev_eq : ev = .silent := (Prod.mk.inj (Option.some.inj hstep)).1
          subst hev_eq
          -- Apply IH
          obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
            ih_depth (Core.Expr.depth body) hdepth envVar envMap
            ⟨body', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
            ⟨body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            .silent sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.2.1) (sorry /- ExprAddrWF -/)
            ⟨scope, st, st1, by simp only [hbody'_def, hst1_def]; exact (Prod.eta _).symm⟩
            ⟨hsubstep⟩
          -- Core steps with tryCatch wrapping
          have hcore_tc : Core.step? sc =
            some (.silent, Core.pushTrace { sc_arg with expr := .tryCatch sc_arg.expr catchParam catchBody finally_, trace := sc.trace } .silent) := by
            rw [show sc = ⟨.tryCatch body catchParam catchBody finally_, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all]
            exact Core.step_tryCatch_step_body_silent body catchParam catchBody finally_ sc.env sc.heap sc.trace sc.funcs sc.callStack hval sc_arg
              (by rw [show (⟨body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := body } from by cases sc; simp_all]; exact hcore_substep)
          set sc' := Core.pushTrace { sc_arg with expr := .tryCatch sc_arg.expr catchParam catchBody finally_, trace := sc.trace } .silent
          refine ⟨sc', ⟨hcore_tc⟩, ?_⟩
          constructor
          · -- Trace
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            rw [← hsf'_eq]; show sf.trace ++ [.silent] = sc.trace ++ [.silent]; rw [htrace]
          constructor
          · -- EnvCorr
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
            rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
          constructor
          · -- Heap
            have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
            rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
          · -- Expression correspondence
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .tryCatch sa_flat.expr catchParam catchBody' finally' := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .tryCatch sc_arg.expr catchParam catchBody finally_ := by simp [sc', Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]
            refine ⟨scope', st_a, ?_, ?_⟩
            · exact (Flat.convertOptExpr finally_ scope' envVar envMap
                (Flat.convertExpr catchBody (catchParam :: scope') envVar envMap
                  (Flat.convertExpr sc_arg.expr scope' envVar envMap st_a).2).2).2
            · simp only [Flat.convertExpr]
              rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
                (sa_flat.expr, st_a') from hconv_arg.symm]
              congr 1
              · congr 1
                · congr 1
                  · rw [hcatchBody'_def, hst1_def]
                    rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                      (Flat.convertExpr body scope envVar envMap st).2]
                    rfl
                  · rw [hfinally'_def, hst2_def, hst1_def]
                    rw [convertOptExpr_scope_irrelevant finally_ scope scope' envVar envMap
                      (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap
                        (Flat.convertExpr body scope envVar envMap st).2).2]
                    congr 1
                    rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                      (Flat.convertExpr body scope envVar envMap st).2]
                    rfl
                · rw [hfinally'_def, hst2_def, hst1_def]
                  rw [convertOptExpr_scope_irrelevant finally_ scope scope' envVar envMap _]
                  congr 1
                  rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                    (Flat.convertExpr body scope envVar envMap st).2]
                  rfl
              · rw [hfinally'_def, hst2_def, hst1_def]
                rw [convertOptExpr_scope_irrelevant finally_ scope scope' envVar envMap _]
                congr 1
                rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                  (Flat.convertExpr body scope envVar envMap st).2]
                rfl
        | log msg =>
          -- Log step in body: both Flat and Core wrap in tryCatch
          have hev_eq : ev = .log msg := (Prod.mk.inj (Option.some.inj hstep)).1
          subst hev_eq
          -- Apply IH
          obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
            ih_depth (Core.Expr.depth body) hdepth envVar envMap
            ⟨body', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
            ⟨body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            (.log msg) sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h.2.1) (sorry /- ExprAddrWF -/)
            ⟨scope, st, st1, by simp only [hbody'_def, hst1_def]; exact (Prod.eta _).symm⟩
            ⟨hsubstep⟩
          -- Core steps with tryCatch wrapping
          have hcore_tc : Core.step? sc =
            some (.log msg, Core.pushTrace { sc_arg with expr := .tryCatch sc_arg.expr catchParam catchBody finally_, trace := sc.trace } (.log msg)) := by
            rw [show sc = ⟨.tryCatch body catchParam catchBody finally_, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all]
            exact Core.step_tryCatch_step_body_log body catchParam catchBody finally_ sc.env sc.heap sc.trace sc.funcs sc.callStack hval msg sc_arg
              (by rw [show (⟨body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := body } from by cases sc; simp_all]; exact hcore_substep)
          set sc' := Core.pushTrace { sc_arg with expr := .tryCatch sc_arg.expr catchParam catchBody finally_, trace := sc.trace } (.log msg)
          refine ⟨sc', ⟨hcore_tc⟩, ?_⟩
          constructor
          · -- Trace
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            rw [← hsf'_eq]; show sf.trace ++ [.log msg] = sc.trace ++ [.log msg]; rw [htrace]
          constructor
          · -- EnvCorr
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
            rw [hsc'_env]; convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
          constructor
          · -- Heap
            have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
            rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
          · -- Expression correspondence (same as silent case)
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .tryCatch sa_flat.expr catchParam catchBody' finally' := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .tryCatch sc_arg.expr catchParam catchBody finally_ := by simp [sc', Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]
            refine ⟨scope', st_a, ?_, ?_⟩
            · exact (Flat.convertOptExpr finally_ scope' envVar envMap
                (Flat.convertExpr catchBody (catchParam :: scope') envVar envMap
                  (Flat.convertExpr sc_arg.expr scope' envVar envMap st_a).2).2).2
            · simp only [Flat.convertExpr]
              rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
                (sa_flat.expr, st_a') from hconv_arg.symm]
              congr 1
              · congr 1
                · congr 1
                  · rw [hcatchBody'_def, hst1_def]
                    rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                      (Flat.convertExpr body scope envVar envMap st).2]
                    rfl
                  · rw [hfinally'_def, hst2_def, hst1_def]
                    rw [convertOptExpr_scope_irrelevant finally_ scope scope' envVar envMap
                      (Flat.convertExpr catchBody (catchParam :: scope) envVar envMap
                        (Flat.convertExpr body scope envVar envMap st).2).2]
                    congr 1
                    rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                      (Flat.convertExpr body scope envVar envMap st).2]
                    rfl
                · rw [hfinally'_def, hst2_def, hst1_def]
                  rw [convertOptExpr_scope_irrelevant finally_ scope scope' envVar envMap _]
                  congr 1
                  rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                    (Flat.convertExpr body scope envVar envMap st).2]
                  rfl
              · rw [hfinally'_def, hst2_def, hst1_def]
                rw [convertOptExpr_scope_irrelevant finally_ scope scope' envVar envMap _]
                congr 1
                rw [convertExpr_scope_irrelevant catchBody (catchParam :: scope) (catchParam :: scope') envVar envMap
                  (Flat.convertExpr body scope envVar envMap st).2]
                rfl
  | while_ cond body =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    -- convertExpr (.while_ cond body) = (.while_ cond' body', st2)
    have hsf_expr : sf.expr = .while_ (Flat.convertExpr cond scope envVar envMap st).fst
        (Flat.convertExpr body scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    -- Both step with .silent, unfolding while to if-then-seq-while
    have hsf_rw : sf = ⟨Flat.Expr.while_
        (Flat.convertExpr cond scope envVar envMap st).fst
        (Flat.convertExpr body scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst,
        sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
      cases sf; simp_all
    have hsc_rw : sc = ⟨Core.Expr.while_ cond body, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
      cases sc; simp only [] at hsc ⊢; congr
    -- Flat steps with .silent
    have hflat_ev : ev = .silent := by
      rw [hsf_rw] at hstep; simp only [Flat.step?] at hstep
      exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
    subst hflat_ev
    -- Core also steps with .silent
    obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
      rw [hsc_rw]; simp only [Core.step?]; exact ⟨_, rfl⟩
    refine ⟨sc', ⟨hcstep⟩, ?_⟩
    -- Trace preservation
    have hsf'_trace : sf'.trace = sc'.trace := by
      have hf := hstep; have hc := hcstep
      rw [hsf_rw] at hf; rw [hsc_rw] at hc
      simp only [Flat.step?] at hf
      simp only [Core.step?] at hc
      have heqf := (Prod.mk.inj (Option.some.inj hf)).2
      have heqc := (Prod.mk.inj (Option.some.inj hc)).2
      subst heqf; subst heqc
      show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
    -- Env preservation (while_ doesn't change env)
    have henv' : EnvCorr sc'.env sf'.env := by
      have hsf'_env : sf'.env = sf.env := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?] at h0
        have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
      have hsc'_env : sc'.env = sc.env := by
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?] at h0
        have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
      rw [hsc'_env, hsf'_env]; exact henvCorr
    -- Expression correspondence: both lower to if cond (seq body (while_ cond body)) (lit undefined)
    -- sc'.expr = .if cond (.seq body (.while_ cond body)) (.lit .undefined)
    -- sf'.expr = .if cond' (.seq body' (.while_ cond' body')) (.lit .undefined)
    -- where cond' = convertExpr cond ..., body' = convertExpr body ...
    -- This should match convertExpr (.if cond (.seq body (.while_ cond body)) (.lit .undefined))
    have hsf'_expr : sf'.expr = .«if»
        (Flat.convertExpr cond scope envVar envMap st).fst
        (.seq (Flat.convertExpr body scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst
          (.while_ (Flat.convertExpr cond scope envVar envMap st).fst
            (Flat.convertExpr body scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst))
        (.lit .undefined) := by
      have h0 := hstep; rw [hsf_rw] at h0
      simp only [Flat.step?] at h0
      exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
    have hsc'_expr : sc'.expr = .«if» cond (.seq body (.while_ cond body)) (.lit .undefined) := by
      have h0 := hcstep; rw [hsc_rw] at h0
      simp only [Core.step?] at h0
      exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
    have hheap' : HeapCorr sc'.heap sf'.heap := by
      have h0 := hstep; rw [hsf_rw] at h0
      simp only [Flat.step?] at h0
      have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
      have h0 := hcstep; rw [hsc_rw] at h0
      simp only [Core.step?] at h0
      have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
    exact ⟨hsf'_trace, henv', hheap', by
      have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h
      rw [hsc'_expr]; simp [noCallFrameReturn, Bool.and_eq_true]; exact ⟨h.1, h.2, h.1, h.2⟩, sorry /- ExprAddrWF -/, scope, st, _,
      by simp only [Flat.convertExpr]; rw [hsc'_expr]; simp only [Flat.convertExpr, Flat.convertValue]; rw [hsf'_expr]⟩
  | «return» arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    -- convertExpr (.return arg) = (.return arg', st1) where arg' = convertOptExpr arg
    cases arg with
    | none =>
      -- .return none: both produce .error "return:undefined" and step to .lit .undefined
      have hsf_expr : sf.expr = .«return» none := by
        simp only [Flat.convertOptExpr] at hconv; cases sf; simp_all [(Prod.mk.inj hconv).1]
      have hflat_ev : ev = .error "return:undefined" := by
        rw [show sf = {sf with expr := .«return» none} from by cases sf; simp_all] at hstep
        simp only [Flat.step?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.error "return:undefined", sc') := by
        rw [show sc = {sc with expr := .«return» none} from by cases sc; simp_all]
        simp only [Core.step?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [show sf = {sf with expr := .«return» none} from by cases sf; simp_all] at hf
        rw [show sc = {sc with expr := .«return» none} from by cases sc; simp_all] at hc
        simp only [Flat.step?] at hf; simp only [Core.step?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep
          rw [show sf = {sf with expr := .«return» none} from by cases sf; simp_all] at h0
          simp only [Flat.step?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep
          rw [show sc = {sc with expr := .«return» none} from by cases sc; simp_all] at h0
          simp only [Core.step?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      have hsf'_expr : sf'.expr = .lit .undefined := by
        have h0 := hstep
        rw [show sf = {sf with expr := .«return» none} from by cases sf; simp_all] at h0
        simp only [Flat.step?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = .lit .undefined := by
        have h0 := hcstep
        rw [show sc = {sc with expr := .«return» none} from by cases sc; simp_all] at h0
        simp only [Core.step?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hheap' : HeapCorr sc'.heap sf'.heap := by
        have h0 := hstep
        rw [show sf = {sf with expr := .«return» none} from by cases sf; simp_all] at h0
        simp only [Flat.step?] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
        have h0 := hcstep
        rw [show sc = {sc with expr := .«return» none} from by cases sc; simp_all] at h0
        simp only [Core.step?] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
      exact ⟨hsf'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
        by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
    | some e =>
      -- .return (some e): split into value and stepping sub-cases
      simp only [Flat.convertOptExpr] at hconv
      have hsf_expr : sf.expr = .«return» (some (Flat.convertExpr e scope envVar envMap st).1) := by
        cases sf; simp_all [(Prod.mk.inj hconv).1]
      cases hval : Core.exprValue? e with
      | some v =>
        have he_lit : e = .lit v := by cases e <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
        subst he_lit
        simp only [Flat.convertExpr] at hsf_expr hconv
        have hsf_rw : sf = ⟨Flat.Expr.return (some (.lit (Flat.convertValue v))), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all
        have hsc_rw : sc = ⟨Core.Expr.return (some (.lit v)), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
          cases sc; simp only [] at hsc ⊢; congr
        -- Both produce .error ("return:" ++ valueToString v)
        have hflat_ev : ev = .error ("return:" ++ Flat.valueToString (Flat.convertValue v)) := by
          rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
          exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
        rw [valueToString_convertValue] at hflat_ev
        subst hflat_ev
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.error ("return:" ++ Core.valueToString v), sc') := by
          rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        have hsf'_trace : sf'.trace = sc'.trace := by
          have hf := hstep; have hc := hcstep
          rw [hsf_rw] at hf; rw [hsc_rw] at hc
          simp only [Flat.step?, Flat.exprValue?] at hf
          simp only [Core.step?, Core.exprValue?] at hc
          have heqf := (Prod.mk.inj (Option.some.inj hf)).2
          have heqc := (Prod.mk.inj (Option.some.inj hc)).2
          subst heqf; subst heqc
          show sf.trace ++ _ = sc.trace ++ _
          rw [htrace, valueToString_convertValue]
        have henv' : EnvCorr sc'.env sf'.env := by
          have hsf'_env : sf'.env = sf.env := by
            have h0 := hstep; rw [hsf_rw] at h0
            simp only [Flat.step?, Flat.exprValue?] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          have hsc'_env : sc'.env = sc.env := by
            have h0 := hcstep; rw [hsc_rw] at h0
            simp only [Core.step?, Core.exprValue?] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          rw [hsc'_env, hsf'_env]; exact henvCorr
        have hsf'_expr : sf'.expr = .lit (Flat.convertValue v) := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hsc'_expr : sc'.expr = .lit v := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        exact ⟨hsf'_trace, henv', by
        have h0 := hstep; rw [hsf_rw] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := hcstep; rw [hsc_rw] at h1; simp only [Core.step?, Core.exprValue?] at h1
        have := (Prod.mk.inj (Option.some.inj h0)).2; have := (Prod.mk.inj (Option.some.inj h1)).2
        subst_vars; exact hheap, by simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
          by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
      | none =>
        -- Stepping sub-case for return (some e): same single-subexpr pattern
        set e' := (Flat.convertExpr e scope envVar envMap st).1 with he'_def
        set st1 := (Flat.convertExpr e scope envVar envMap st).2 with hst1_def
        have he'_nv : Flat.exprValue? e' = none := convertExpr_not_value e hval scope envVar envMap st
        have hsf_rw : sf = ⟨.«return» (some e'), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by cases sf; simp_all
        have hdepth : Core.Expr.depth e < n := by rw [← hd, hsc]; simp [Core.Expr.depth]; omega
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?, he'_nv] at hstep
        cases hsubstep : Flat.step? ⟨e', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
        | none => simp [hsubstep] at hstep
        | some p =>
          obtain ⟨ev_sub, sa_flat⟩ := p
          simp only [hsubstep] at hstep
          have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
          subst hev_eq
          -- Apply IH (envVar/envMap carried through induction)
          obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
            ih_depth (Core.Expr.depth e) hdepth envVar envMap
            ⟨e', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
            ⟨e, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h) (sorry /- ExprAddrWF -/)
            ⟨scope, st, st1, by simp only [he'_def, hst1_def]; exact (Prod.eta _).symm⟩
            ⟨hsubstep⟩
          have hcore_ret : Core.step? sc =
            some (ev_sub, Core.pushTrace { sc_arg with expr := .«return» (some sc_arg.expr), trace := sc.trace } ev_sub) := by
            rw [show sc = ⟨.«return» (some e), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all]
            exact Core.step_return_step_arg e sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
              (by rw [show (⟨e, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := e } from by cases sc; simp_all]; exact hcore_substep)
          set sc' := Core.pushTrace { sc_arg with expr := .«return» (some sc_arg.expr), trace := sc.trace } ev_sub
          refine ⟨sc', ⟨hcore_ret⟩, ?_⟩
          constructor
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
          constructor
          · have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
            rw [hsc'_env]
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
          constructor
          · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
          · refine ⟨scope', st_a, st_a', ?_⟩
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .«return» (some sa_flat.expr) := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .«return» (some sc_arg.expr) := by simp [sc', Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]
            simp only [Flat.convertExpr, Flat.convertOptExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
  | yield arg delegate =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    cases arg with
    | none =>
      -- .yield none: both produce .silent and step to .lit .undefined
      have hsf_expr : sf.expr = .yield none delegate := by
        simp only [Flat.convertOptExpr] at hconv; cases sf; simp_all [(Prod.mk.inj hconv).1]
      have hflat_ev : ev = .silent := by
        rw [show sf = {sf with expr := .yield none delegate} from by cases sf; simp_all] at hstep
        simp only [Flat.step?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [show sc = {sc with expr := .yield none delegate} from by cases sc; simp_all]
        simp only [Core.step?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [show sf = {sf with expr := .yield none delegate} from by cases sf; simp_all] at hf
        rw [show sc = {sc with expr := .yield none delegate} from by cases sc; simp_all] at hc
        simp only [Flat.step?] at hf; simp only [Core.step?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep
          rw [show sf = {sf with expr := .yield none delegate} from by cases sf; simp_all] at h0
          simp only [Flat.step?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep
          rw [show sc = {sc with expr := .yield none delegate} from by cases sc; simp_all] at h0
          simp only [Core.step?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      have hsf'_expr : sf'.expr = .lit .undefined := by
        have h0 := hstep
        rw [show sf = {sf with expr := .yield none delegate} from by cases sf; simp_all] at h0
        simp only [Flat.step?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = .lit .undefined := by
        have h0 := hcstep
        rw [show sc = {sc with expr := .yield none delegate} from by cases sc; simp_all] at h0
        simp only [Core.step?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hheap' : HeapCorr sc'.heap sf'.heap := by
        have h0 := hstep
        rw [show sf = {sf with expr := .yield none delegate} from by cases sf; simp_all] at h0
        simp only [Flat.step?] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
        have h0 := hcstep
        rw [show sc = {sc with expr := .yield none delegate} from by cases sc; simp_all] at h0
        simp only [Core.step?] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
      exact ⟨hsf'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
        by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
    | some e =>
      -- .yield (some e): split into value and stepping sub-cases
      simp only [Flat.convertOptExpr] at hconv
      have hsf_expr : sf.expr = .yield (some (Flat.convertExpr e scope envVar envMap st).1) delegate := by
        cases sf; simp_all [(Prod.mk.inj hconv).1]
      cases hval : Core.exprValue? e with
      | some v =>
        have ha_lit : e = .lit v := by cases e <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
        subst ha_lit
        simp only [Flat.convertExpr] at hsf_expr hconv
        have hsf_rw : sf = ⟨Flat.Expr.yield (some (.lit (Flat.convertValue v))) delegate, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
          cases sf; simp_all
        have hsc_rw : sc = ⟨Core.Expr.yield (some (.lit v)) delegate, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
          cases sc; simp only [] at hsc ⊢; congr
        have hflat_ev : ev = .silent := by
          rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
          exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
        subst hflat_ev
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
          rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        have hsf'_trace : sf'.trace = sc'.trace := by
          have hf := hstep; have hc := hcstep
          rw [hsf_rw] at hf; rw [hsc_rw] at hc
          simp only [Flat.step?, Flat.exprValue?] at hf
          simp only [Core.step?, Core.exprValue?] at hc
          have heqf := (Prod.mk.inj (Option.some.inj hf)).2
          have heqc := (Prod.mk.inj (Option.some.inj hc)).2
          subst heqf; subst heqc
          show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
        have henv' : EnvCorr sc'.env sf'.env := by
          have hsf'_env : sf'.env = sf.env := by
            have h0 := hstep; rw [hsf_rw] at h0
            simp only [Flat.step?, Flat.exprValue?] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          have hsc'_env : sc'.env = sc.env := by
            have h0 := hcstep; rw [hsc_rw] at h0
            simp only [Core.step?, Core.exprValue?] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          rw [hsc'_env, hsf'_env]; exact henvCorr
        have hsf'_expr : sf'.expr = .lit (Flat.convertValue v) := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hsc'_expr : sc'.expr = .lit v := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        exact ⟨hsf'_trace, henv', by
        have h0 := hstep; rw [hsf_rw] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := hcstep; rw [hsc_rw] at h1; simp only [Core.step?, Core.exprValue?] at h1
        have := (Prod.mk.inj (Option.some.inj h0)).2; have := (Prod.mk.inj (Option.some.inj h1)).2
        subst_vars; exact hheap, by simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
          by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
      | none =>
        -- Stepping sub-case for yield (some e): single-subexpr pattern
        set e' := (Flat.convertExpr e scope envVar envMap st).1 with he'_def
        set st1 := (Flat.convertExpr e scope envVar envMap st).2 with hst1_def
        have he'_nv : Flat.exprValue? e' = none := convertExpr_not_value e hval scope envVar envMap st
        have hsf_rw : sf = ⟨.yield (some e') delegate, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by cases sf; simp_all
        have hdepth : Core.Expr.depth e < n := by rw [← hd, hsc]; simp [Core.Expr.depth]; omega
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?, he'_nv] at hstep
        cases hsubstep : Flat.step? ⟨e', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
        | none => simp [hsubstep] at hstep
        | some p =>
          obtain ⟨ev_sub, sa_flat⟩ := p
          simp only [hsubstep] at hstep
          have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
          subst hev_eq
          -- Apply IH (envVar/envMap carried through induction)
          obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
            ih_depth (Core.Expr.depth e) hdepth envVar envMap
            ⟨e', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
            ⟨e, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h) (sorry /- ExprAddrWF -/)
            ⟨scope, st, st1, by simp only [he'_def, hst1_def]; exact (Prod.eta _).symm⟩
            ⟨hsubstep⟩
          have hcore_yield : Core.step? sc =
            some (ev_sub, Core.pushTrace { sc_arg with expr := .yield (some sc_arg.expr) delegate, trace := sc.trace } ev_sub) := by
            rw [show sc = ⟨.yield (some e) delegate, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
              from by cases sc; simp_all]
            exact Core.step_yield_step_arg e delegate sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
              (by rw [show (⟨e, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
                { sc with expr := e } from by cases sc; simp_all]; exact hcore_substep)
          set sc' := Core.pushTrace { sc_arg with expr := .yield (some sc_arg.expr) delegate, trace := sc.trace } ev_sub
          refine ⟨sc', ⟨hcore_yield⟩, ?_⟩
          constructor
          · have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            rw [← hsf'_eq]; show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]; rw [htrace]
          constructor
          · have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
            rw [hsc'_env]
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            convert henvCorr_arg using 1; rw [← hsf'_eq]; rfl
          constructor
          · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
          · refine ⟨scope', st_a, st_a', ?_⟩
            have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
            have hsf'_expr : sf'.expr = .yield (some sa_flat.expr) delegate := by rw [← hsf'_eq]; rfl
            have hsc'_expr : sc'.expr = .yield (some sc_arg.expr) delegate := by simp [sc', Core.pushTrace]
            rw [hsc'_expr, hsf'_expr]
            simp only [Flat.convertExpr, Flat.convertOptExpr]
            rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
              (sa_flat.expr, st_a') from hconv_arg.symm]
  | await arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .await (Flat.convertExpr arg scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? arg with
    | some v =>
      have ha_lit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.await (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      have hsc_rw : sc = ⟨Core.Expr.await (.lit v), sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ := by
        cases sc; simp only [] at hsc ⊢; congr
      have hflat_ev : ev = .silent := by
        rw [hsf_rw] at hstep; simp only [Flat.step?, Flat.exprValue?] at hstep
        exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
      subst hflat_ev
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [hsc_rw]; simp only [Core.step?, Core.exprValue?]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [hsf_rw] at hf; rw [hsc_rw] at hc
        simp only [Flat.step?, Flat.exprValue?] at hf
        simp only [Core.step?, Core.exprValue?] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep; rw [hsf_rw] at h0
          simp only [Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep; rw [hsc_rw] at h0
          simp only [Core.step?, Core.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      have hsf'_expr : sf'.expr = .lit (Flat.convertValue v) := by
        have h0 := hstep; rw [hsf_rw] at h0
        simp only [Flat.step?, Flat.exprValue?] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = .lit v := by
        have h0 := hcstep; rw [hsc_rw] at h0
        simp only [Core.step?, Core.exprValue?] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      exact ⟨hsf'_trace, henv', by
        have h0 := hstep; rw [hsf_rw] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
        have h1 := hcstep; rw [hsc_rw] at h1; simp only [Core.step?, Core.exprValue?] at h1
        have := (Prod.mk.inj (Option.some.inj h0)).2; have := (Prod.mk.inj (Option.some.inj h1)).2
        subst_vars; exact hheap, by simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
    | none =>
      -- arg' is the converted sub-expression
      set arg' := (Flat.convertExpr arg scope envVar envMap st).1 with harg'_def
      set st1 := (Flat.convertExpr arg scope envVar envMap st).2 with hst1_def
      have harg'_nv : Flat.exprValue? arg' = none := convertExpr_not_value arg hval scope envVar envMap st
      have hsf_rw : sf = ⟨.await arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ := by
        cases sf; simp_all
      -- Depth of arg < n
      have hdepth : Core.Expr.depth arg < n := by
        rw [← hd, hsc]; simp [Core.Expr.depth]; omega
      -- Extract Flat sub-step
      rw [hsf_rw] at hstep
      simp only [Flat.step?, Flat.exprValue?, harg'_nv] at hstep
      -- Case split on step? of arg'
      cases hsubstep : Flat.step? ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ with
      | none => simp [hsubstep] at hstep
      | some p =>
        obtain ⟨ev_sub, sa_flat⟩ := p
        simp only [hsubstep] at hstep
        have hev_eq : ev = ev_sub := (Prod.mk.inj (Option.some.inj hstep)).1
        subst hev_eq
        -- Flat.Step for sub-expression
        have hflat_step_sub : Flat.Step ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩ ev_sub sa_flat :=
          ⟨hsubstep⟩
        -- Apply IH (envVar/envMap carried through induction)
        obtain ⟨sc_arg, ⟨hcore_substep⟩, htrace_arg, henvCorr_arg, hheap_arg, hncfr_arg, _hexprwf_arg, scope', st_a, st_a', hconv_arg⟩ :=
          ih_depth (Core.Expr.depth arg) hdepth envVar envMap
          ⟨arg', sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
          ⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
          ev_sub sa_flat rfl htrace henvCorr hheap (by have h := hncfr; rw [hsc] at h; simp [noCallFrameReturn, Bool.and_eq_true] at h; exact h) (sorry /- ExprAddrWF -/)
          ⟨scope, st, st1, by simp only [harg'_def, hst1_def]; exact (Prod.eta _).symm⟩
          hflat_step_sub
        -- Construct Core step on .await arg using step_await_step_arg
        have hcore_await : Core.step? sc =
          some (ev_sub, Core.pushTrace { sc_arg with expr := .await sc_arg.expr, trace := sc.trace } ev_sub) := by
          rw [show sc = ⟨.await arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩
            from by cases sc; simp_all]
          exact Core.step_await_step_arg arg sc.env sc.heap sc.trace sc.funcs sc.callStack hval ev_sub sc_arg
            (by rw [show (⟨arg, sc.env, sc.heap, sc.trace, sc.funcs, sc.callStack⟩ : Core.State) =
              { sc with expr := arg } from by cases sc; simp_all]; exact hcore_substep)
        set sc' := Core.pushTrace { sc_arg with expr := .await sc_arg.expr, trace := sc.trace } ev_sub
        refine ⟨sc', ⟨hcore_await⟩, ?_⟩
        constructor
        · -- Trace
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          rw [← hsf'_eq]
          show sf.trace ++ [ev_sub] = sc.trace ++ [ev_sub]
          rw [htrace]
        constructor
        · -- EnvCorr
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc'_env : sc'.env = sc_arg.env := by simp [sc', Core.pushTrace]
          rw [hsc'_env]
          convert henvCorr_arg using 1
          rw [← hsf'_eq]; rfl
        constructor
        · have hsf_eq_hp := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsc_heap_hp : sc'.heap = sc_arg.heap := by simp [sc', Core.pushTrace]
          rw [hsc_heap_hp]; convert hheap_arg using 1; rw [← hsf_eq_hp]; rfl
        · -- Expression correspondence
          refine ⟨scope', st_a, st_a', ?_⟩
          have hsf'_eq := (Prod.mk.inj (Option.some.inj hstep)).2
          have hsf'_expr : sf'.expr = .await sa_flat.expr := by rw [← hsf'_eq]; rfl
          have hsc'_expr : sc'.expr = .await sc_arg.expr := by simp [sc', Core.pushTrace]
          rw [hsc'_expr, hsf'_expr]
          simp only [Flat.convertExpr]
          rw [show Flat.convertExpr sc_arg.expr scope' envVar envMap st_a =
            (sa_flat.expr, st_a') from hconv_arg.symm]
  | this =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .this := by cases sf; simp_all [(Prod.mk.inj hconv).1]
    -- Both Core and Flat .this always produce .silent
    have hflat_ev : ev = .silent := by
      rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at hstep
      simp only [Flat.step?] at hstep
      split at hstep <;> exact (Prod.mk.inj (Option.some.inj hstep)).1.symm
    subst hflat_ev
    -- Case split on Flat env lookup of "this"
    cases hfenv : sf.env.lookup "this" with
    | some fv =>
      -- EnvCorr gives us Core also has "this"
      obtain ⟨cv, hcenv, hfv_eq⟩ := henvCorr.1 "this" fv hfenv
      -- Core step
      obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
        rw [show sc = {sc with expr := .this} from by cases sc; simp_all]
        simp only [Core.step?, hcenv]; exact ⟨_, rfl⟩
      refine ⟨sc', ⟨hcstep⟩, ?_⟩
      -- Trace preservation
      have hsf'_trace : sf'.trace = sc'.trace := by
        have hf := hstep; have hc := hcstep
        rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at hf
        rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at hc
        simp only [Flat.step?, hfenv] at hf; simp only [Core.step?, hcenv] at hc
        have heqf := (Prod.mk.inj (Option.some.inj hf)).2
        have heqc := (Prod.mk.inj (Option.some.inj hc)).2
        subst heqf; subst heqc
        show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
      -- EnvCorr preservation (env unchanged by .this step)
      have henv' : EnvCorr sc'.env sf'.env := by
        have hsf'_env : sf'.env = sf.env := by
          have h0 := hstep
          rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at h0
          simp only [Flat.step?, hfenv] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        have hsc'_env : sc'.env = sc.env := by
          have h0 := hcstep
          rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at h0
          simp only [Core.step?, hcenv] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
        rw [hsc'_env, hsf'_env]; exact henvCorr
      -- Expression correspondence: sf'.expr = .lit fv, sc'.expr = .lit cv
      have hsf'_expr : sf'.expr = .lit fv := by
        have h0 := hstep
        rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at h0
        simp only [Flat.step?, hfenv] at h0
        exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hsc'_expr : sc'.expr = .lit cv := by
        have h0 := hcstep
        rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at h0
        simp only [Core.step?, hcenv] at h0
        exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
      have hheap' : HeapCorr sc'.heap sf'.heap := by
        have h0 := hstep
        rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at h0
        simp only [Flat.step?, hfenv] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
        have h0 := hcstep
        rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at h0
        simp only [Core.step?, hcenv] at h0
        have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
      exact ⟨hsf'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st,
        (Flat.convertExpr (.lit cv) scope envVar envMap st).2,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr, hfv_eq]⟩
    | none =>
      -- Flat doesn't find "this" → produces .lit .undefined
      -- Case split on Core env lookup
      cases hcenv : sc.env.lookup "this" with
      | none =>
        -- Both produce .lit .undefined
        obtain ⟨sc', hcstep⟩ : ∃ sc', Core.step? sc = some (.silent, sc') := by
          rw [show sc = {sc with expr := .this} from by cases sc; simp_all]
          simp only [Core.step?, hcenv]; exact ⟨_, rfl⟩
        refine ⟨sc', ⟨hcstep⟩, ?_⟩
        have hsf'_trace : sf'.trace = sc'.trace := by
          have hf := hstep; have hc := hcstep
          rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at hf
          rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at hc
          simp only [Flat.step?, hfenv] at hf; simp only [Core.step?, hcenv] at hc
          have heqf := (Prod.mk.inj (Option.some.inj hf)).2
          have heqc := (Prod.mk.inj (Option.some.inj hc)).2
          subst heqf; subst heqc
          show sf.trace ++ _ = sc.trace ++ _; rw [htrace]
        have henv' : EnvCorr sc'.env sf'.env := by
          have hsf'_env : sf'.env = sf.env := by
            have h0 := hstep
            rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at h0
            simp only [Flat.step?, hfenv] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          have hsc'_env : sc'.env = sc.env := by
            have h0 := hcstep
            rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at h0
            simp only [Core.step?, hcenv] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
          rw [hsc'_env, hsf'_env]; exact henvCorr
        have hsf'_expr : sf'.expr = .lit .undefined := by
          have h0 := hstep
          rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at h0
          simp only [Flat.step?, hfenv] at h0
          exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hsc'_expr : sc'.expr = .lit .undefined := by
          have h0 := hcstep
          rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at h0
          simp only [Core.step?, hcenv] at h0
          exact congrArg Core.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hheap' : HeapCorr sc'.heap sf'.heap := by
          have h0 := hstep
          rw [show sf = {sf with expr := .this} from by cases sf; simp_all] at h0
          simp only [Flat.step?, hfenv] at h0
          have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1
          have h0 := hcstep
          rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at h0
          simp only [Core.step?, hcenv] at h0
          have h1 := (Prod.mk.inj (Option.some.inj h0)).2; subst h1; exact hheap
        exact ⟨hsf'_trace, henv', hheap', by rw [hsc'_expr]; simp [noCallFrameReturn], sorry /- ExprAddrWF -/, scope, st, st,
          by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
      | some cv =>
        -- Core has "this" but Flat doesn't → contradiction via EnvCorr.2
        exfalso
        obtain ⟨fv, hfenv', _⟩ := henvCorr.2 "this" cv hcenv
        simp [hfenv] at hfenv'

/-! ### step?_none_implies_lit -/

/-- The only Flat expression where step? returns none is a literal value. -/
private theorem step?_none_implies_lit_aux :
    ∀ (n : Nat) (s : Flat.State),
      s.expr.depth ≤ n → Flat.step? s = none → ∃ v, s.expr = .lit v := by
  intro n
  induction n with
  | zero =>
    intro ⟨fexpr, fenv, fheap, ftrace⟩ hd h
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
    intro ⟨fexpr, fenv, fheap, ftrace⟩ hd h
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
          have ⟨v, hv⟩ := ih ⟨a, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨init, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨value, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨cond, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨arg, fenv, fheap, ftrace⟩
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
        cases hstep : Flat.step? ⟨obj, fenv, fheap, ftrace⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | deleteProp obj _prop =>
      exfalso
      cases hev : Flat.exprValue? obj with
      | some v =>
        unfold Flat.step? at h; simp only [hev] at h
        split at h <;> contradiction
      | none =>
        cases hstep : Flat.step? ⟨obj, fenv, fheap, ftrace⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | makeClosure _idx envExpr =>
      exfalso
      cases hev : Flat.exprValue? envExpr with
      | some v =>
        unfold Flat.step? at h; simp only [hev] at h
        split at h <;> contradiction
      | none =>
        cases hstep : Flat.step? ⟨envExpr, fenv, fheap, ftrace⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | getEnv envExpr _idx =>
      exfalso
      cases hev : Flat.exprValue? envExpr with
      | some v =>
        unfold Flat.step? at h; simp only [hev] at h
        repeat (first | contradiction | split at h)
      | none =>
        cases hstep : Flat.step? ⟨envExpr, fenv, fheap, ftrace⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
        | none =>
          have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace⟩
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
          cases hstep : Flat.step? ⟨e, fenv, fheap, ftrace⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
          | none =>
            have ⟨v, hv⟩ := ih ⟨e, fenv, fheap, ftrace⟩
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
          cases hstep : Flat.step? ⟨e, fenv, fheap, ftrace⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hev, hstep] at h; contradiction
          | none =>
            have ⟨v, hv⟩ := ih ⟨e, fenv, fheap, ftrace⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev
    | binary _op lhs rhs =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevl =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨v, hv⟩ := ih ⟨lhs, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevl; simp [Flat.exprValue?] at hevl
      next _ =>
        split at h
        next hevr =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨rhs, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevo; simp [Flat.exprValue?] at hevo
      next _ =>
        split at h
        next => simp at h
        next hevv =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨value, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevo; simp [Flat.exprValue?] at hevo
      next _ =>
        split at h
        next => simp at h
        next hevi =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨idx, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨obj, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
          simp at hv; rw [hv] at hevo; simp [Flat.exprValue?] at hevo
      next _ =>
        split at h
        next hevi =>
          split at h
          next => simp at h
          next hstep =>
            have ⟨v, hv⟩ := ih ⟨idx, fenv, fheap, ftrace⟩
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep
            simp at hv; rw [hv] at hevi; simp [Flat.exprValue?] at hevi
        next _ =>
          split at h
          next => simp at h
          next hevv =>
            split at h
            next => simp at h
            next hstep =>
              have ⟨v, hv⟩ := ih ⟨value, fenv, fheap, ftrace⟩
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
          have ⟨v, hv⟩ := ih ⟨body, fenv, fheap, ftrace⟩
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
        cases hstepf : Flat.step? ⟨funcExpr, fenv, fheap, ftrace⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hevf, hstepf] at h; exact absurd h (by simp)
        | none =>
          have ⟨v, hv⟩ := ih ⟨funcExpr, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepf
          simp at hv; rw [hv] at hevf; simp [Flat.exprValue?] at hevf
      | some vf =>
        cases heve : Flat.exprValue? envExpr with
        | none =>
          cases hstepe : Flat.step? ⟨envExpr, fenv, fheap, ftrace⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hevf, heve, hstepe] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace⟩
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
              cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace⟩ with
              | some r =>
                unfold Flat.step? at h; simp only [hevf, heve, hvals] at h
                rw [show Flat.firstNonValueExpr args = some (done, target, remaining) from hf] at h
                simp only [hstept] at h; exact absurd h (by simp)
              | none =>
                have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace⟩
                  (by simp [Flat.Expr.depth] at hd ⊢
                      have := Flat.firstNonValueExpr_depth hf; omega) hstept
                exact absurd hv (firstNonValueExpr_not_lit hf v)
    | newObj funcExpr envExpr args =>
      exfalso
      cases hevf : Flat.exprValue? funcExpr with
      | none =>
        cases hstepf : Flat.step? ⟨funcExpr, fenv, fheap, ftrace⟩ with
        | some r =>
          unfold Flat.step? at h; simp only [hevf, hstepf] at h; exact absurd h (by simp)
        | none =>
          have ⟨v, hv⟩ := ih ⟨funcExpr, fenv, fheap, ftrace⟩
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstepf
          simp at hv; rw [hv] at hevf; simp [Flat.exprValue?] at hevf
      | some vf =>
        cases heve : Flat.exprValue? envExpr with
        | none =>
          cases hstepe : Flat.step? ⟨envExpr, fenv, fheap, ftrace⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hevf, heve, hstepe] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨envExpr, fenv, fheap, ftrace⟩
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
              cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace⟩ with
              | some r =>
                unfold Flat.step? at h; simp only [hevf, heve, hvals] at h
                rw [show Flat.firstNonValueExpr args = some (done, target, remaining) from hf] at h
                simp only [hstept] at h; exact absurd h (by simp)
              | none =>
                have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace⟩
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
          cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hvals] at h
            rw [show Flat.firstNonValueExpr values = some (done, target, remaining) from hf] at h
            simp only [hstept] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace⟩
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
          cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hvals] at h
            rw [show Flat.firstNonValueProp props = some (done, propName, target, remaining) from hf] at h
            simp only [hstept] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace⟩
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
          cases hstept : Flat.step? ⟨target, fenv, fheap, ftrace⟩ with
          | some r =>
            unfold Flat.step? at h; simp only [hvals] at h
            rw [show Flat.firstNonValueExpr elems = some (done, target, remaining) from hf] at h
            simp only [hstept] at h; exact absurd h (by simp)
          | none =>
            have ⟨v, hv⟩ := ih ⟨target, fenv, fheap, ftrace⟩
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
  intro sf sc ⟨htrace, _henvCorr, _hheap, _hncfr, _hexprwf, scope, envVar, envMap, st, st', hconv⟩ hhalt hnoForIn hnoForOf
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
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → Core.Behaves s b := by
  intro b ⟨sf, hsteps, hhalt⟩
  have hinit := closureConvert_init_related s t h h_wf
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
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact closureConvert_trace_reflection s t h h_wf hnofor b hb

end VerifiedJS.Proofs
