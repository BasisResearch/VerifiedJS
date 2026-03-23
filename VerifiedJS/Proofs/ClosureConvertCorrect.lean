/-
  VerifiedJS — Closure Conversion Correctness Proof
  JS.Core → JS.Flat semantic preservation.
-/

import VerifiedJS.Flat.ClosureConvert
import VerifiedJS.Core.Semantics
import VerifiedJS.Flat.Semantics

set_option maxHeartbeats 400000

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
  | _ => sorry -- BLOCKED: Flat.evalBinary differs from Core for add/eq/neq/lt/gt/le/ge/bitwise/mod/exp/instanceof/in

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

/-- Simulation relation for closure conversion: Flat and Core states
    have matching traces, environment correspondence, and expression
    correspondence through the conversion. -/
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  EnvCorr sc.env sf.env ∧
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st

private theorem closureConvert_init_related
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    CC_SimRel s t (Flat.initialState t) (Core.initialState s) := by
  unfold CC_SimRel Flat.initialState Core.initialState
  refine ⟨rfl, ?_, ?_⟩
  · -- EnvCorr: both envs have exactly one binding: "console" → .object 0
    have h_empty : EnvCorr Core.Env.empty Flat.Env.empty := by
      constructor <;> intro _ _ h <;> simp [Core.Env.empty, Core.Env.lookup, Flat.Env.empty, Flat.Env.lookup] at h
    exact EnvCorr_extend h_empty "console" (.object 0)
  · unfold Flat.closureConvert at h
    simp only [Except.ok.injEq] at h
    let st2 := (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).fst.foldl
      (fun s f => (s.addFunc f).2) (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).2
    refine ⟨[], "__env_main", [], st2,
      (Flat.convertExpr s.body [] "__env_main" [] st2).2, ?_⟩
    rw [← h]

private theorem closureConvert_step_simulation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State),
      CC_SimRel s t sf sc → Flat.Step sf ev sf' →
      ∃ sc', Core.Step sc ev sc' ∧ CC_SimRel s t sf' sc' := by
  intro sf sc ev sf' ⟨htrace, henvCorr, scope, envVar, envMap, st, st', hconv⟩ ⟨hstep⟩
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
    exact ⟨hsf'_trace_eq_sc'_trace, henv', [], "", [], st', st', by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
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
    exact ⟨hsf'_trace_eq_sc'_trace, henv', [], "", [], st', st', by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
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
    exact ⟨hsf'_trace_eq_sc'_trace, henv', scope, envVar, envMap, st,
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
        exact ⟨hsf'_trace, henv', scope, envVar, envMap, st,
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
          exact ⟨hsf'_trace, henv', [], "", [], st, st,
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
      have hsf_rw : sf = ⟨Flat.Expr.«let» name (.lit (Flat.convertValue v)) (Flat.convertExpr body (name :: scope) envVar envMap st).fst, sf.env, sf.heap, sf.trace⟩ := by
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
      exact ⟨hsf'_trace, henv', name :: scope, envVar, envMap, st,
        (Flat.convertExpr body (name :: scope) envVar envMap st).snd,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
    | none =>
      sorry -- stepping sub-case: needs recursive step simulation
  | assign _ _ => sorry -- needs env correspondence
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
          sf.env, sf.heap, sf.trace⟩ := by
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
      cases hb : Core.toBoolean v with
      | true =>
        simp only [hbool_eq, hb, ite_true] at hsf'_expr hsc'_expr
        exact ⟨hsf'_trace, henv', scope, envVar, envMap, st,
          (Flat.convertExpr then_ scope envVar envMap st).snd,
          by rw [hsc'_expr]; simp [hsf'_expr]⟩
      | false =>
        simp only [hbool_eq, hb, ite_false] at hsf'_expr hsc'_expr
        exact ⟨hsf'_trace, henv', scope, envVar, envMap,
          (Flat.convertExpr then_ scope envVar envMap st).snd,
          (Flat.convertExpr else_ scope envVar envMap
            (Flat.convertExpr then_ scope envVar envMap st).snd).snd,
          by rw [hsc'_expr]; simp [hsf'_expr]⟩
    | none =>
      sorry -- stepping sub-case: needs recursive step simulation
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
      have hsf_rw : sf = ⟨Flat.Expr.seq (.lit (Flat.convertValue v)) (Flat.convertExpr b scope envVar envMap st).fst, sf.env, sf.heap, sf.trace⟩ := by
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
      exact ⟨hsf'_trace, henv', scope, envVar, envMap, st,
        (Flat.convertExpr b scope envVar envMap st).2,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
    | none =>
      -- Stepping sub-case: a is not a value, need recursive step simulation
      sorry
  | call _ _ => sorry -- needs env/heap/funcs correspondence
  | newObj _ _ => sorry -- needs env/heap correspondence
  | getProp _ _ => sorry -- needs env/heap correspondence
  | setProp _ _ _ => sorry -- needs env/heap correspondence
  | getIndex _ _ => sorry -- needs env/heap correspondence
  | setIndex _ _ _ => sorry -- needs env/heap correspondence
  | deleteProp _ _ => sorry -- needs env/heap correspondence
  | typeof arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .typeof (Flat.convertExpr arg scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? arg with
    | some v =>
      have ha_lit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.typeof (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace⟩ := by
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
        scope, envVar, envMap, st, st, ?_⟩
      cases v with
      | null => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | undefined => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | bool => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | number => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | string => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | function => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
      | object => simp [Flat.convertExpr, Flat.convertValue, Core.pushTrace]; rfl
    | none =>
      sorry -- stepping sub-case: needs recursive step simulation
  | unary op arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .unary op (Flat.convertExpr arg scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? arg with
    | some v =>
      have ha_lit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.unary op (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace⟩ := by
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
        scope, envVar, envMap, st, st, ?_⟩
      -- Expression correspondence via evalUnary_convertValue
      show (Flat.Expr.lit (Flat.evalUnary op (Flat.convertValue v)), st) =
           Flat.convertExpr (.lit (Core.evalUnary op v)) scope envVar envMap st
      simp only [Flat.convertExpr]
      congr 1; exact congrArg _ (evalUnary_convertValue op v)
    | none =>
      sorry -- stepping sub-case: needs recursive step simulation
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
            sf.env, sf.heap, sf.trace⟩ := by
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
          scope, envVar, envMap, st, st, ?_⟩
        -- Expression correspondence via evalBinary_convertValue
        show (Flat.Expr.lit (Flat.evalBinary op (Flat.convertValue lv) (Flat.convertValue rv)), st) =
             Flat.convertExpr (.lit (Core.evalBinary op lv rv)) scope envVar envMap st
        simp only [Flat.convertExpr]
        congr 1; exact congrArg _ (evalBinary_convertValue op lv rv)
      | none => sorry -- stepping sub-case: rhs needs evaluation
    | none => sorry -- stepping sub-case: lhs needs evaluation
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
      have hsf_rw : sf = ⟨Flat.Expr.throw (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace⟩ := by
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
      exact ⟨hsf'_trace, henv', scope, envVar, envMap, st, st,
        by rw [hsc'_expr]; simp [Flat.convertExpr, Flat.convertValue, hsf'_expr]⟩
    | none =>
      sorry -- stepping sub-case: needs recursive step simulation
  | tryCatch _ _ _ _ => sorry -- needs env correspondence
  | while_ _ _ => sorry -- needs env correspondence
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
      exact ⟨hsf'_trace, henv', [], "", [], st, st,
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
        have hsf_rw : sf = ⟨Flat.Expr.return (some (.lit (Flat.convertValue v))), sf.env, sf.heap, sf.trace⟩ := by
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
        exact ⟨hsf'_trace, henv', scope, envVar, envMap, st, st,
          by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
      | none =>
        sorry -- stepping sub-case: needs recursive step simulation
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
      exact ⟨hsf'_trace, henv', [], "", [], st, st,
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
        have hsf_rw : sf = ⟨Flat.Expr.yield (some (.lit (Flat.convertValue v))) delegate, sf.env, sf.heap, sf.trace⟩ := by
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
        exact ⟨hsf'_trace, henv', scope, envVar, envMap, st, st,
          by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
      | none =>
        sorry -- stepping sub-case: needs recursive step simulation
  | await arg =>
    rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    have hsf_expr : sf.expr = .await (Flat.convertExpr arg scope envVar envMap st).1 := by
      cases sf; simp_all [(Prod.mk.inj hconv).1]
    cases hval : Core.exprValue? arg with
    | some v =>
      have ha_lit : arg = .lit v := by cases arg <;> simp [Core.exprValue?] at hval <;> exact congrArg _ hval
      subst ha_lit
      simp only [Flat.convertExpr] at hsf_expr hconv
      have hsf_rw : sf = ⟨Flat.Expr.await (.lit (Flat.convertValue v)), sf.env, sf.heap, sf.trace⟩ := by
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
      exact ⟨hsf'_trace, henv', scope, envVar, envMap, st, st,
        by rw [hsc'_expr]; simp [Flat.convertExpr, hsf'_expr]⟩
    | none =>
      sorry -- stepping sub-case: needs recursive step simulation
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
      exact ⟨hsf'_trace, henv', scope, envVar, envMap, st,
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
        exact ⟨hsf'_trace, henv', [], "", [], st, st,
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
  intro sf sc ⟨htrace, _henvCorr, scope, envVar, envMap, st, st', hconv⟩ hhalt hnoForIn hnoForOf
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
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → Core.Behaves s b := by
  intro b ⟨sf, hsteps, hhalt⟩
  have hinit := closureConvert_init_related s t h
  obtain ⟨sc, hcsteps, hrel⟩ :=
    closureConvert_steps_simulation s t h _ _ _ _ hinit hsteps
  have hnoFor := hnofor sc _ hcsteps
  exact ⟨sc, hcsteps,
    closureConvert_halt_preservation s t h _ _ hrel hhalt hnoFor.1 hnoFor.2⟩

/-- Closure conversion preserves behavior, assuming the source program
    never reaches a forIn/forOf expression (unimplemented in closure conversion). -/
theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (hnofor : ∀ sc tr, Core.Steps (Core.initialState s) tr sc →
        (∀ b o f, sc.expr ≠ .forIn b o f) ∧ (∀ b i f, sc.expr ≠ .forOf b i f)) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact closureConvert_trace_reflection s t h hnofor b hb

end VerifiedJS.Proofs
