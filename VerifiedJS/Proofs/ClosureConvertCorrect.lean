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

/-- Simulation relation for closure conversion: Flat and Core states
    have matching traces, and expression correspondence through the conversion. -/
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st

private theorem closureConvert_init_related
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    CC_SimRel s t (Flat.initialState t) (Core.initialState s) := by
  unfold CC_SimRel Flat.initialState Core.initialState
  constructor
  · rfl
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
  intro sf sc ev sf' ⟨htrace, scope, envVar, envMap, st, st', hconv⟩ ⟨hstep⟩
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
  | _ => all_goals sorry

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
  intro sf sc ⟨htrace, scope, envVar, envMap, st, st', hconv⟩ hhalt hnoForIn hnoForOf
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
