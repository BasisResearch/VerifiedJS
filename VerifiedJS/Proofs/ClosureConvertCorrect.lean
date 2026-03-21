/-
  VerifiedJS — Closure Conversion Correctness Proof
  JS.Core → JS.Flat semantic preservation.
-/

import VerifiedJS.Flat.ClosureConvert
import VerifiedJS.Core.Semantics
import VerifiedJS.Flat.Semantics

namespace VerifiedJS.Proofs

/-- Simulation relation for closure conversion: Flat and Core states
    have matching traces, and expression correspondence through the conversion.
    The expression correspondence means the Flat expression is the result of
    converting the Core expression via convertExpr. -/
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  -- Expression correspondence: Flat expr is the closure-converted form of Core expr
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st

private theorem closureConvert_init_related
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    CC_SimRel s t (Flat.initialState t) (Core.initialState s) := by
  unfold CC_SimRel Flat.initialState Core.initialState
  constructor
  · rfl
  · -- The Flat main expression is convertExpr of Core body
    unfold Flat.closureConvert at h
    simp only [Except.ok.injEq] at h
    -- h : { functions := ..., main := (convertExpr s.body ...).fst } = t
    -- Construct the witness using the exact state from closureConvert
    let st2 := (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).fst.foldl
      (fun s f => (s.addFunc f).2) (Flat.convertFuncDefs s.functions.toList Flat.CCState.empty).2
    refine ⟨[], "__env_main", [], st2,
      (Flat.convertExpr s.body [] "__env_main" [] st2).2, ?_⟩
    -- Goal: (sf.expr, ...) = convertExpr s.body [] "__env_main" [] st2
    -- sf.expr = (Flat.initialState t).expr = t.main
    -- t.main = (convertExpr s.body ...).fst (from h)
    rw [← h]

private theorem closureConvert_step_simulation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ (sf : Flat.State) (sc : Core.State) (ev : Core.TraceEvent) (sf' : Flat.State),
      CC_SimRel s t sf sc → Flat.Step sf ev sf' →
      ∃ sc', Core.Step sc ev sc' ∧ CC_SimRel s t sf' sc' := by
  sorry -- Requires case analysis on Flat.Step + expression correspondence through conversion

/-- The only Flat expression where step? returns none is a literal value.
    For non-lit base cases (var, this, break, continue, while_, labeled), step?
    always returns some. For compound cases, step? either returns some directly
    (when a subexpression is a value) or recurses with strictly smaller depth.
    By IH, the sub-step returns some (since only .lit has step?=none and .lit
    is a value), contradicting exprValue? returning none. -/
private theorem step?_none_implies_lit_aux :
    ∀ (n : Nat) (s : Flat.State),
      s.expr.depth ≤ n → Flat.step? s = none → ∃ v, s.expr = .lit v := by
  intro n
  induction n with
  | zero =>
    intro ⟨fexpr, fenv, fheap, ftrace⟩ hd h
    -- depth=0: only lit, var, this, break, continue, return none, yield none
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
    | «let» name init body =>
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
    | _ => all_goals sorry

private theorem step?_none_implies_lit (s : Flat.State) (h : Flat.step? s = none) :
    ∃ v, s.expr = .lit v :=
  step?_none_implies_lit_aux s.expr.depth s (Nat.le_refl _) h

private theorem closureConvert_halt_preservation
    (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ sf sc, CC_SimRel s t sf sc → Flat.step? sf = none → Core.step? sc = none := by
  intro sf sc ⟨htrace, scope, envVar, envMap, st, st', hconv⟩ hhalt
  -- From step?_none_implies_lit: sf.expr must be .lit v
  obtain ⟨v, hlit⟩ := step?_none_implies_lit sf hhalt
  -- Substitute sf.expr = .lit v into hconv
  -- hconv : (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st
  rw [hlit] at hconv
  -- Now hconv : (.lit v, st') = convertExpr sc.expr ...
  -- Case-split on sc.expr: only .lit, .forIn, .forOf produce .lit
  cases hsc : sc.expr with
  | lit w =>
    have hsc' : sc = { sc with expr := .lit w } := by cases sc; simp_all
    rw [hsc']; simp [Core.step?]
  | var name =>
    exfalso; rw [hsc] at hconv; simp only [Flat.convertExpr] at hconv
    split at hconv <;> simp [Prod.mk.injEq] at hconv
  | forIn _ _ _ =>
    -- convertExpr (.forIn ...) = (.lit .undefined, st) — halts, but Core.step? ≠ none
    -- Genuinely false: conversion loses behavior for unimplemented features
    sorry
  | forOf _ _ _ => sorry -- same as forIn
  | functionDef _ _ _ _ _ =>
    -- convertExpr produces .makeClosure which is not .lit
    -- Complex computation (free vars, captures, etc.) prevents direct simp
    exfalso; rw [hsc] at hconv; unfold Flat.convertExpr at hconv
    simp [Prod.mk.injEq] at hconv
  | _ =>
    -- All other constructors: convertExpr produces a non-.lit Flat.Expr
    -- hconv : (.lit v, st') = (non-lit-expr, st') is a contradiction
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
    (h : Flat.closureConvert s = .ok t) :
    ∀ b, Flat.Behaves t b → Core.Behaves s b := by
  intro b ⟨sf, hsteps, hhalt⟩
  have hinit := closureConvert_init_related s t h
  obtain ⟨sc, hcsteps, hrel⟩ :=
    closureConvert_steps_simulation s t h _ _ _ _ hinit hsteps
  exact ⟨sc, hcsteps, closureConvert_halt_preservation s t h _ _ hrel hhalt⟩

theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact closureConvert_trace_reflection s t h b hb

end VerifiedJS.Proofs
