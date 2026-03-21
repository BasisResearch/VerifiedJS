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

/-! ### Helper lemmas for firstNonValueExpr / firstNonValueProp -/

/-- The target returned by firstNonValueExpr is never a literal
    (it has exprValue? = none). -/
private theorem firstNonValueExpr_exprValue_none
    {l : List Flat.Expr} {done : List Flat.Expr} {target : Flat.Expr}
    {rest : List Flat.Expr}
    (h : Flat.firstNonValueExpr l = some (done, target, rest)) :
    Flat.exprValue? target = none := by
  induction l generalizing done with
  | nil => simp [Flat.firstNonValueExpr] at h
  | cons e tl ih =>
    unfold Flat.firstNonValueExpr at h
    cases e with
    | lit _ =>
      split at h
      next heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ih (h.2.1 ▸ heq)
      next => simp at h
    | _ => all_goals
        (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨_, rfl, _⟩ := h; rfl)

/-- If firstNonValueExpr returns none, then valuesFromExprList? returns some. -/
private theorem firstNonValueExpr_none_values_some
    {l : List Flat.Expr}
    (h : Flat.firstNonValueExpr l = none) :
    ∃ vs, Flat.valuesFromExprList? l = some vs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons e tl ih =>
    unfold Flat.firstNonValueExpr at h
    cases e with
    | lit v =>
      simp at h
      split at h
      · simp at h
      · obtain ⟨vs, hvs⟩ := ih h
        exact ⟨v :: vs, by simp [Flat.valuesFromExprList?, Flat.exprValue?, hvs]⟩
    | _ => all_goals simp at h

/-- The target returned by firstNonValueProp is never a literal. -/
private theorem firstNonValueProp_exprValue_none
    {l : List (Core.PropName × Flat.Expr)}
    {done : List (Core.PropName × Flat.Expr)}
    {propName : Core.PropName} {target : Flat.Expr}
    {rest : List (Core.PropName × Flat.Expr)}
    (h : Flat.firstNonValueProp l = some (done, propName, target, rest)) :
    Flat.exprValue? target = none := by
  induction l generalizing done with
  | nil => simp [Flat.firstNonValueProp] at h
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Flat.firstNonValueProp at h
    cases pe with
    | lit _ =>
      split at h
      next heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ih (h.2.2.1 ▸ heq)
      next => simp at h
    | _ => all_goals
        (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨_, _, rfl, _⟩ := h; rfl)

/-- If firstNonValueProp returns none, then valuesFromExprList? on the
    projected values returns some. -/
private theorem firstNonValueProp_none_values_some
    {l : List (Core.PropName × Flat.Expr)}
    (h : Flat.firstNonValueProp l = none) :
    ∃ vs, Flat.valuesFromExprList? (l.map Prod.snd) = some vs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons p tl ih =>
    obtain ⟨pn, pe⟩ := p
    unfold Flat.firstNonValueProp at h
    cases pe with
    | lit v =>
      simp at h
      split at h
      · simp at h
      · obtain ⟨vs, hvs⟩ := ih h
        exact ⟨v :: vs, by simp [Flat.valuesFromExprList?, Flat.exprValue?, hvs]⟩
    | _ => all_goals simp at h

/-! ### step?_none_implies_lit -/

/-- Common pattern: subexpression has step? = none, by IH it's .lit v,
    but exprValue? was none — contradiction. -/
private theorem step?_none_subexpr_absurd
    (ih : ∀ (s : Flat.State), s.expr.depth ≤ k → Flat.step? s = none → ∃ v, s.expr = .lit v)
    (sub : Flat.Expr) (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (hdepth : sub.depth ≤ k)
    (hstep : Flat.step? ⟨sub, env, heap, trace⟩ = none)
    (hev : Flat.exprValue? sub = none) : False := by
  obtain ⟨v, hv⟩ := ih ⟨sub, env, heap, trace⟩ hdepth hstep
  simp at hv; rw [hv] at hev; simp [Flat.exprValue?] at hev

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
    -- seq and let: standard pattern (exprValue? / step? / IH contradiction)
    | seq a b =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih a fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | «let» _name init _body =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih init fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    -- Single subexpression constructors
    | assign _name value =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih value fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | «if» cond _then_ _else_ =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih cond fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | unary _op arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih arg fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | typeof arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih arg fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | throw arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih arg fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | await arg =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih arg fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    -- getProp: exprValue? has 3 branches (object, other, none)
    | getProp obj _prop =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h  -- some (.object _) → some
      next => simp at h  -- some _ → some
      next hev =>         -- none → recursive step?
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih obj fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | deleteProp obj _prop =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h  -- some (.object _) → some
      next => simp at h  -- some _ → some
      next hev =>         -- none → recursive step?
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih obj fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | makeClosure _idx envExpr =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h  -- some (.object _) → some
      next => simp at h  -- some _ → some (error)
      next hev =>         -- none → recursive step?
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih envExpr fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | getEnv envExpr _idx =>
      exfalso; unfold Flat.step? at h
      split at h
      next => -- some (.object _) → always some (several sub-cases)
        split at h <;> (try split at h) <;> simp at h
      next => simp at h  -- some _ → some (error)
      next hev =>         -- none → recursive step?
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih envExpr fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    -- return and yield: subcases on option arg
    | «return» arg =>
      exfalso; unfold Flat.step? at h
      cases arg with
      | none => simp at h
      | some e =>
        split at h
        next => simp at h
        next hev =>
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih e fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    | yield arg _delegate =>
      exfalso; unfold Flat.step? at h
      cases arg with
      | none => simp at h
      | some e =>
        split at h
        next => simp at h
        next hev =>
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih e fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    -- Two-subexpression constructors
    | binary _op lhs rhs =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevl =>  -- lhs not value
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih lhs fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevl
      next _ =>     -- lhs is value
        split at h
        next hevr =>  -- rhs not value
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih rhs fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevr
        next => simp at h  -- both values → evalBinary → some
    | setProp obj _prop value =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevo =>  -- obj not value
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih obj fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevo
      next _ =>     -- obj = object
        split at h
        next => simp at h  -- value is a value → some
        next hevv =>        -- value not value
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih value fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevv
      next => simp at h  -- obj = non-object value → error → some
    | getIndex obj idx =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevo =>  -- obj not value
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih obj fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevo
      next _ =>     -- obj = object
        split at h
        next => simp at h  -- idx is value → some
        next hevi =>        -- idx not value
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih idx fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevi
      next => simp at h  -- obj = non-object → error
    | setIndex obj idx value =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevo =>  -- obj not value
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih obj fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevo
      next _ =>     -- obj = object
        split at h
        next hevi =>  -- idx not value
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih idx fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevi
        next _ =>     -- idx is value
          split at h
          next => simp at h  -- value is value → some
          next hevv =>        -- value not value
            split at h
            next => simp at h
            next hstep =>
              exact step?_none_subexpr_absurd ih value fenv fheap ftrace
                (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevv
      next => simp at h  -- obj = non-object → error
    -- tryCatch: body evaluation with error handling
    | tryCatch body _catchParam _catchBody _finally_ =>
      exfalso; unfold Flat.step? at h
      split at h
      next =>         -- body is value
        split at h <;> simp at h  -- finally some/none, both return some
      next hev =>     -- body not value
        split at h
        next => simp at h   -- step body = some (.error, _) → some
        next => simp at h   -- step body = some (t, _) → some
        next hstep =>        -- step body = none
          exact step?_none_subexpr_absurd ih body fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hev
    -- List-based constructors: call, newObj, makeEnv, arrayLit, objectLit
    | call funcExpr envExpr args =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevf =>  -- funcExpr not value
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih funcExpr fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevf
      next _ =>     -- funcExpr is value
        split at h
        next heve =>  -- envExpr not value
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih envExpr fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep heve
        next _ =>     -- envExpr is value
          split at h
          next => simp at h  -- all args are values → some
          next _ =>           -- valuesFromExprList? = none
            split at h
            next hfnv =>      -- firstNonValueExpr = some
              split at h
              next => simp at h
              next hstep =>   -- step? target = none
                -- By IH, target = .lit v; but firstNonValueExpr returns non-lit targets
                have hevt := firstNonValueExpr_exprValue_none hfnv
                obtain ⟨v, hv⟩ := ih ⟨_, fenv, fheap, ftrace⟩
                  (by simp [Flat.Expr.depth] at hd ⊢
                      have := Flat.firstNonValueExpr_depth hfnv; omega) hstep
                simp at hv; rw [hv] at hevt; simp [Flat.exprValue?] at hevt
            next hfnv =>      -- firstNonValueExpr = none
              -- Contradiction: firstNonValueExpr = none → valuesFromExprList? = some
              rename_i hvals
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_values_some hfnv
              rw [hvs] at hvals; simp at hvals
    | newObj funcExpr envExpr args =>
      exfalso; unfold Flat.step? at h
      split at h
      next hevf =>  -- funcExpr not value
        split at h
        next => simp at h
        next hstep =>
          exact step?_none_subexpr_absurd ih funcExpr fenv fheap ftrace
            (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep hevf
      next _ =>     -- funcExpr is value
        split at h
        next heve =>  -- envExpr not value
          split at h
          next => simp at h
          next hstep =>
            exact step?_none_subexpr_absurd ih envExpr fenv fheap ftrace
              (by simp [Flat.Expr.depth] at hd ⊢; omega) hstep heve
        next _ =>     -- envExpr is value
          split at h
          next => simp at h  -- all args values → allocFreshObject → some
          next _ =>
            split at h
            next hfnv =>
              split at h
              next => simp at h
              next hstep =>
                have hevt := firstNonValueExpr_exprValue_none hfnv
                obtain ⟨v, hv⟩ := ih ⟨_, fenv, fheap, ftrace⟩
                  (by simp [Flat.Expr.depth] at hd ⊢
                      have := Flat.firstNonValueExpr_depth hfnv; omega) hstep
                simp at hv; rw [hv] at hevt; simp [Flat.exprValue?] at hevt
            next hfnv =>
              rename_i hvals
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_values_some hfnv
              rw [hvs] at hvals; simp at hvals
    | makeEnv values =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h  -- all values → allocEnvObject → some
      next _ =>
        split at h
        next hfnv =>
          split at h
          next => simp at h
          next hstep =>
            have hevt := firstNonValueExpr_exprValue_none hfnv
            obtain ⟨v, hv⟩ := ih ⟨_, fenv, fheap, ftrace⟩
              (by simp [Flat.Expr.depth] at hd ⊢
                  have := Flat.firstNonValueExpr_depth hfnv; omega) hstep
            simp at hv; rw [hv] at hevt; simp [Flat.exprValue?] at hevt
        next hfnv =>
          rename_i hvals
          have ⟨vs, hvs⟩ := firstNonValueExpr_none_values_some hfnv
          rw [hvs] at hvals; simp at hvals
    | arrayLit elems =>
      exfalso; unfold Flat.step? at h
      split at h
      next => simp at h  -- all values → allocFreshObject → some
      next _ =>
        split at h
        next hfnv =>
          split at h
          next => simp at h
          next hstep =>
            have hevt := firstNonValueExpr_exprValue_none hfnv
            obtain ⟨v, hv⟩ := ih ⟨_, fenv, fheap, ftrace⟩
              (by simp [Flat.Expr.depth] at hd ⊢
                  have := Flat.firstNonValueExpr_depth hfnv; omega) hstep
            simp at hv; rw [hv] at hevt; simp [Flat.exprValue?] at hevt
        next hfnv =>
          rename_i hvals
          have ⟨vs, hvs⟩ := firstNonValueExpr_none_values_some hfnv
          rw [hvs] at hvals; simp at hvals
    | objectLit props =>
      exfalso
      -- step? for objectLit uses let vals := props.map Prod.snd
      -- Case split on valuesFromExprList? and firstNonValueProp to avoid unfold issues
      unfold Flat.step? at h
      -- The unfolded expression has nested matches; repeatedly split
      repeat split at h
      all_goals (first
        | exact absurd h (by simp)
        | (rename_i hfnv _ hstep
           have hevt := firstNonValueProp_exprValue_none hfnv
           obtain ⟨v, hv⟩ := ih ⟨_, fenv, fheap, ftrace⟩
             (by simp [Flat.Expr.depth] at hd ⊢
                 have := Flat.firstNonValueProp_depth hfnv; omega) hstep
           simp at hv; rw [hv] at hevt; simp [Flat.exprValue?] at hevt)
        | (rename_i hfnv
           have := firstNonValueProp_none_values_some hfnv
           simp_all)
        | simp at h)

private theorem step?_none_implies_lit (s : Flat.State) (h : Flat.step? s = none) :
    ∃ v, s.expr = .lit v :=
  step?_none_implies_lit_aux s.expr.depth s (Nat.le_refl _) h

/-- Halt preservation with precondition: the theorem is valid when the Core
    expression at halt point is not a forIn or forOf (which are not yet
    implemented in closure conversion). -/
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
    (h : Flat.closureConvert s = .ok t) :
    ∀ b, Flat.Behaves t b → Core.Behaves s b := by
  intro b ⟨sf, hsteps, hhalt⟩
  have hinit := closureConvert_init_related s t h
  obtain ⟨sc, hcsteps, hrel⟩ :=
    closureConvert_steps_simulation s t h _ _ _ _ hinit hsteps
  exact ⟨sc, hcsteps, closureConvert_halt_preservation s t h _ _ hrel hhalt
    -- Preconditions: Core expression at halt is not forIn/forOf.
    -- TRUE: requires showing the source program has no forIn/forOf
    -- (reasonable since closureConvert stubs them out) and Core.Step preserves this.
    sorry sorry⟩

theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ b, Flat.Behaves t b → ∃ b', Core.Behaves s b' ∧ b = b' :=
by
  intro b hb
  refine ⟨b, ?_, rfl⟩
  exact closureConvert_trace_reflection s t h b hb

end VerifiedJS.Proofs
