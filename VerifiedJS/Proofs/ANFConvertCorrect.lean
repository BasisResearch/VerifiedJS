/-
  VerifiedJS — ANF Conversion Correctness Proof
  JS.Flat → JS.ANF observable semantic preservation.

  ANF conversion names all intermediate computations, introducing extra let-bindings
  that evaluate atomically (via evalComplex). This changes the number of small-step
  transitions: one ANF step (evaluating a let-binding) may correspond to multiple
  Flat steps (evaluating subexpressions one at a time). Therefore we use:
  - Observable traces (filtering out .silent events) rather than full traces
  - A stuttering (multi-step) simulation: one ANF step ↔ one or more Flat steps
-/

import VerifiedJS.ANF.Convert
import VerifiedJS.Flat.Semantics
import VerifiedJS.ANF.Semantics

namespace VerifiedJS.Proofs

/-- Append two multi-step sequences. -/
private theorem Flat.Steps.append {s1 s2 s3 : Flat.State}
    {tr1 tr2 : List Core.TraceEvent}
    (h1 : Flat.Steps s1 tr1 s2) (h2 : Flat.Steps s2 tr2 s3) :
    Flat.Steps s1 (tr1 ++ tr2) s3 := by
  induction h1 with
  | refl => exact h2
  | tail hstep _ ih => exact .tail hstep (ih h2)

/-- Filter trace to observable (non-silent) events.
    ANF conversion preserves observable events but changes the number of
    silent (administrative) steps. -/
def observableTrace : List Core.TraceEvent → List Core.TraceEvent :=
  List.filter (· != .silent)

theorem observableTrace_nil : observableTrace [] = [] := rfl

theorem observableTrace_silent (rest : List Core.TraceEvent) :
    observableTrace (.silent :: rest) = observableTrace rest := rfl

theorem observableTrace_log (s : String) (rest : List Core.TraceEvent) :
    observableTrace (.log s :: rest) = .log s :: observableTrace rest := rfl

theorem observableTrace_error (s : String) (rest : List Core.TraceEvent) :
    observableTrace (.error s :: rest) = .error s :: observableTrace rest := rfl

theorem observableTrace_append (a b : List Core.TraceEvent) :
    observableTrace (a ++ b) = observableTrace a ++ observableTrace b := by
  simp [observableTrace, List.filter_append]

/-- Simulation relation for ANF conversion correctness.
    The relation captures:
    - Heaps are equal (both operate on the same Core.Heap)
    - Observable traces agree (ANF may have different silent steps)
    - Expression correspondence: the ANF expression is the result of normalizing
      the Flat expression under some continuation k with counter state n -/
private def ANF_SimRel (_s : Flat.Program) (_t : ANF.Program) (sa : ANF.State) (sf : Flat.State) : Prop :=
  sa.heap = sf.heap ∧
  observableTrace sa.trace = observableTrace sf.trace ∧
  ∃ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat),
    (ANF.normalizeExpr sf.expr k).run n = Except.ok (sa.expr, m)

/-- Initial states are related: both have empty traces and heaps,
    and the ANF main expression is the normalization of the Flat main. -/
private theorem anfConvert_init_related
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ANF_SimRel s t (ANF.initialState t) (Flat.initialState s) := by
  simp only [ANF.initialState, Flat.initialState]
  refine ⟨rfl, rfl, fun t => pure (.trivial t), 0, ?_⟩
  exact ANF.convert_main_from_normalizeExpr s t h

/-- Stuttering simulation: one ANF step corresponds to one or more Flat steps,
    preserving observable events and the simulation relation.
    This is the key theorem requiring detailed case analysis over expression forms. -/
private theorem anfConvert_step_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (ev : Core.TraceEvent) (sa' : ANF.State),
      ANF_SimRel s t sa sf →
      ANF.Step sa ev sa' →
      ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
        Flat.Steps sf evs sf' ∧
        observableTrace [ev] = observableTrace evs ∧
        ANF_SimRel s t sa' sf' := by
  sorry -- Requires case analysis on ANF.Step over all expression forms:
  -- For each ANF step (via evalComplex on a let-binding RHS), show the
  -- corresponding Flat execution evaluates the same subexpressions step-by-step.
  -- Key: use the normalizeExpr correspondence to construct Flat multi-steps.
  -- The continuation k changes at each step, tracking the "remaining computation".

/-! ### normalizeExpr output characterization -/

/-- normalizeExpr never produces .trivial when the continuation k never produces .trivial.
    This is the KEY lemma for proving anfConvert_halt_star: most Flat constructors
    produce ANF expressions that always step, so ANF.step? = none is impossible.

    Proof by well-founded induction matching normalizeExpr's termination measure. -/
private theorem normalizeExpr_not_trivial
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ x n' m' t, (k x).run n' ≠ .ok (.trivial t, m'))
    (n m : Nat) (t : ANF.Trivial) :
    (ANF.normalizeExpr e k).run n ≠ .ok (.trivial t, m) := by
  induction e generalizing k n m t with
  | lit v =>
    simp only [ANF.normalizeExpr]
    cases ANF.trivialOfFlatValue v with
    | ok tv => exact hk tv n m t
    | error _ => simp [StateT.run, Except.bind]
  | var name =>
    simp only [ANF.normalizeExpr]
    exact hk (.var name) n m t
  | this =>
    simp only [ANF.normalizeExpr]
    exact hk (.var "this") n m t
  | «break» label =>
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | «continue» label =>
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | «return» arg =>
    cases arg with
    | none =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
      intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
    | some value =>
      simp only [ANF.normalizeExpr]
      apply normalizeExpr_not_trivial value
      intro x n' m' t' habs
      simp only [pure, Pure.pure, StateT.pure, Except.pure] at habs
      exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | yield arg delegate =>
    cases arg with
    | none =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
      intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
    | some value =>
      simp only [ANF.normalizeExpr]
      apply normalizeExpr_not_trivial value
      intro x n' m' t' habs
      simp only [pure, Pure.pure, StateT.pure, Except.pure] at habs
      exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | throw arg =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial arg
    intro x n' m' t' habs
    simp only [pure, Pure.pure, StateT.pure, Except.pure] at habs
    exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | await arg =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial arg
    intro x n' m' t' habs
    simp only [pure, Pure.pure, StateT.pure, Except.pure] at habs
    exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | assign name value =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial value
    intro x n' m' t'
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | «let» name init body ih_init ih_body =>
    simp only [ANF.normalizeExpr]
    apply ih_init
    intro x n' m' t'
    simp only [bind, Bind.bind, StateT.bind, Except.bind]
    intro habs
    -- After normalizeExpr body k, the result is wrapped in .let
    split at habs
    · simp at habs
    · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
      exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | «if» cond then_ else_ ih_cond ih_then ih_else =>
    simp only [ANF.normalizeExpr]
    apply ih_cond
    intro x n' m' t'
    simp only [bind, Bind.bind, StateT.bind, Except.bind]
    intro habs
    split at habs <;> (try split at habs) <;>
      simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
    exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | seq a b ih_a ih_b =>
    simp only [ANF.normalizeExpr]
    apply ih_a
    intro x n' m' t'
    exact ih_b k hk n' m' t'
  | labeled label body ih_body =>
    simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
    intro habs
    split at habs
    · simp at habs
    · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
      exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | while_ cond body =>
    simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
    intro habs
    -- Result is .seq (.while_ ...) rest, never .trivial
    repeat (first | split at habs | simp at habs)
    simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
    exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | tryCatch body catchParam catchBody finally_ =>
    simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
    intro habs
    repeat (first | split at habs | simp at habs)
    all_goals (
      try simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Functor.map,
                      StateT.map] at habs
      try exact ANF.Expr.noConfusion (Prod.mk.inj habs).1)
    all_goals sorry -- tryCatch monadic unfolding
  | unary op arg =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial arg
    intro x n' m' t'
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | binary op lhs rhs =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial lhs
    intro x n' m' t'
    apply normalizeExpr_not_trivial rhs
    intro y n'' m'' t''
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | getProp obj prop =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial obj
    intro x n' m' t'
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | deleteProp obj prop =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial obj
    intro x n' m' t'
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | typeof arg =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial arg
    intro x n' m' t'
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | getEnv envPtr idx =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial envPtr
    intro x n' m' t'
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | makeClosure funcIdx env =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial env
    intro x n' m' t'
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | setProp obj prop value =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial obj
    intro x n' m' t'
    apply normalizeExpr_not_trivial value
    intro y n'' m'' t''
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | getIndex obj idx =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial obj
    intro x n' m' t'
    apply normalizeExpr_not_trivial idx
    intro y n'' m'' t''
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | setIndex obj idx value =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial obj
    intro x n' m' t'
    apply normalizeExpr_not_trivial idx
    intro y n'' m'' t''
    apply normalizeExpr_not_trivial value
    intro z n''' m''' t'''
    simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
               get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
               StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
    intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj habs).1
  | call funcIdx envPtr args =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial funcIdx
    intro x n' m' t'
    apply normalizeExpr_not_trivial envPtr
    intro y n'' m'' t''
    sorry -- normalizeExprList + bindComplex, needs mutual induction
  | newObj funcIdx envPtr args =>
    simp only [ANF.normalizeExpr]
    apply normalizeExpr_not_trivial funcIdx
    intro x n' m' t'
    apply normalizeExpr_not_trivial envPtr
    intro y n'' m'' t''
    sorry -- normalizeExprList + bindComplex, needs mutual induction
  | makeEnv values =>
    sorry -- normalizeExprList + bindComplex, needs mutual induction
  | objectLit props =>
    sorry -- normalizeProps + bindComplex, needs mutual induction
  | arrayLit elems =>
    sorry -- normalizeExprList + bindComplex, needs mutual induction
  | functionDef =>
    sorry -- functionDef case in normalizeExpr

/-! ### ANF step? characterization -/

/-- ANF.step? returns none only when the expression is a non-variable trivial literal.
    Proved by strong induction on expression depth. The recursive cases (seq, while_,
    tryCatch) are impossible because their sub-expression would need to be stuck
    (step? = none), which by IH means it's a trivial literal, but then exprValue?
    returns some, contradicting the branch condition. -/
private theorem ANF_step?_none_implies_trivial_aux :
    ∀ (n : Nat) (s : ANF.State), s.expr.depth ≤ n → ANF.step? s = none →
    ∃ t, s.expr = .trivial t ∧ ∀ name, t ≠ .var name := by
  intro n
  induction n with
  | zero =>
    intro s hd h
    cases he : s.expr with
    | trivial t =>
      cases t with
      | var name => exfalso; unfold ANF.step? at h; simp at h
      | _ => exact ⟨_, he, fun _ habs => ANF.Trivial.noConfusion habs⟩
    | «break» _ => exfalso; simp [ANF.step?] at h
    | «continue» _ => exfalso; simp [ANF.step?] at h
    | _ => exfalso; simp [ANF.Expr.depth] at hd
  | succ k ih =>
    intro s hd h
    cases he : s.expr with
    | trivial t =>
      cases t with
      | var name => exfalso; unfold ANF.step? at h; simp at h
      | _ => exact ⟨_, he, fun _ habs => ANF.Trivial.noConfusion habs⟩
    | «let» _ _ _ => exfalso; simp [ANF.step?] at h
    | «if» _ _ _ =>
      exfalso; unfold ANF.step? at h; split at h <;> simp at h
    | throw _ =>
      exfalso; unfold ANF.step? at h; split at h <;> simp at h
    | «return» arg =>
      exfalso; cases arg with
      | none => simp [ANF.step?] at h
      | some t => unfold ANF.step? at h; split at h <;> simp at h
    | yield arg delegate =>
      exfalso; cases arg with
      | none => simp [ANF.step?] at h
      | some t => unfold ANF.step? at h; split at h <;> simp at h
    | await _ =>
      exfalso; unfold ANF.step? at h; split at h <;> simp at h
    | labeled _ _ => exfalso; simp [ANF.step?] at h
    | «break» _ => exfalso; simp [ANF.step?] at h
    | «continue» _ => exfalso; simp [ANF.step?] at h
    | seq a b =>
      exfalso; unfold ANF.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨t, ht, _⟩ := ih ⟨a, s.env, s.heap, s.trace⟩
            (by simp [ANF.Expr.depth] at hd ⊢; omega) hstep
          simp at ht; rw [ht] at hev; simp [ANF.exprValue?, ANF.trivialValue?] at hev
    | while_ cond body =>
      exfalso; unfold ANF.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next hstep =>
          have ⟨t, ht, _⟩ := ih ⟨cond, s.env, s.heap, s.trace⟩
            (by simp [ANF.Expr.depth] at hd ⊢; omega) hstep
          simp at ht; rw [ht] at hev; simp [ANF.exprValue?, ANF.trivialValue?] at hev
    | tryCatch body catchParam catchBody finally_ =>
      exfalso; unfold ANF.step? at h
      split at h
      next => simp at h
      next hev =>
        split at h
        next => simp at h
        next => simp at h
        next hstep =>
          have ⟨t, ht, _⟩ := ih ⟨body, s.env, s.heap, s.trace⟩
            (by cases finally_ <;> simp [ANF.Expr.depth] at hd ⊢ <;> omega) hstep
          simp at ht; rw [ht] at hev; simp [ANF.exprValue?, ANF.trivialValue?] at hev

private theorem ANF_step?_none_implies_trivial (s : ANF.State) (h : ANF.step? s = none) :
    ∃ t, s.expr = .trivial t ∧ ∀ name, t ≠ .var name :=
  ANF_step?_none_implies_trivial_aux s.expr.depth s (Nat.le_refl _) h

/-- When ANF reaches a terminal state (step? = none), Flat can also reach a
    terminal state after zero or more silent steps.
    ANF.step? = none ↔ expr is a non-variable trivial (literal value).
    The corresponding Flat state must evaluate to a literal value. -/
private theorem anfConvert_halt_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State),
      ANF_SimRel s t sa sf →
      ANF.step? sa = none →
      ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
        Flat.Steps sf evs sf' ∧
        Flat.step? sf' = none ∧
        observableTrace evs = [] ∧
        ANF_SimRel s t sa sf' := by
  intro sa sf ⟨hheap, htrace, k, n, m, hconv⟩ hhalt
  -- ANF.step? sa = none implies sa.expr is a non-variable trivial
  -- We know (normalizeExpr sf.expr k).run n = .ok (sa.expr, m)
  -- Case analysis on sf.expr to determine what normalizeExpr produced
  -- For now, handle the key case: sf.expr = .lit v
  -- In this case, Flat.step? = none immediately, and the SimRel is maintained
  -- ANF.step? sa = none implies sa.expr is a non-variable trivial or a stuck compound.
  -- From the SimRel, we have normalizeExpr sf.expr k producing sa.expr.
  -- We need to show Flat can reach a halted state.
  -- For the .lit case (the main case), Flat already halts.
  -- For stuck compound cases (seq, while, tryCatch), these arise from
  -- stuck subexpressions in Flat.
  -- Handle the simple case: sf.expr = .lit v
  -- Case split on the Flat expression
  cases hlit : sf.expr with
  | lit v =>
    -- Flat is already halted at a literal
    have hsf : sf = { sf with expr := .lit v } := by cases sf; simp_all
    refine ⟨sf, [], .refl sf, ?_, rfl, ?_⟩
    · rw [hsf]; exact Flat.step?_lit_none sf v
    · exact ⟨hheap, htrace, k, n, m, hconv⟩
  -- For most non-lit constructors, normalizeExpr produces an ANF expression
  -- where step? always returns some, contradicting hhalt.
  -- Pattern: unfold normalizeExpr → show result always steps → exfalso
  | «break» label =>
    -- normalizeExpr (.break label) k = pure (.break label)
    -- ANF.step? on .break always returns some → contradiction
    exfalso; rw [hlit] at hconv
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure,
               Except.ok.injEq, Prod.mk.injEq] at hconv
    have hsa : sa = { sa with expr := .break label } := by cases sa; simp [hconv.1.symm]
    rw [hsa] at hhalt; simp [ANF.step?] at hhalt
  | «continue» label =>
    exfalso; rw [hlit] at hconv
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure,
               Except.ok.injEq, Prod.mk.injEq] at hconv
    have hsa : sa = { sa with expr := .continue label } := by cases sa; simp [hconv.1.symm]
    rw [hsa] at hhalt; simp [ANF.step?] at hhalt
  | _ =>
    -- Remaining non-lit cases: var, this, let, assign, if, seq, call, newObj,
    -- getProp, setProp, getIndex, setIndex, deleteProp, typeof, getEnv, makeEnv,
    -- makeClosure, objectLit, arrayLit, throw, tryCatch, while_, labeled,
    -- return, yield, await, unary, binary, functionDef
    -- Each requires showing normalizeExpr produces .let/.throw/etc that always steps,
    -- or (for var/this/seq/tryCatch) multi-step Flat reasoning.
    all_goals sorry

/-- Multi-step simulation derived from single-step stuttering simulation. -/
private theorem anfConvert_steps_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (tr : List Core.TraceEvent) (sa' : ANF.State),
      ANF_SimRel s t sa sf →
      ANF.Steps sa tr sa' →
      ∃ (sf' : Flat.State) (tr' : List Core.TraceEvent),
        Flat.Steps sf tr' sf' ∧
        observableTrace tr = observableTrace tr' ∧
        ANF_SimRel s t sa' sf' := by
  intro sa sf tr sa' hrel hsteps
  induction hsteps generalizing sf with
  | refl => exact ⟨sf, [], .refl sf, rfl, hrel⟩
  | tail hstep _ ih =>
    obtain ⟨sf2, evs1, hfsteps1, hobsev, hrel2⟩ :=
      anfConvert_step_star s t h _ _ _ _ hrel hstep
    obtain ⟨sf3, evs2, hfsteps2, hobstr, hrel3⟩ :=
      ih sf2 hrel2
    exact ⟨sf3, evs1 ++ evs2,
      Flat.Steps.append hfsteps1 hfsteps2,
      by rw [show ∀ (a : Core.TraceEvent) l, a :: l = [a] ++ l from fun _ _ => rfl,
             observableTrace_append, observableTrace_append, hobsev, hobstr],
      hrel3⟩

/-- ANF conversion preserves observable behavior:
    For every terminating ANF execution, there exists a terminating Flat
    execution with the same observable trace (non-silent events). -/
theorem anfConvert_correct (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ b, ANF.Behaves t b →
      ∃ b', Flat.Behaves s b' ∧ observableTrace b = observableTrace b' := by
  intro b ⟨sa, hsteps, hhalt⟩
  have hinit := anfConvert_init_related s t h
  -- Multi-step simulation
  obtain ⟨sf, tr', hfsteps, hobstr, hrel⟩ :=
    anfConvert_steps_star s t h _ _ _ _ hinit hsteps
  -- Halt preservation
  obtain ⟨sf', evs', hfsteps', hhalt', hobsevs, hrel'⟩ :=
    anfConvert_halt_star s t h _ _ hrel hhalt
  -- Combine: Flat reaches sf via tr', then sf' via evs' (all silent)
  exact ⟨tr' ++ evs', ⟨sf', Flat.Steps.append hfsteps hfsteps', hhalt'⟩,
    by rw [observableTrace_append, hobsevs, List.append_nil]; exact hobstr⟩

end VerifiedJS.Proofs
