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

/-- bindComplex always produces .let, never .trivial. -/
private theorem bindComplex_not_trivial (rhs : ANF.ComplexExpr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (t : ANF.Trivial) :
    (ANF.bindComplex rhs k).run n ≠ .ok (.trivial t, m) := by
  show ANF.bindComplex rhs k n ≠ .ok (.trivial t, m)
  simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
             get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
             StateT.set, pure, Pure.pure, StateT.pure, Except.pure, getThe, MonadStateOf.get]
  cases hk : k (.var (toString "_anf" ++ toString (Nat.repr n))) (n + 1) with
  | error => simp [hk]
  | ok v => intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1

/-- normalizeExpr never produces .trivial when the continuation k never produces .trivial.
    Combined with normalizeExprList and normalizeProps by strong induction on depth. -/
private theorem normalizeExpr_not_trivial_family :
    ∀ (d : Nat),
      (∀ (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr),
        (∀ x n' m' t, (k x) n' ≠ .ok (.trivial t, m')) →
        e.depth ≤ d → ∀ n m t, (ANF.normalizeExpr e k) n ≠ .ok (.trivial t, m)) ∧
      (∀ (es : List Flat.Expr) (k : List ANF.Trivial → ANF.ConvM ANF.Expr),
        (∀ xs n' m' t, (k xs) n' ≠ .ok (.trivial t, m')) →
        Flat.Expr.listDepth es ≤ d → ∀ n m t, (ANF.normalizeExprList es k) n ≠ .ok (.trivial t, m)) ∧
      (∀ (ps : List (Flat.PropName × Flat.Expr)) (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr),
        (∀ xs n' m' t, (k xs) n' ≠ .ok (.trivial t, m')) →
        Flat.Expr.propListDepth ps ≤ d → ∀ n m t, (ANF.normalizeProps ps k) n ≠ .ok (.trivial t, m))
    := by
  intro d
  induction d with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e k hk hd n m t
      cases e with
      | lit v =>
        simp only [ANF.normalizeExpr]
        cases ANF.trivialOfFlatValue v with
        | ok tv => exact hk tv n m t
        | error _ => intro h; simp [Except.bind] at h
      | var name => simp only [ANF.normalizeExpr]; exact hk (.var name) n m t
      | this => simp only [ANF.normalizeExpr]; exact hk (.var "this") n m t
      | «break» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
      | «continue» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
      | «return» arg =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
        | some _ => exfalso; simp [Flat.Expr.depth] at hd
      | yield arg _ =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
        | some _ => exfalso; simp [Flat.Expr.depth] at hd
      | _ => exfalso; simp [Flat.Expr.depth] at hd
    · intro es k hk hd n m t
      cases es with
      | nil => simp only [ANF.normalizeExprList]; exact hk [] n m t
      | cons e rest => exfalso; simp [Flat.Expr.listDepth] at hd
    · intro ps k hk hd n m t
      cases ps with
      | nil => simp only [ANF.normalizeProps]; exact hk [] n m t
      | cons p rest => exfalso; simp [Flat.Expr.propListDepth] at hd
  | succ d ih =>
    obtain ⟨ihe, ihes, ihps⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- normalizeExpr
    · intro e k hk hd n m t
      cases e with
      | lit v =>
        simp only [ANF.normalizeExpr]
        cases ANF.trivialOfFlatValue v with
        | ok tv => exact hk tv n m t
        | error _ => intro h; simp [Except.bind] at h
      | var name => simp only [ANF.normalizeExpr]; exact hk (.var name) n m t
      | this => simp only [ANF.normalizeExpr]; exact hk (.var "this") n m t
      | «break» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
      | «continue» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
      | «return» arg =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
        | some value =>
          simp only [ANF.normalizeExpr]
          exact ihe value (fun t => pure (.return (some t)))
            (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
            (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | yield arg delegate =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
        | some value =>
          simp only [ANF.normalizeExpr]
          exact ihe value (fun t => pure (.yield (some t) delegate))
            (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
            (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | throw arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun t => pure (.throw t))
          (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | await arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun t => pure (.await t))
          (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | assign name value =>
        simp only [ANF.normalizeExpr]
        exact ihe value (fun vt => ANF.bindComplex (.assign name vt) k)
          (by intro x n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | unary op arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun at_ => ANF.bindComplex (.unary op at_) k)
          (by intro x n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | typeof arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun at_ => ANF.bindComplex (.typeof at_) k)
          (by intro x n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | getProp obj prop =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.bindComplex (.getProp ot prop) k)
          (by intro x n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.bindComplex (.deleteProp ot prop) k)
          (by intro x n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr]
        exact ihe envPtr (fun et => ANF.bindComplex (.getEnv et idx) k)
          (by intro x n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr]
        exact ihe env (fun et => ANF.bindComplex (.makeClosure funcIdx et) k)
          (by intro x n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | setProp obj prop value =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setProp ot prop vt) k))
          (by intro x n' m' t'
              exact ihe value (fun vt => ANF.bindComplex (.setProp x prop vt) k)
                (by intro y n'' m'' t''; exact bindComplex_not_trivial _ k n'' m'' t'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.normalizeExpr idx (fun it => ANF.bindComplex (.getIndex ot it) k))
          (by intro x n' m' t'
              exact ihe idx (fun it => ANF.bindComplex (.getIndex x it) k)
                (by intro y n'' m'' t''; exact bindComplex_not_trivial _ k n'' m'' t'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | setIndex obj idx value =>
        simp only [ANF.normalizeExpr]
        exact ihe obj
          (fun ot => ANF.normalizeExpr idx (fun it => ANF.normalizeExpr value
            (fun vt => ANF.bindComplex (.setIndex ot it vt) k)))
          (by intro x n' m' t'
              exact ihe idx (fun it => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setIndex x it vt) k))
                (by intro y n'' m'' t''
                    exact ihe value (fun vt => ANF.bindComplex (.setIndex x y vt) k)
                      (by intro z n3 m3 t3; exact bindComplex_not_trivial _ k n3 m3 t3)
                      (by simp [Flat.Expr.depth] at hd ⊢; omega) n'' m'' t'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr]
        exact ihe lhs (fun lt => ANF.normalizeExpr rhs (fun rt => ANF.bindComplex (.binary op lt rt) k))
          (by intro x n' m' t'
              exact ihe rhs (fun rt => ANF.bindComplex (.binary op x rt) k)
                (by intro y n'' m'' t''; exact bindComplex_not_trivial _ k n'' m'' t'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | «let» name init body =>
        simp only [ANF.normalizeExpr]
        exact ihe init (fun initTriv => do
            let bodyExpr ← ANF.normalizeExpr body k
            pure (.let name (.trivial initTriv) bodyExpr))
          (by intro x n' m' t'
              simp only [bind, Bind.bind, StateT.bind, Except.bind]
              intro habs; split at habs
              · simp at habs
              · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
                exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | «if» cond then_ else_ =>
        simp only [ANF.normalizeExpr]
        exact ihe cond (fun condTriv => do
            let thenExpr ← ANF.normalizeExpr then_ k
            let elseExpr ← ANF.normalizeExpr else_ k
            pure (.if condTriv thenExpr elseExpr))
          (by intro x n' m' t'
              simp only [bind, Bind.bind, StateT.bind, Except.bind]
              intro habs
              repeat (first | split at habs | simp at habs)
              all_goals (simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs)
              all_goals (exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | seq a b =>
        simp only [ANF.normalizeExpr]
        exact ihe a (fun _ => ANF.normalizeExpr b k)
          (by intro x n' m' t'
              exact ihe b k hk (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | labeled label body =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro habs
        split at habs
        · simp at habs
        · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
      | while_ cond body =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro habs
        repeat (first | split at habs | simp at habs)
        all_goals (
          try simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
          try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
      | tryCatch body catchParam catchBody finally_ =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro habs
        -- The do block: bodyExpr ← normalizeExpr body k; catchExpr ← ...; finallyExpr ← ...; pure (.tryCatch ...)
        -- Split on each bind result
        split at habs
        · simp at habs
        · rename_i bodyRes _ _
          split at habs
          · simp at habs
          · rename_i catchRes _ _
            -- Now split on the finally_ match
            cases finally_ with
            | none =>
              simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
              exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
            | some fin =>
              simp only [Functor.map, StateT.map, bind, Bind.bind, StateT.bind, Except.bind] at habs
              split at habs
              · simp at habs
              · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
                exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
      | call funcIdx envPtr args =>
        simp only [ANF.normalizeExpr]
        exact ihe funcIdx (fun ft => ANF.normalizeExpr envPtr (fun et =>
            ANF.normalizeExprList args (fun ats => ANF.bindComplex (.call ft et ats) k)))
          (by intro x n' m' t'
              exact ihe envPtr (fun et =>
                  ANF.normalizeExprList args (fun ats => ANF.bindComplex (.call x et ats) k))
                (by intro y n'' m'' t''
                    exact ihes args (fun ats => ANF.bindComplex (.call x y ats) k)
                      (by intro xs n3 m3 t3; exact bindComplex_not_trivial _ k n3 m3 t3)
                      (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n'' m'' t'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | newObj funcIdx envPtr args =>
        simp only [ANF.normalizeExpr]
        exact ihe funcIdx (fun ft => ANF.normalizeExpr envPtr (fun et =>
            ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj ft et ats) k)))
          (by intro x n' m' t'
              exact ihe envPtr (fun et =>
                  ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj x et ats) k))
                (by intro y n'' m'' t''
                    exact ihes args (fun ats => ANF.bindComplex (.newObj x y ats) k)
                      (by intro xs n3 m3 t3; exact bindComplex_not_trivial _ k n3 m3 t3)
                      (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n'' m'' t'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m t
      | makeEnv values =>
        simp only [ANF.normalizeExpr]
        exact ihes values (fun vts => ANF.bindComplex (.makeEnv vts) k)
          (by intro xs n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n m t
      | objectLit props =>
        simp only [ANF.normalizeExpr]
        exact ihps props (fun pts => ANF.bindComplex (.objectLit pts) k)
          (by intro xs n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth, Flat.Expr.propListDepth] at hd ⊢; omega) n m t
      | arrayLit elems =>
        simp only [ANF.normalizeExpr]
        exact ihes elems (fun ets => ANF.bindComplex (.arrayLit ets) k)
          (by intro xs n' m' t'; exact bindComplex_not_trivial _ k n' m' t')
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n m t
    -- normalizeExprList
    · intro es k hk hd n m t
      cases es with
      | nil => simp only [ANF.normalizeExprList]; exact hk [] n m t
      | cons e rest =>
        simp only [ANF.normalizeExprList]
        exact ihe e (fun et => ANF.normalizeExprList rest (fun ts => k (et :: ts)))
          (by intro x n' m' t'
              exact ihes rest (fun ts => k (x :: ts))
                (by intro xs n'' m'' t''; exact hk (x :: xs) n'' m'' t'')
                (by simp [Flat.Expr.listDepth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.listDepth] at hd ⊢; omega) n m t
    -- normalizeProps
    · intro ps k hk hd n m t
      cases ps with
      | nil => simp only [ANF.normalizeProps]; exact hk [] n m t
      | cons p rest =>
        obtain ⟨pn, pe⟩ := p
        simp only [ANF.normalizeProps]
        exact ihe pe (fun pt => ANF.normalizeProps rest (fun pts => k ((pn, pt) :: pts)))
          (by intro x n' m' t'
              exact ihps rest (fun pts => k ((pn, x) :: pts))
                (by intro xs n'' m'' t''; exact hk ((pn, x) :: xs) n'' m'' t'')
                (by simp [Flat.Expr.propListDepth] at hd ⊢; omega) n' m' t')
          (by simp [Flat.Expr.propListDepth] at hd ⊢; omega) n m t

/-- Convenience wrapper: normalizeExpr never produces .trivial when k doesn't. -/
private theorem normalizeExpr_not_trivial
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ x n' m' t, (k x).run n' ≠ .ok (.trivial t, m'))
    (n m : Nat) (t : ANF.Trivial) :
    (ANF.normalizeExpr e k).run n ≠ .ok (.trivial t, m) :=
  (normalizeExpr_not_trivial_family e.depth).1 e k hk (Nat.le_refl _) n m t

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
  -- From ANF_step?_none_implies_trivial: sa.expr = .trivial t (non-var literal)
  obtain ⟨tv, hsa_expr, hnovar⟩ := ANF_step?_none_implies_trivial sa hhalt
  -- From hconv: (normalizeExpr sf.expr k).run n = .ok (sa.expr, m)
  -- Since sa.expr = .trivial tv, normalizeExpr produced .trivial tv.
  -- By normalizeExpr_not_trivial: this only happens when k produces .trivial,
  -- which means sf.expr must be one of: .lit, .var, .this, or .seq (chain of atomics)
  -- For all other constructors, normalizeExpr cannot produce .trivial → exfalso.
  rw [hsa_expr] at hconv
  cases hlit : sf.expr with
  | lit v =>
    have hsf : sf = { sf with expr := .lit v } := by cases sf; simp_all
    refine ⟨sf, [], .refl sf, ?_, rfl, ?_⟩
    · rw [hsf]; exact Flat.step?_lit_none sf v
    · exact ⟨hheap, htrace, k, n, m, hsa_expr ▸ hconv⟩
  | this =>
    -- normalizeExpr .this k = k (.var "this"). Flat.step? on .this always returns
    -- some (.silent, ...) regardless of whether "this" is bound. One silent step.
    rw [hlit] at hconv
    simp only [ANF.normalizeExpr] at hconv
    -- hconv : (k (ANF.Trivial.var "this")).run n = .ok (.trivial tv, m)
    -- Flat steps: .this → .lit v (one silent step)
    have hsf : sf = { sf with expr := .this } := by cases sf; simp_all
    cases hlk : sf.env.lookup "this" with
    | some v =>
      -- "this" found in env: step to .lit v
      have hstep : Flat.step? sf = some (.silent, Flat.pushTrace { sf with expr := .lit v } .silent) := by
        rw [hsf]; simp [Flat.step?, hlk]
      let sf' := Flat.pushTrace { sf with expr := .lit v } .silent
      refine ⟨sf', [.silent], .tail (.mk hstep) (.refl sf'), ?_, ?_, ?_⟩
      · simp [Flat.pushTrace, Flat.step?]
      · rfl
      · unfold ANF_SimRel
        simp only [Flat.pushTrace]
        refine ⟨hheap, ?_, ?_⟩
        · simp [observableTrace, htrace]
        · refine ⟨fun _ => pure (.trivial tv), n, m, ?_⟩
          simp [ANF.normalizeExpr, ANF.trivialOfFlatValue]
          cases v <;> simp [ANF.trivialOfFlatValue, pure, Pure.pure, StateT.pure, Except.pure]
    | none =>
      -- "this" not found: step to .lit .undefined (still silent)
      have hstep : Flat.step? sf = some (.silent, Flat.pushTrace { sf with expr := .lit .undefined } .silent) := by
        rw [hsf]; simp [Flat.step?, hlk]
      let sf' := Flat.pushTrace { sf with expr := .lit .undefined } .silent
      refine ⟨sf', [.silent], .tail (.mk hstep) (.refl sf'), ?_, ?_, ?_⟩
      · simp [Flat.pushTrace, Flat.step?]
      · rfl
      · unfold ANF_SimRel
        simp only [Flat.pushTrace]
        refine ⟨hheap, ?_, ?_⟩
        · simp [observableTrace, htrace]
        · refine ⟨fun _ => pure (.trivial tv), n, m, ?_⟩
          simp [ANF.normalizeExpr, ANF.trivialOfFlatValue, pure, Pure.pure, StateT.pure, Except.pure]
  | var name =>
    -- normalizeExpr (.var name) k = k (.var name). Flat.step? on .var always steps.
    rw [hlit] at hconv
    simp only [ANF.normalizeExpr] at hconv
    -- hconv : (k (ANF.Trivial.var name)).run n = .ok (.trivial tv, m)
    have hsf : sf = { sf with expr := .var name } := by cases sf; simp_all
    cases hlk : sf.env.lookup name with
    | some v =>
      -- Variable found: step to .lit v (silent)
      have hstep : Flat.step? sf = some (.silent, Flat.pushTrace { sf with expr := .lit v } .silent) := by
        rw [hsf]; exact Flat.step?_var_found sf name v hlk
      let sf' := Flat.pushTrace { sf with expr := .lit v } .silent
      refine ⟨sf', [.silent], .tail (.mk hstep) (.refl sf'), ?_, ?_, ?_⟩
      · simp [Flat.pushTrace, Flat.step?]
      · rfl
      · unfold ANF_SimRel
        simp only [Flat.pushTrace]
        refine ⟨hheap, ?_, ?_⟩
        · simp [observableTrace, htrace]
        · refine ⟨fun _ => pure (.trivial tv), n, m, ?_⟩
          simp [ANF.normalizeExpr, ANF.trivialOfFlatValue]
          cases v <;> simp [ANF.trivialOfFlatValue, pure, Pure.pure, StateT.pure, Except.pure]
    | none =>
      -- Variable not found: produces .error event (observable).
      -- Cannot prove observableTrace evs = [] in this case.
      -- Requires well-formedness precondition on environments.
      sorry
  | seq a b =>
    -- normalizeExpr (.seq a b) k = normalizeExpr a (fun _ => normalizeExpr b k)
    -- Multi-step Flat reasoning needed: evaluate seq components.
    sorry
  -- For all remaining constructors, normalizeExpr wraps k's output through
  -- bindComplex (→ .let), or ignores k entirely. The INNER continuation passed
  -- to sub-expression normalization never produces .trivial, so by
  -- normalizeExpr_not_trivial the result is never .trivial → contradiction.
  | «break» label =>
    exfalso; rw [hlit] at hconv
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure,
               Except.ok.injEq, Prod.mk.injEq] at hconv
    have : sa.expr = .break label := by cases sa; simp [hconv.1.symm]
    rw [this] at hsa_expr; exact ANF.Expr.noConfusion hsa_expr
  | «continue» label =>
    exfalso; rw [hlit] at hconv
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure,
               Except.ok.injEq, Prod.mk.injEq] at hconv
    have : sa.expr = .continue label := by cases sa; simp [hconv.1.symm]
    rw [this] at hsa_expr; exact ANF.Expr.noConfusion hsa_expr
  | «return» arg =>
    exfalso; rw [hlit] at hconv
    cases arg with
    | none =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure,
                 Except.ok.injEq, Prod.mk.injEq] at hconv
      have : sa.expr = .return none := by cases sa; simp [hconv.1.symm]
      rw [this] at hsa_expr; exact ANF.Expr.noConfusion hsa_expr
    | some value =>
      simp only [ANF.normalizeExpr] at hconv
      exact normalizeExpr_not_trivial value (fun t => pure (.return (some t)))
        (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
        n m tv hconv
  | yield arg delegate =>
    exfalso; rw [hlit] at hconv
    cases arg with
    | none =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure,
                 Except.ok.injEq, Prod.mk.injEq] at hconv
      have : sa.expr = .yield none delegate := by cases sa; simp [hconv.1.symm]
      rw [this] at hsa_expr; exact ANF.Expr.noConfusion hsa_expr
    | some value =>
      simp only [ANF.normalizeExpr] at hconv
      exact normalizeExpr_not_trivial value (fun t => pure (.yield (some t) delegate))
        (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
        n m tv hconv
  | throw arg =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial arg (fun t => pure (.throw t))
      (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
      n m tv hconv
  | await arg =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial arg (fun t => pure (.await t))
      (by intro x n' m' t' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
      n m tv hconv
  | assign name value =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial value (fun vt => ANF.bindComplex (.assign name vt) k)
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t')
      n m tv hconv
  | unary op arg =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial arg (fun at_ => ANF.bindComplex (.unary op at_) k)
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t')
      n m tv hconv
  | typeof arg =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial arg (fun at_ => ANF.bindComplex (.typeof at_) k)
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t')
      n m tv hconv
  | getProp obj prop =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial obj (fun ot => ANF.bindComplex (.getProp ot prop) k)
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t')
      n m tv hconv
  | deleteProp obj prop =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial obj (fun ot => ANF.bindComplex (.deleteProp ot prop) k)
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t')
      n m tv hconv
  | getEnv envPtr idx =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial envPtr (fun et => ANF.bindComplex (.getEnv et idx) k)
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t')
      n m tv hconv
  | makeClosure funcIdx env =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial env (fun et => ANF.bindComplex (.makeClosure funcIdx et) k)
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t')
      n m tv hconv
  | setProp obj prop value =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial obj
      (fun ot => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setProp ot prop vt) k))
      (by intro x n' m' t'
          exact normalizeExpr_not_trivial value
            (fun vt => ANF.bindComplex (.setProp x prop vt) k)
            (fun y n'' m'' t'' => bindComplex_not_trivial _ k n'' m'' t'')
            n' m' t')
      n m tv hconv
  | getIndex obj idx =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial obj
      (fun ot => ANF.normalizeExpr idx (fun it => ANF.bindComplex (.getIndex ot it) k))
      (by intro x n' m' t'
          exact normalizeExpr_not_trivial idx
            (fun it => ANF.bindComplex (.getIndex x it) k)
            (fun y n'' m'' t'' => bindComplex_not_trivial _ k n'' m'' t'')
            n' m' t')
      n m tv hconv
  | setIndex obj idx value =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial obj
      (fun ot => ANF.normalizeExpr idx (fun it => ANF.normalizeExpr value
        (fun vt => ANF.bindComplex (.setIndex ot it vt) k)))
      (by intro x n' m' t'
          exact normalizeExpr_not_trivial idx
            (fun it => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setIndex x it vt) k))
            (by intro y n'' m'' t''
                exact normalizeExpr_not_trivial value
                  (fun vt => ANF.bindComplex (.setIndex x y vt) k)
                  (fun z n3 m3 t3 => bindComplex_not_trivial _ k n3 m3 t3) n'' m'' t'')
            n' m' t')
      n m tv hconv
  | binary op lhs rhs =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial lhs
      (fun lt => ANF.normalizeExpr rhs (fun rt => ANF.bindComplex (.binary op lt rt) k))
      (by intro x n' m' t'
          exact normalizeExpr_not_trivial rhs
            (fun rt => ANF.bindComplex (.binary op x rt) k)
            (fun y n'' m'' t'' => bindComplex_not_trivial _ k n'' m'' t'')
            n' m' t')
      n m tv hconv
  | «let» name init body =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial init (fun initTriv => do
        let bodyExpr ← ANF.normalizeExpr body k
        pure (.let name (.trivial initTriv) bodyExpr))
      (by intro x n' m' t'
          simp only [bind, Bind.bind, StateT.bind, Except.bind]
          intro habs; split at habs
          · simp at habs
          · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
      n m tv hconv
  | «if» cond then_ else_ =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial cond (fun condTriv => do
        let thenExpr ← ANF.normalizeExpr then_ k
        let elseExpr ← ANF.normalizeExpr else_ k
        pure (.if condTriv thenExpr elseExpr))
      (by intro x n' m' t'
          simp only [bind, Bind.bind, StateT.bind, Except.bind]
          intro habs
          repeat (first | split at habs | simp at habs)
          all_goals (simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at habs)
          all_goals (exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1))
      n m tv hconv
  | labeled label body =>
    exfalso; rw [hlit] at hconv
    simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind] at hconv
    split at hconv
    · simp at hconv
    · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at hconv
      exact ANF.Expr.noConfusion (Prod.mk.inj hconv).1
  | while_ cond body =>
    exfalso; rw [hlit] at hconv
    simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind] at hconv
    repeat (first | split at hconv | simp at hconv)
    all_goals (
      try simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at hconv
      try exact ANF.Expr.noConfusion (Prod.mk.inj hconv).1)
  | tryCatch body catchParam catchBody finally_ =>
    exfalso; rw [hlit] at hconv
    simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind] at hconv
    split at hconv
    · simp at hconv
    · split at hconv
      · simp at hconv
      · cases finally_ with
        | none =>
          simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at hconv
          exact ANF.Expr.noConfusion (Prod.mk.inj hconv).1
        | some fin =>
          simp only [Functor.map, StateT.map, bind, Bind.bind, StateT.bind, Except.bind] at hconv
          split at hconv
          · simp at hconv
          · simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at hconv
            exact ANF.Expr.noConfusion (Prod.mk.inj hconv).1
  | call funcIdx envPtr args =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial funcIdx
      (fun ft => ANF.normalizeExpr envPtr (fun et =>
          ANF.normalizeExprList args (fun ats => ANF.bindComplex (.call ft et ats) k)))
      (by intro x n' m' t'
          exact normalizeExpr_not_trivial envPtr
            (fun et => ANF.normalizeExprList args (fun ats => ANF.bindComplex (.call x et ats) k))
            (by intro y n'' m'' t''
                exact (normalizeExpr_not_trivial_family (Flat.Expr.listDepth args)).2.1 args
                  (fun ats => ANF.bindComplex (.call x y ats) k)
                  (fun xs n3 m3 t3 => bindComplex_not_trivial _ k n3 m3 t3)
                  (Nat.le_refl _) n'' m'' t'')
            n' m' t')
      n m tv hconv
  | newObj funcIdx envPtr args =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact normalizeExpr_not_trivial funcIdx
      (fun ft => ANF.normalizeExpr envPtr (fun et =>
          ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj ft et ats) k)))
      (by intro x n' m' t'
          exact normalizeExpr_not_trivial envPtr
            (fun et => ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj x et ats) k))
            (by intro y n'' m'' t''
                exact (normalizeExpr_not_trivial_family (Flat.Expr.listDepth args)).2.1 args
                  (fun ats => ANF.bindComplex (.newObj x y ats) k)
                  (fun xs n3 m3 t3 => bindComplex_not_trivial _ k n3 m3 t3)
                  (Nat.le_refl _) n'' m'' t'')
            n' m' t')
      n m tv hconv
  | makeEnv values =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact (normalizeExpr_not_trivial_family (Flat.Expr.listDepth values)).2.1 values
      (fun vts => ANF.bindComplex (.makeEnv vts) k)
      (fun xs n' m' t' => bindComplex_not_trivial _ k n' m' t')
      (Nat.le_refl _) n m tv hconv
  | objectLit props =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact (normalizeExpr_not_trivial_family (Flat.Expr.propListDepth props)).2.2 props
      (fun pts => ANF.bindComplex (.objectLit pts) k)
      (fun xs n' m' t' => bindComplex_not_trivial _ k n' m' t')
      (Nat.le_refl _) n m tv hconv
  | arrayLit elems =>
    exfalso; rw [hlit] at hconv; simp only [ANF.normalizeExpr] at hconv
    exact (normalizeExpr_not_trivial_family (Flat.Expr.listDepth elems)).2.1 elems
      (fun ets => ANF.bindComplex (.arrayLit ets) k)
      (fun xs n' m' t' => bindComplex_not_trivial _ k n' m' t')
      (Nat.le_refl _) n m tv hconv

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
