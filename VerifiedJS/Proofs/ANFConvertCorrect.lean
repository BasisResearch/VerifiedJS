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

/-- Local copy of flatPushTrace (private in Flat.Semantics). -/
private def flatPushTrace (s : Flat.State) (t : Core.TraceEvent) : Flat.State :=
  { s with trace := s.trace ++ [t] }

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
  sa.env = sf.env ∧
  observableTrace sa.trace = observableTrace sf.trace ∧
  ∃ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat),
    (ANF.normalizeExpr sf.expr k).run n = Except.ok (sa.expr, m) ∧
    (∀ (arg : ANF.Trivial) (n' m' : Nat) (t : ANF.Trivial),
      (k arg).run n' = .ok (.trivial t, m') → t = arg)

/-- Initial states are related: both have empty traces and heaps,
    and the ANF main expression is the normalization of the Flat main. -/
private theorem anfConvert_init_related
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ANF_SimRel s t (ANF.initialState t) (Flat.initialState s) := by
  simp only [ANF.initialState, Flat.initialState]
  obtain ⟨m, hm⟩ := ANF.convert_main_from_normalizeExpr s t h
  refine ⟨rfl, rfl, rfl, fun t => pure (.trivial t), 0, m, hm, ?_⟩
  intro arg n' m' t' hk
  simp [pure, Pure.pure, StateT.pure, Except.pure] at hk
  exact (Prod.mk.inj (Except.ok.inj hk)).1

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
        | error _ => nofun
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
      | tryCatch _ _ _ fin => exfalso; cases fin <;> simp [Flat.Expr.depth] at hd
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
        | error _ => nofun
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
              · cases habs
              · simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
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
              repeat (first | split at habs | (simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)))
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
        · cases habs
        · simp [pure, Pure.pure, StateT.pure, Except.pure] at habs
      | while_ cond body =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro habs
        repeat (first | split at habs | (simp [pure, Pure.pure, StateT.pure, Except.pure] at habs) | cases habs)
      | tryCatch body catchParam catchBody finally_ =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro habs
        cases finally_ with
        | none =>
          repeat (first | split at habs | (simp [pure, Pure.pure, StateT.pure, Except.pure] at habs) | cases habs)
        | some fin =>
          simp only [Functor.map, StateT.map, bind, Bind.bind, StateT.bind, Except.bind] at habs
          repeat (first | split at habs | (simp [pure, Pure.pure, StateT.pure, Except.pure] at habs) | cases habs)
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

/-- Convenience wrapper: normalizeExprList never produces .trivial when k doesn't. -/
private theorem normalizeExprList_not_trivial
    (es : List Flat.Expr) (k : List ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ xs n' m' t, (k xs).run n' ≠ .ok (.trivial t, m'))
    (n m : Nat) (t : ANF.Trivial) :
    (ANF.normalizeExprList es k).run n ≠ .ok (.trivial t, m) :=
  (normalizeExpr_not_trivial_family (Flat.Expr.listDepth es)).2.1 es k hk (Nat.le_refl _) n m t

/-- Convenience wrapper: normalizeProps never produces .trivial when k doesn't. -/
private theorem normalizeProps_not_trivial
    (ps : List (Flat.PropName × Flat.Expr))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr)
    (hk : ∀ xs n' m' t, (k xs).run n' ≠ .ok (.trivial t, m'))
    (n m : Nat) (t : ANF.Trivial) :
    (ANF.normalizeProps ps k).run n ≠ .ok (.trivial t, m) :=
  (normalizeExpr_not_trivial_family (Flat.Expr.propListDepth ps)).2.2 ps k hk (Nat.le_refl _) n m t

/-- normalizeExpr on compound expressions (non-atom, non-seq) never produces .trivial,
    regardless of the continuation k. All compound constructors either wrap the result
    in a non-trivial constructor (let, if, labeled, etc.) or route through bindComplex
    (which always produces .let). -/
private theorem normalizeExpr_compound_not_trivial
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (h1 : ∀ v, e ≠ .lit v) (h2 : ∀ name, e ≠ .var name) (h3 : e ≠ .this)
    (h4 : ∀ a b, e ≠ .seq a b) (n m : Nat) (t : ANF.Trivial) :
    (ANF.normalizeExpr e k).run n ≠ .ok (.trivial t, m) := by
  cases e with
  | lit v => exact absurd rfl (h1 v)
  | var name => exact absurd rfl (h2 name)
  | this => exact absurd rfl h3
  | seq a b => exact absurd rfl (h4 a b)
  | «break» _ =>
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
    intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
  | «continue» _ =>
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
    intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
  | assign name value =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial value _
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | unary op arg =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial arg _
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | typeof arg =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial arg _
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | getProp obj prop =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial obj _
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | deleteProp obj prop =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial obj _
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | getEnv envPtr idx =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial envPtr _
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | makeClosure funcIdx env =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial env _
      (fun x n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | setProp obj prop value =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial obj _
      (fun x n' m' t' => normalizeExpr_not_trivial value _
        (fun y n'' m'' t'' => bindComplex_not_trivial _ k n'' m'' t'') n' m' t') n m t
  | getIndex obj idx =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial obj _
      (fun x n' m' t' => normalizeExpr_not_trivial idx _
        (fun y n'' m'' t'' => bindComplex_not_trivial _ k n'' m'' t'') n' m' t') n m t
  | binary op lhs rhs =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial lhs _
      (fun x n' m' t' => normalizeExpr_not_trivial rhs _
        (fun y n'' m'' t'' => bindComplex_not_trivial _ k n'' m'' t'') n' m' t') n m t
  | setIndex obj idx value =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial obj _
      (fun x n' m' t' => normalizeExpr_not_trivial idx _
        (fun y n'' m'' t'' => normalizeExpr_not_trivial value _
          (fun z n3 m3 t3 => bindComplex_not_trivial _ k n3 m3 t3) n'' m'' t'') n' m' t') n m t
  | call funcIdx envPtr args =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial funcIdx _
      (fun x n' m' t' => normalizeExpr_not_trivial envPtr _
        (fun y n'' m'' t'' => normalizeExprList_not_trivial args _
          (fun xs n3 m3 t3 => bindComplex_not_trivial _ k n3 m3 t3) n'' m'' t'') n' m' t') n m t
  | newObj funcIdx envPtr args =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial funcIdx _
      (fun x n' m' t' => normalizeExpr_not_trivial envPtr _
        (fun y n'' m'' t'' => normalizeExprList_not_trivial args _
          (fun xs n3 m3 t3 => bindComplex_not_trivial _ k n3 m3 t3) n'' m'' t'') n' m' t') n m t
  | makeEnv values =>
    simp only [ANF.normalizeExpr]
    exact normalizeExprList_not_trivial values _
      (fun xs n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | objectLit props =>
    simp only [ANF.normalizeExpr]
    exact normalizeProps_not_trivial props _
      (fun xs n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | arrayLit elems =>
    simp only [ANF.normalizeExpr]
    exact normalizeExprList_not_trivial elems _
      (fun xs n' m' t' => bindComplex_not_trivial _ k n' m' t') n m t
  | throw arg =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial arg _
      (by intro x n' m' t'; simp [pure, Pure.pure, StateT.pure, Except.pure]
          intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1) n m t
  | await arg =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial arg _
      (by intro x n' m' t'; simp [pure, Pure.pure, StateT.pure, Except.pure]
          intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1) n m t
  | «let» name init body =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial init _
      (by intro x n' m' t'
          intro habs; simp [StateT.bind, StateT.run, bind, Bind.bind, Except.bind] at habs
          split at habs <;> simp_all [pure, Pure.pure, StateT.pure, Except.pure]) n m t
  | «if» cond then_ else_ =>
    simp only [ANF.normalizeExpr]
    exact normalizeExpr_not_trivial cond _
      (by intro x n' m' t'
          intro habs; simp [StateT.bind, StateT.run, bind, Bind.bind, Except.bind] at habs
          repeat (first | split at habs | simp_all [pure, Pure.pure, StateT.pure, Except.pure])) n m t
  | labeled label body =>
    simp only [ANF.normalizeExpr]
    intro habs; simp [StateT.bind, StateT.run, bind, Bind.bind, Except.bind] at habs
    split at habs <;> simp_all [pure, Pure.pure, StateT.pure, Except.pure]
  | while_ cond body =>
    simp only [ANF.normalizeExpr]
    intro habs; simp [StateT.bind, StateT.run, bind, Bind.bind, Except.bind] at habs
    repeat (first | split at habs | simp_all [pure, Pure.pure, StateT.pure, Except.pure] | cases habs)
  | tryCatch body catchParam catchBody finally_ =>
    simp only [ANF.normalizeExpr]
    intro habs; simp [StateT.bind, StateT.run, bind, Bind.bind, Except.bind] at habs
    cases finally_ with
    | none =>
      repeat (first | split at habs | simp_all [pure, Pure.pure, StateT.pure, Except.pure] | cases habs)
    | some fin =>
      simp only [Functor.map, StateT.map, StateT.bind, StateT.run, bind, Bind.bind, Except.bind] at habs
      repeat (first | split at habs | simp_all [pure, Pure.pure, StateT.pure, Except.pure] | cases habs)
  | «return» arg =>
    cases arg with
    | none =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
      intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
    | some value =>
      simp only [ANF.normalizeExpr]
      exact normalizeExpr_not_trivial value _
        (by intro x n' m' t'; simp [pure, Pure.pure, StateT.pure, Except.pure]
            intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1) n m t
  | yield arg delegate =>
    cases arg with
    | none =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
      intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
    | some value =>
      simp only [ANF.normalizeExpr]
      exact normalizeExpr_not_trivial value _
        (by intro x n' m' t'; simp [pure, Pure.pure, StateT.pure, Except.pure]
            intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1) n m t

/-! ### ANF step? characterization -/

/-- Non-variable trivial always has a concrete value. -/
private theorem trivialValue?_non_var (t : ANF.Trivial)
    (h : ∀ name, t ≠ .var name) :
    ∃ v, ANF.trivialValue? t = some v := by
  cases t with
  | var name => exact absurd rfl (h name)
  | litNull => exact ⟨_, rfl⟩
  | litUndefined => exact ⟨_, rfl⟩
  | litBool b => exact ⟨_, rfl⟩
  | litNum n => exact ⟨_, rfl⟩
  | litStr s => exact ⟨_, rfl⟩
  | litObject addr => exact ⟨_, rfl⟩
  | litClosure f e => exact ⟨_, rfl⟩

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
      refine ⟨t, rfl, fun name habs => ?_⟩
      subst habs; unfold ANF.step? at h; simp at h
    | «let» _ _ _ | seq _ _ | «if» _ _ _ | while_ _ _ | labeled _ _ =>
      exfalso; simp [ANF.Expr.depth] at hd
    | tryCatch _ _ _ fin => exfalso; cases fin <;> simp [ANF.Expr.depth] at hd
    | «break» _ => unfold ANF.step? at h; simp at h
    | «continue» _ => unfold ANF.step? at h; simp at h
    | «return» arg => unfold ANF.step? at h; simp at h
    | yield arg _ => unfold ANF.step? at h; simp at h
    | «throw» _ => unfold ANF.step? at h; split at h <;> simp at h
    | «await» _ => unfold ANF.step? at h; split at h <;> simp at h
  | succ n ih =>
    intro s hd h
    cases he : s.expr with
    | trivial t =>
      refine ⟨t, rfl, fun name habs => ?_⟩
      subst habs; unfold ANF.step? at h; simp at h
    | «let» _ _ _ => unfold ANF.step? at h; simp at h
    | «break» _ => unfold ANF.step? at h; simp at h
    | «continue» _ => unfold ANF.step? at h; simp at h
    | labeled _ _ => unfold ANF.step? at h; simp at h
    | «return» arg => unfold ANF.step? at h; simp at h
    | yield arg _ => unfold ANF.step? at h; simp at h
    | «throw» _ => unfold ANF.step? at h; split at h <;> simp at h
    | «await» _ => unfold ANF.step? at h; split at h <;> simp at h
    | «if» _ _ _ => unfold ANF.step? at h; split at h <;> simp at h
    | seq a b =>
      exfalso; unfold ANF.step? at h
      split at h
      · simp at h
      · rename_i hev; split at h
        · simp at h
        · next hstep =>
          have ⟨t, hat, hnovar⟩ := ih { s with expr := a }
            (by simp [ANF.Expr.depth] at hd; omega) hstep
          obtain ⟨v, hv⟩ := trivialValue?_non_var t hnovar
          simp [hat, ANF.exprValue?, hv] at hev
        all_goals (exfalso; exact ANF.Expr.noConfusion (he.symm.trans ‹s.expr = _›))
    | while_ cond body =>
      exfalso; unfold ANF.step? at h
      split at h
      · simp at h
      · rename_i hev; split at h
        · simp at h
        · next hstep =>
          have ⟨t, hct, hnovar⟩ := ih { s with expr := cond }
            (by simp [ANF.Expr.depth] at hd; omega) hstep
          obtain ⟨v, hv⟩ := trivialValue?_non_var t hnovar
          simp [hct, ANF.exprValue?, hv] at hev
        all_goals (exfalso; exact ANF.Expr.noConfusion (he.symm.trans ‹s.expr = _›))
    | tryCatch body _ catchBody fin =>
      exfalso; unfold ANF.step? at h
      split at h
      · split at h <;> simp at h
      · rename_i hev; split at h
        · simp at h
        · simp at h
        · next hstep =>
          have ⟨t, hbt, hnovar⟩ := ih { s with expr := body }
            (by cases fin <;> simp [ANF.Expr.depth] at hd <;> omega) hstep
          obtain ⟨v, hv⟩ := trivialValue?_non_var t hnovar
          simp [hbt, ANF.exprValue?, hv] at hev
        all_goals (exfalso; exact ANF.Expr.noConfusion (he.symm.trans ‹s.expr = _›))

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
  intro sa sf ⟨hheap, henv, htrace, k, n, m, hnorm, hfaithful⟩ hstuck
  obtain ⟨t, hat, hnovar⟩ := ANF_step?_none_implies_trivial sa hstuck
  -- sa.expr = .trivial t, t is not a var
  -- From hnorm: (normalizeExpr sf.expr k).run n = .ok (.trivial t, m)
  -- Case split on sf.expr: .lit halts immediately, others need multi-step Flat reasoning
  cases hsf : sf.expr with
  | lit v =>
    -- Flat.step? on .lit = none (already halted), take sf' = sf
    exact ⟨sf, [], .refl sf,
      by rw [show sf = {sf with expr := .lit v} from by cases sf; simp_all]; unfold Flat.step?; simp,
      rfl, hheap, henv, htrace, k, n, m, hnorm, hfaithful⟩
  | var name =>
    -- normalizeExpr (.var name) k = k (.var name), producing .trivial t
    -- By faithfulness of k: t = .var name, contradicting hnovar
    exfalso
    rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
    rw [hat] at hnorm
    exact absurd (hfaithful (.var name) n m t hnorm) (hnovar name)
  | this =>
    -- normalizeExpr (.this) k = k (.var "this"), producing .trivial t
    -- By faithfulness of k: t = .var "this", contradicting hnovar
    exfalso
    rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
    rw [hat] at hnorm
    exact absurd (hfaithful (.var "this") n m t hnorm) (hnovar "this")
  | seq a b =>
    -- normalizeExpr (.seq a b) k = normalizeExpr a (fun _ => normalizeExpr b k)
    -- Can produce .trivial only when a is trivial (lit/var/this) or .seq
    rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
    rw [hat] at hnorm
    -- hnorm: (normalizeExpr a (fun _ => normalizeExpr b k)).run n = .ok (.trivial t, m)
    -- Case split on a to isolate the problematic sub-cases
    cases ha : a with
    | var name =>
      -- normalizeExpr (.var name) k' = k' (.var name) = normalizeExpr b k
      -- Flat must evaluate .var name (might error). Needs well-formedness precondition.
      sorry
    | this =>
      -- normalizeExpr (.this) k' = k' (.var "this") = normalizeExpr b k
      -- Same issue: Flat evaluates .this (might give undefined silently, but env state varies)
      sorry
    | lit v =>
      -- normalizeExpr (.lit v) k' = k' (trivialOfFlatValue v) = normalizeExpr b k
      -- Flat steps silently from .seq (.lit v) b to b. Need halt_star for b (depth induction).
      sorry
    | seq a1 a2 =>
      -- normalizeExpr (.seq a1 a2) k' recurses. Same structure, needs depth induction.
      sorry
    | _ =>
      -- All compound non-seq, non-atom a: contradiction
      -- normalizeExpr on compound a wraps result in non-.trivial constructor
      exfalso; rw [ha] at hnorm
      exact absurd hnorm (normalizeExpr_compound_not_trivial a _
        (by intro v; rw [ha]; exact Flat.Expr.noConfusion)
        (by intro nm; rw [ha]; exact Flat.Expr.noConfusion)
        (by rw [ha]; exact Flat.Expr.noConfusion)
        (by intro a' b'; rw [ha]; exact Flat.Expr.noConfusion) n m t)
  | _ =>
    -- All compound non-seq constructors: normalizeExpr wraps in non-.trivial constructor
    exfalso; rw [hat] at hnorm
    have h1 : ∀ v, sf.expr ≠ .lit v := by intro v h; rw [hsf] at h; exact Flat.Expr.noConfusion h
    have h2 : ∀ name, sf.expr ≠ .var name := by intro nm h; rw [hsf] at h; exact Flat.Expr.noConfusion h
    have h3 : sf.expr ≠ .this := by intro h; rw [hsf] at h; exact Flat.Expr.noConfusion h
    have h4 : ∀ a b, sf.expr ≠ .seq a b := by intro a b h; rw [hsf] at h; exact Flat.Expr.noConfusion h
    exact absurd hnorm (normalizeExpr_compound_not_trivial sf.expr k h1 h2 h3 h4 n m t)

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
