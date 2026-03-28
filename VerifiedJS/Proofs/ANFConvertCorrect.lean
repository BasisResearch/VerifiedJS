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
    (∀ (arg : ANF.Trivial) (n' : Nat), ∃ (m' : Nat),
      (k arg).run n' = Except.ok (.trivial arg, m'))

/-- Initial states are related: both have empty traces and heaps,
    and the ANF main expression is the normalization of the Flat main. -/
private theorem anfConvert_init_related
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ANF_SimRel s t (ANF.initialState t) (Flat.initialState s) := by
  simp only [ANF.initialState, Flat.initialState]
  obtain ⟨m, hm⟩ := ANF.convert_main_from_normalizeExpr s t h
  refine ⟨rfl, rfl, rfl, fun t => pure (.trivial t), 0, m, hm, ?_⟩
  intro arg n'
  exact ⟨n', rfl⟩

/-- A variable name is free in a Flat expression (tracks .var in .seq chains). -/
private inductive VarFreeIn : String → Flat.Expr → Prop where
  | var (x : String) : VarFreeIn x (.var x)
  | seq_l (x : String) (a b : Flat.Expr) : VarFreeIn x a → VarFreeIn x (.seq a b)
  | seq_r (x : String) (a b : Flat.Expr) : VarFreeIn x b → VarFreeIn x (.seq a b)
  | labeled_body (x : String) (label : Core.LabelName) (body : Flat.Expr) :
      VarFreeIn x body → VarFreeIn x (.labeled label body)
  | let_init (x name : String) (init body : Flat.Expr) :
      VarFreeIn x init → VarFreeIn x (.«let» name init body)
  | let_body (x name : String) (init body : Flat.Expr) :
      VarFreeIn x body → VarFreeIn x (.«let» name init body)
  | if_cond (x : String) (c t e : Flat.Expr) : VarFreeIn x c → VarFreeIn x (.«if» c t e)
  | if_then (x : String) (c t e : Flat.Expr) : VarFreeIn x t → VarFreeIn x (.«if» c t e)
  | if_else (x : String) (c t e : Flat.Expr) : VarFreeIn x e → VarFreeIn x (.«if» c t e)
  | while_cond (x : String) (c b : Flat.Expr) : VarFreeIn x c → VarFreeIn x (.while_ c b)
  | while_body (x : String) (c b : Flat.Expr) : VarFreeIn x b → VarFreeIn x (.while_ c b)
  | throw_arg (x : String) (arg : Flat.Expr) : VarFreeIn x arg → VarFreeIn x (.throw arg)
  | tryCatch_body (x : String) (b : Flat.Expr) (cp : String) (cb : Flat.Expr) (fin : Option Flat.Expr) :
      VarFreeIn x b → VarFreeIn x (.tryCatch b cp cb fin)
  | tryCatch_catch (x : String) (b : Flat.Expr) (cp : String) (cb : Flat.Expr) (fin : Option Flat.Expr) :
      VarFreeIn x cb → VarFreeIn x (.tryCatch b cp cb fin)

/-- An expression is well-formed w.r.t. an environment if all free vars are bound. -/
def ExprWellFormed (expr : Flat.Expr) (env : Flat.Env) : Prop :=
  ∀ x, VarFreeIn x expr → env.lookup x ≠ none

private theorem ANF_step?_trivial_non_var (env : ANF.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (t : ANF.Trivial) (h : ∀ name, t ≠ .var name) :
    ANF.step? ⟨.trivial t, env, heap, trace⟩ = none := by
  cases t with
  | var name => exact absurd rfl (h name)
  | _ => unfold ANF.step?; rfl

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
    Delegates to ANF.step?_none_implies_trivial_lit from Semantics.lean,
    converting isLit = true to ∀ name, t ≠ .var name. -/
private theorem ANF_step?_none_implies_trivial (s : ANF.State) (h : ANF.step? s = none) :
    ∃ t, s.expr = .trivial t ∧ ∀ name, t ≠ .var name := by
  obtain ⟨t, ht, hlit⟩ := ANF.step?_none_implies_trivial_lit s h
  exact ⟨t, ht, fun name habs => by subst habs; simp [ANF.Trivial.isLit] at hlit⟩

/-! ### Trivial chain evaluation helpers -/

/-- If `normalizeExpr e (fun _ => K)` succeeds with `.trivial`, then `K` produces the
    same result with the same state — i.e., `e` was a trivial chain that passes through
    to its ignored continuation.
    Uses strong induction on expression depth since Flat.Expr is a nested inductive. -/
private theorem normalizeExpr_ignored_bypass_trivial :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    ∀ (K : ANF.ConvM ANF.Expr) (n m : Nat) (tv : ANF.Trivial),
    (ANF.normalizeExpr e (fun _ => K)).run n = .ok (.trivial tv, m) →
    K.run n = .ok (.trivial tv, m) := by
  intro d; induction d with
  | zero =>
    intro e hd K n m tv h
    cases e with
    | lit v => simp only [ANF.normalizeExpr] at h; cases v <;> simp [ANF.trivialOfFlatValue] at h <;> exact h
    | var _ => simp only [ANF.normalizeExpr] at h; exact h
    | «this» => simp only [ANF.normalizeExpr] at h; exact h
    | seq _ _ => exfalso; simp [Flat.Expr.depth] at hd
    | _ => exfalso; exact absurd h (normalizeExpr_compound_not_trivial _ (fun _ => K)
        (by intro v hc; simp at hc) (by intro nm hc; simp at hc)
        (by intro hc; simp at hc) (by intro a' b' hc; simp at hc) n m tv)
  | succ d ih =>
    intro e hd K n m tv h
    cases e with
    | lit v => simp only [ANF.normalizeExpr] at h; cases v <;> simp [ANF.trivialOfFlatValue] at h <;> exact h
    | var _ => simp only [ANF.normalizeExpr] at h; exact h
    | «this» => simp only [ANF.normalizeExpr] at h; exact h
    | seq a b =>
      simp only [ANF.normalizeExpr] at h
      exact ih b (by simp [Flat.Expr.depth] at hd; omega) K n m tv
        (ih a (by simp [Flat.Expr.depth] at hd; omega) _ n m tv h)
    | _ => exfalso; exact absurd h (normalizeExpr_compound_not_trivial _ (fun _ => K)
        (by intro v hc; simp at hc) (by intro nm hc; simp at hc)
        (by intro hc; simp at hc) (by intro a' b' hc; simp at hc) n m tv)

/-- A trivial chain: lit, var, this, or seq of trivial chains. -/
private def isTrivialChain : Flat.Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .this => true
  | .seq a b => isTrivialChain a && isTrivialChain b
  | _ => false

/-- Cost of evaluating a trivial chain. Strictly decreases with each Flat step. -/
private def trivialChainCost : Flat.Expr → Nat
  | .lit _ => 0
  | .var _ => 1
  | .this => 1
  | .seq a b => trivialChainCost a + trivialChainCost b + 1
  | _ => 0

/-- normalizeExpr of a trivial chain passes through to the continuation unchanged. -/
private theorem normalizeExpr_trivialChain_passthrough :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d → isTrivialChain e = true →
    ∀ (K : ANF.ConvM ANF.Expr) (n : Nat),
    (ANF.normalizeExpr e (fun _ => K)).run n = K.run n := by
  intro d; induction d with
  | zero =>
    intro e hd htc K n
    cases e with
    | lit v => simp only [ANF.normalizeExpr]; cases v <;> simp [ANF.trivialOfFlatValue]
    | var _ => simp only [ANF.normalizeExpr]
    | «this» => simp only [ANF.normalizeExpr]
    | seq _ _ => exfalso; simp [Flat.Expr.depth] at hd
    | _ => simp [isTrivialChain] at htc
  | succ d ih =>
    intro e hd htc K n
    cases e with
    | lit v => simp only [ANF.normalizeExpr]; cases v <;> simp [ANF.trivialOfFlatValue]
    | var _ => simp only [ANF.normalizeExpr]
    | «this» => simp only [ANF.normalizeExpr]
    | seq a b =>
      simp [isTrivialChain] at htc
      simp only [ANF.normalizeExpr]
      rw [ih a (by simp [Flat.Expr.depth] at hd; omega) htc.1 (ANF.normalizeExpr b (fun _ => K)) n]
      exact ih b (by simp [Flat.Expr.depth] at hd; omega) htc.2 K n
    | _ => simp [isTrivialChain] at htc

/-- If normalizeExpr e (fun _ => K) produces .trivial, then e is a trivial chain. -/
private theorem normalizeExpr_trivial_implies_chain :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    ∀ (K : ANF.ConvM ANF.Expr) (n m : Nat) (tv : ANF.Trivial),
    (ANF.normalizeExpr e (fun _ => K)).run n = .ok (.trivial tv, m) →
    isTrivialChain e = true := by
  intro d; induction d with
  | zero =>
    intro e hd K n m tv h
    cases e with
    | lit _ => rfl
    | var _ => rfl
    | «this» => rfl
    | seq _ _ => exfalso; simp [Flat.Expr.depth] at hd
    | _ => exfalso; exact absurd h (normalizeExpr_compound_not_trivial _ (fun _ => K)
        (by intro v hc; simp at hc) (by intro nm hc; simp at hc)
        (by intro hc; simp at hc) (by intro a' b' hc; simp at hc) n m tv)
  | succ d ih =>
    intro e hd K n m tv h
    cases e with
    | lit _ => rfl
    | var _ => rfl
    | «this» => rfl
    | seq a b =>
      simp only [ANF.normalizeExpr] at h
      simp [isTrivialChain]
      have ha_tc := ih a (by simp [Flat.Expr.depth] at hd; omega) _ n m tv h
      constructor
      · exact ha_tc
      · rw [normalizeExpr_trivialChain_passthrough a.depth a (Nat.le_refl _) ha_tc _ n] at h
        exact ih b (by simp [Flat.Expr.depth] at hd; omega) K n m tv h
    | _ =>
      exfalso; exact absurd h (normalizeExpr_compound_not_trivial _ (fun _ => K)
        (by intro v hc; simp at hc) (by intro nm hc; simp at hc)
        (by intro hc; simp at hc) (by intro a' b' hc; simp at hc) n m tv)

/-- trivialOfFlatValue agrees with trivialOfValue. -/
private theorem trivialOfFlatValue_eq_trivialOfValue (v : Flat.Value) :
    ANF.trivialOfFlatValue v = .ok (ANF.trivialOfValue v) := by
  cases v <;> rfl

/-- Contextual stepping: if a is not a value and steps, .seq a b steps with
    the result wrapped. Returns existence with field projections. -/
private theorem step?_seq_ctx (s : Flat.State) (a b : Flat.Expr)
    (hnotval : Flat.exprValue? a = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := a } = some (t, sa)) :
    ∃ s', Flat.step? { s with expr := .seq a b } = some (t, s') ∧
      s'.expr = .seq sa.expr b ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Build left-associated seq spine: wrapSeqCtx e [a,b,c] = .seq (.seq (.seq e a) b) c -/
private def wrapSeqCtx (inner : Flat.Expr) : List Flat.Expr → Flat.Expr
  | [] => inner
  | r :: rs => wrapSeqCtx (.seq inner r) rs

/-- Lift a single Flat step through N layers of left-seq context. -/
private theorem step_wrapSeqCtx (s : Flat.State) (t : Core.TraceEvent)
    (ctx : List Flat.Expr) :
    ∀ (inner : Flat.Expr) (s_inner : Flat.State),
    Flat.exprValue? inner = none →
    Flat.step? { s with expr := inner } = some (t, s_inner) →
    s_inner.funcs = s.funcs → s_inner.callStack = s.callStack → s_inner.trace = s.trace ++ [t] →
    ∃ s', Flat.step? { s with expr := wrapSeqCtx inner ctx } = some (t, s') ∧
      s'.expr = wrapSeqCtx s_inner.expr ctx ∧
      s'.env = s_inner.env ∧ s'.heap = s_inner.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  induction ctx with
  | nil =>
    intro inner s_inner _ hstep hf hc ht
    exact ⟨s_inner, hstep, rfl, rfl, rfl, hf, hc, ht⟩
  | cons r rs ih =>
    intro inner s_inner hnotval hstep hf hc ht
    obtain ⟨s1, hstep1, hexpr1, henv1, hheap1, hfuncs1, hcs1, htrace1⟩ :=
      step?_seq_ctx s inner r hnotval t s_inner hstep
    have hnotval1 : Flat.exprValue? (Flat.Expr.seq inner r) = none := by
      simp [Flat.exprValue?]
    obtain ⟨s', hs', he', henv', hheap', hf', hc', ht'⟩ :=
      ih (Flat.Expr.seq inner r) s1 hnotval1 hstep1 hfuncs1 hcs1 htrace1
    refine ⟨s', hs', ?_, henv'.trans henv1, hheap'.trans hheap1, hf', hc', ht'⟩
    rw [he', hexpr1]; rfl

/-- Helper: step? on .seq (.lit v) r gives r (silent, preserves env/heap/funcs/callStack). -/
private theorem step?_seq_lit (sf : Flat.State) (v : Flat.Value) (r : Flat.Expr) :
    ∃ s_i, Flat.step? { sf with expr := Flat.Expr.seq (.lit v) r } = some (.silent, s_i) ∧
      s_i.expr = r ∧ s_i.env = sf.env ∧ s_i.heap = sf.heap ∧
      s_i.funcs = sf.funcs ∧ s_i.callStack = sf.callStack ∧
      s_i.trace = sf.trace ++ [Core.TraceEvent.silent] := by
  simp only [Flat.step?, Flat.exprValue?]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Helper: step? on .var name when name is bound gives .lit val (silent). -/
private theorem step?_var_bound (sf : Flat.State) (name : String) (val : Flat.Value)
    (hval : sf.env.lookup name = some val) :
    ∃ s_i, Flat.step? { sf with expr := Flat.Expr.var name } = some (.silent, s_i) ∧
      s_i.expr = .lit val ∧ s_i.env = sf.env ∧ s_i.heap = sf.heap ∧
      s_i.funcs = sf.funcs ∧ s_i.callStack = sf.callStack ∧
      s_i.trace = sf.trace ++ [Core.TraceEvent.silent] := by
  simp only [Flat.step?, hval]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Helper: step? on .this gives .lit val (silent, regardless of binding). -/
private theorem step?_this_resolve (sf : Flat.State) :
    ∃ val s_i, Flat.step? { sf with expr := Flat.Expr.this } = some (.silent, s_i) ∧
      s_i.expr = .lit val ∧ s_i.env = sf.env ∧ s_i.heap = sf.heap ∧
      s_i.funcs = sf.funcs ∧ s_i.callStack = sf.callStack ∧
      s_i.trace = sf.trace ++ [Core.TraceEvent.silent] := by
  simp only [Flat.step?]
  cases sf.env.lookup "this" with
  | some v => exact ⟨v, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | none => exact ⟨.undefined, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Consume a trivial chain inside a left-seq context via silent Flat steps.
    wrapSeqCtx tc ctx steps to wrapSeqCtx (ctx.head _) ctx.tail. -/
private theorem trivialChain_consume_ctx
    (fuel : Nat) (tc : Flat.Expr) (ctx : List Flat.Expr) (sf : Flat.State)
    (htc : isTrivialChain tc = true)
    (hcost : trivialChainCost tc ≤ fuel)
    (hctx : ctx ≠ [])
    (hsf : sf.expr = wrapSeqCtx tc ctx)
    (hwf : ∀ x, VarFreeIn x tc → sf.env.lookup x ≠ none) :
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps sf evs sf' ∧
      sf'.expr = wrapSeqCtx (ctx.head hctx) ctx.tail ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      observableTrace sf'.trace = observableTrace sf.trace ∧
      observableTrace evs = [] := by
  induction fuel generalizing tc sf ctx with
  | zero =>
    cases tc with
    | lit v =>
      -- One step: .seq (.lit v) r → r, lifted through context
      obtain ⟨r, rs, rfl⟩ : ∃ r rs, ctx = r :: rs := List.exists_cons_of_ne_nil hctx
      have hnotval : Flat.exprValue? (Flat.Expr.seq (.lit v) r) = none := by simp [Flat.exprValue?]
      obtain ⟨s_i, hstep_i, hexpr_i, henv_i, hheap_i, hfuncs_i, hcs_i, htrace_i⟩ :=
        step?_seq_lit sf v r
      obtain ⟨sf', hs', he', henv', hheap', _, _, ht'⟩ :=
        step_wrapSeqCtx sf .silent rs _ s_i hnotval hstep_i hfuncs_i hcs_i htrace_i
      have hstep_sf : Flat.step? sf = some (.silent, sf') := by
        have : sf = { sf with expr := wrapSeqCtx (Flat.Expr.seq (.lit v) r) rs } := by
          cases sf; simp_all [wrapSeqCtx]
        rw [this]; exact hs'
      refine ⟨[.silent], sf', .tail ⟨hstep_sf⟩ (.refl _), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.head_cons, List.tail_cons]; rw [he', hexpr_i]
      · exact henv'.trans henv_i
      · exact hheap'.trans hheap_i
      · rw [ht']; simp [observableTrace_append, observableTrace]; decide
      · decide
    | var _ | «this» | seq _ _ => simp [trivialChainCost] at hcost
    | _ => simp [isTrivialChain] at htc
  | succ fuel ih =>
    cases tc with
    | lit v =>
      -- Same as zero case
      obtain ⟨r, rs, rfl⟩ : ∃ r rs, ctx = r :: rs := List.exists_cons_of_ne_nil hctx
      have hnotval : Flat.exprValue? (Flat.Expr.seq (.lit v) r) = none := by simp [Flat.exprValue?]
      obtain ⟨s_i, hstep_i, hexpr_i, henv_i, hheap_i, hfuncs_i, hcs_i, htrace_i⟩ :=
        step?_seq_lit sf v r
      obtain ⟨sf', hs', he', henv', hheap', _, _, ht'⟩ :=
        step_wrapSeqCtx sf .silent rs _ s_i hnotval hstep_i hfuncs_i hcs_i htrace_i
      have hstep_sf : Flat.step? sf = some (.silent, sf') := by
        have : sf = { sf with expr := wrapSeqCtx (Flat.Expr.seq (.lit v) r) rs } := by
          cases sf; simp_all [wrapSeqCtx]
        rw [this]; exact hs'
      refine ⟨[.silent], sf', .tail ⟨hstep_sf⟩ (.refl _), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.head_cons, List.tail_cons]; rw [he', hexpr_i]
      · exact henv'.trans henv_i
      · exact hheap'.trans hheap_i
      · rw [ht']; simp [observableTrace_append, observableTrace]; decide
      · decide
    | var name =>
      -- Step 1: resolve var → .lit val
      have hbound : sf.env.lookup name ≠ none := hwf name (.var _)
      obtain ⟨val, hval⟩ : ∃ v, sf.env.lookup name = some v := by
        cases hlu : sf.env.lookup name with
        | some v => exact ⟨v, rfl⟩
        | none => exact absurd hlu hbound
      have hnotval_v : Flat.exprValue? (Flat.Expr.var name) = none := by simp [Flat.exprValue?]
      obtain ⟨s_v, hstep_v, hexpr_v, henv_v, hheap_v, hfuncs_v, hcs_v, htrace_v⟩ :=
        step?_var_bound sf name val hval
      obtain ⟨sf1, hs1, he1, henv1, hheap1, hf1, hc1, ht1⟩ :=
        step_wrapSeqCtx sf .silent ctx _ s_v hnotval_v hstep_v hfuncs_v hcs_v htrace_v
      have hstep_sf : Flat.step? sf = some (.silent, sf1) := by
        have : sf = { sf with expr := wrapSeqCtx (Flat.Expr.var name) ctx } := by
          cases sf; simp_all
        rw [this]; exact hs1
      -- sf1.expr = wrapSeqCtx (.lit val) ctx
      have hsf1 : sf1.expr = wrapSeqCtx (.lit val) ctx := by rw [he1, hexpr_v]
      -- Step 2: IH on (.lit val) with same ctx (cost 0 ≤ fuel)
      obtain ⟨evs_lit, sf', hsteps_lit, hexpr', henv', hheap', htrace', hobs'⟩ :=
        ih (.lit val) ctx sf1 rfl (Nat.zero_le _) hctx hsf1 (fun x hfx => by cases hfx)
      exact ⟨.silent :: evs_lit, sf',
        .tail ⟨hstep_sf⟩ hsteps_lit,
        hexpr',
        henv'.trans (henv1.trans henv_v),
        hheap'.trans (hheap1.trans hheap_v),
        ⟨htrace'.trans (by rw [ht1]; simp [observableTrace_append, observableTrace]; decide),
         by simp [observableTrace_silent, hobs']⟩⟩
    | «this» =>
      -- Step 1: resolve this → .lit val
      have hnotval_t : Flat.exprValue? Flat.Expr.this = none := by simp [Flat.exprValue?]
      obtain ⟨val, s_t, hstep_t, hexpr_t, henv_t, hheap_t, hfuncs_t, hcs_t, htrace_t⟩ :=
        step?_this_resolve sf
      obtain ⟨sf1, hs1, he1, henv1, hheap1, hf1, hc1, ht1⟩ :=
        step_wrapSeqCtx sf .silent ctx _ s_t hnotval_t hstep_t hfuncs_t hcs_t htrace_t
      have hstep_sf : Flat.step? sf = some (.silent, sf1) := by
        have : sf = { sf with expr := wrapSeqCtx Flat.Expr.this ctx } := by
          cases sf; simp_all
        rw [this]; exact hs1
      have hsf1 : sf1.expr = wrapSeqCtx (.lit val) ctx := by rw [he1, hexpr_t]
      obtain ⟨evs_lit, sf', hsteps_lit, hexpr', henv', hheap', htrace', hobs'⟩ :=
        ih (.lit val) ctx sf1 rfl (Nat.zero_le _) hctx hsf1 (fun x hfx => by cases hfx)
      exact ⟨.silent :: evs_lit, sf',
        .tail ⟨hstep_sf⟩ hsteps_lit,
        hexpr',
        henv'.trans (henv1.trans henv_t),
        hheap'.trans (hheap1.trans hheap_t),
        ⟨htrace'.trans (by rw [ht1]; simp [observableTrace_append, observableTrace]; decide),
         by simp [observableTrace_silent, hobs']⟩⟩
    | seq ea eb =>
      -- wrapSeqCtx (.seq ea eb) ctx = wrapSeqCtx ea (eb :: ctx)
      simp [isTrivialChain] at htc
      obtain ⟨htc_a, htc_b⟩ := htc
      have hcost_a : trivialChainCost ea ≤ fuel := by simp [trivialChainCost] at hcost; omega
      have hcost_b : trivialChainCost eb ≤ fuel := by simp [trivialChainCost] at hcost; omega
      obtain ⟨evs_a, sf_a, hsteps_a, hexpr_a, henv_a, hheap_a, htrace_a, hobs_a⟩ :=
        ih ea (eb :: ctx) sf htc_a hcost_a (List.cons_ne_nil _ _) hsf
          (fun x hfx => hwf x (.seq_l _ _ _ hfx))
      obtain ⟨evs_b, sf_b, hsteps_b, hexpr_b, henv_b, hheap_b, htrace_b, hobs_b⟩ :=
        ih eb ctx sf_a htc_b hcost_b hctx
          (by rw [hexpr_a]; simp [List.head_cons, List.tail_cons])
          (fun x hfx => by rw [henv_a]; exact hwf x (.seq_r _ _ _ hfx))
      exact ⟨evs_a ++ evs_b, sf_b,
        Flat.Steps.append hsteps_a hsteps_b,
        hexpr_b,
        henv_b.trans henv_a, hheap_b.trans hheap_a,
        htrace_b.trans htrace_a,
        by rw [observableTrace_append, hobs_a, hobs_b]; rfl⟩
    | _ => simp [isTrivialChain] at htc

/-- When normalizeExpr e k produces .trivial (.var name) with k trivial-preserving,
    and env.lookup name = some val, there exist silent Flat steps from sf to sf'
    where sf'.expr = .lit val. This is the core simulation lemma for the var case. -/
private theorem normalizeExpr_var_step_sim :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat) (name : ANF.VarName),
    (∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m')) →
    (ANF.normalizeExpr e k).run n = .ok (.trivial (.var name), m) →
    ∀ (sf : Flat.State), sf.expr = e →
    ∀ (val : Flat.Value), sf.env.lookup name = some val →
    ExprWellFormed e sf.env →
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps sf evs sf' ∧
      sf'.expr = .lit val ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      observableTrace sf'.trace = observableTrace sf.trace ∧
      observableTrace evs = [] := by
  intro d; induction d with
  | zero =>
    intro e hd k n m name hk hnorm sf hsf val hval hwf
    cases e with
    | var vname =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var vname) n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq
      obtain ⟨s_i, hstep_i, hexpr_i, henv_i, hheap_i, _, _, htrace_i⟩ :=
        step?_var_bound sf name val hval
      have hstep_sf : Flat.step? sf = some (.silent, s_i) := by
        have : sf = { sf with expr := .var name } := by cases sf; simp_all
        rw [this]; exact hstep_i
      have htobs : observableTrace s_i.trace = observableTrace sf.trace := by
        rw [htrace_i]; simp [observableTrace_append, observableTrace]; decide
      exact ⟨[.silent], s_i, .tail ⟨hstep_sf⟩ (.refl _), hexpr_i, henv_i, hheap_i, htobs, rfl⟩
    | this =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var "this") n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq
      let sf' : Flat.State := { sf with expr := .lit val, trace := sf.trace ++ [.silent] }
      have hstep_sf : Flat.step? sf = some (.silent, sf') := by
        have : sf = { sf with expr := .this } := by cases sf; simp_all
        rw [this]; simp only [Flat.step?, hval, sf']; rfl
      have htobs : observableTrace sf'.trace = observableTrace sf.trace := by
        simp [sf', observableTrace_append, observableTrace]; decide
      exact ⟨[.silent], sf', .tail ⟨hstep_sf⟩ (.refl _), rfl, rfl, rfl, htobs, rfl⟩
    | lit v =>
      exfalso
      simp only [ANF.normalizeExpr] at hnorm
      rw [trivialOfFlatValue_eq_trivialOfValue] at hnorm
      obtain ⟨m', hk'⟩ := hk (ANF.trivialOfValue v) n
      have heq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj
      exact absurd heq.symm (ANF.trivialOfValue_ne_var v name)
    | seq _ _ => exfalso; simp [Flat.Expr.depth] at hd
    | _ => exfalso; exact absurd hnorm (normalizeExpr_compound_not_trivial _ k
        (by intro v hc; exact Flat.Expr.noConfusion hc) (by intro nm hc; exact Flat.Expr.noConfusion hc)
        (by intro hc; exact Flat.Expr.noConfusion hc) (by intro a' b' hc; exact Flat.Expr.noConfusion hc) n m _)
  | succ d ih =>
    intro e hd k n m name hk hnorm sf hsf val hval hwf
    cases e with
    | var vname =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var vname) n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq
      obtain ⟨s_i, hstep_i, hexpr_i, henv_i, hheap_i, _, _, htrace_i⟩ :=
        step?_var_bound sf name val hval
      have hstep_sf : Flat.step? sf = some (.silent, s_i) := by
        have : sf = { sf with expr := .var name } := by cases sf; simp_all
        rw [this]; exact hstep_i
      have htobs : observableTrace s_i.trace = observableTrace sf.trace := by
        rw [htrace_i]; simp [observableTrace_append, observableTrace]; decide
      exact ⟨[.silent], s_i, .tail ⟨hstep_sf⟩ (.refl _), hexpr_i, henv_i, hheap_i, htobs, rfl⟩
    | this =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var "this") n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq
      let sf' : Flat.State := { sf with expr := .lit val, trace := sf.trace ++ [.silent] }
      have hstep_sf : Flat.step? sf = some (.silent, sf') := by
        have : sf = { sf with expr := .this } := by cases sf; simp_all
        rw [this]; simp only [Flat.step?, hval, sf']; rfl
      have htobs : observableTrace sf'.trace = observableTrace sf.trace := by
        simp [sf', observableTrace_append, observableTrace]; decide
      exact ⟨[.silent], sf', .tail ⟨hstep_sf⟩ (.refl _), rfl, rfl, rfl, htobs, rfl⟩
    | lit v =>
      exfalso
      simp only [ANF.normalizeExpr] at hnorm
      rw [trivialOfFlatValue_eq_trivialOfValue] at hnorm
      obtain ⟨m', hk'⟩ := hk (ANF.trivialOfValue v) n
      have heq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj
      exact absurd heq.symm (ANF.trivialOfValue_ne_var v name)
    | seq a b =>
      simp only [ANF.normalizeExpr] at hnorm
      have hda : a.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      have hdb : b.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      have htc : isTrivialChain a = true :=
        normalizeExpr_trivial_implies_chain d a hda _ n m _ hnorm
      have hb_norm : (ANF.normalizeExpr b k).run n = .ok (.trivial (.var name), m) :=
        normalizeExpr_ignored_bypass_trivial d a hda _ n m _ hnorm
      have hwf_a : ∀ x, VarFreeIn x a → sf.env.lookup x ≠ none := by
        intro x hfx; exact hwf x (.seq_l _ _ _ hfx)
      have hsf_eq : sf.expr = wrapSeqCtx a [b] := by rw [hsf]; rfl
      obtain ⟨evs_a, sf_a, hsteps_a, hexpr_a, henv_a, hheap_a, htrace_a, hobs_a⟩ :=
        trivialChain_consume_ctx (trivialChainCost a) a [b] sf htc (Nat.le_refl _)
          (List.cons_ne_nil _ _) hsf_eq hwf_a
      have hsf_a_expr : sf_a.expr = b := by
        rw [hexpr_a]; simp [List.head_cons, List.tail_cons, wrapSeqCtx]
      have hwf_b : ExprWellFormed b sf_a.env := by
        rw [henv_a]; intro x hfx; exact hwf x (.seq_r _ _ _ hfx)
      have hval_a : sf_a.env.lookup name = some val := by rw [henv_a]; exact hval
      obtain ⟨evs_b, sf', hsteps_b, hexpr', henv', hheap', htobs', hobs'⟩ :=
        ih b hdb k n m name hk hb_norm sf_a hsf_a_expr val hval_a hwf_b
      exact ⟨evs_a ++ evs_b, sf',
        Flat.Steps.append hsteps_a hsteps_b,
        hexpr',
        henv'.trans henv_a, hheap'.trans hheap_a,
        htobs'.trans htrace_a,
        by rw [observableTrace_append, hobs_a, hobs']; rfl⟩
    | _ => exfalso; exact absurd hnorm (normalizeExpr_compound_not_trivial _ k
        (by intro v hc; exact Flat.Expr.noConfusion hc) (by intro nm hc; exact Flat.Expr.noConfusion hc)
        (by intro hc; exact Flat.Expr.noConfusion hc) (by intro a' b' hc; exact Flat.Expr.noConfusion hc) n m _)

/-- When normalizeExpr sf.expr k produces .labeled label body, there exist Flat steps
    from sf to sf' such that normalizeExpr sf'.expr k' produces body (with k' trivial-preserving).
    The .labeled may be embedded inside .seq chains or compound expression prefixes;
    the Flat machine steps through these to reach the underlying .labeled statement. -/
private theorem normalizeExpr_labeled_step_sim
    (e : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (label : String) (body : ANF.Expr)
    (hk : ∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (ANF.Expr.labeled label body, m))
    (sf : Flat.State) (hsf : sf.expr = e)
    (hwf : ExprWellFormed e sf.env) :
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps sf evs sf' ∧
      (∃ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n' m' : Nat),
        (ANF.normalizeExpr sf'.expr k').run n' = .ok (body, m') ∧
        (∀ (arg : ANF.Trivial) (n'' : Nat), ∃ m'', (k' arg).run n'' = .ok (.trivial arg, m''))) ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      observableTrace sf'.trace = observableTrace sf.trace ∧
      observableTrace evs = [] ∧
      ExprWellFormed sf'.expr sf'.env := by
  cases e with
  | labeled label' body_flat =>
    -- normalizeExpr (.labeled label' body_flat) k = do { bodyExpr ← normalizeExpr body_flat k; pure (.labeled label' bodyExpr) }
    simp only [ANF.normalizeExpr] at hnorm
    simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind] at hnorm
    cases hres : ANF.normalizeExpr body_flat k n with
    | ok val =>
      simp [hres, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
      obtain ⟨⟨hlabel, hbody⟩, hm⟩ := hnorm
      subst hlabel
      obtain ⟨body_expr, m'⟩ := val; simp at hbody hm; subst hbody; subst hm
      -- One Flat step: .labeled label' body_flat → body_flat
      obtain ⟨sf', hstep, hexpr, henv', hheap', htrace'⟩ : ∃ sf',
          Flat.step? sf = some (.silent, sf') ∧ sf'.expr = body_flat ∧
          sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
          sf'.trace = sf.trace ++ [Core.TraceEvent.silent] := by
        have hsf_eq : sf = { sf with expr := Flat.Expr.labeled label' body_flat } := by
          cases sf; simp_all
        rw [hsf_eq]; unfold Flat.step?; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨[.silent], sf', .tail ⟨hstep⟩ (.refl _), ?_, henv', hheap', ?_, rfl, ?_⟩
      · rw [hexpr]; exact ⟨k, n, m', hres, hk⟩
      · rw [htrace', observableTrace_append]; simp [observableTrace]; decide
      · rw [hexpr]; intro x hfx; rw [henv']; exact hwf x (VarFreeIn.labeled_body _ _ _ hfx)
    | error msg => simp [hres] at hnorm
  | var name =>
    exfalso
    simp only [ANF.normalizeExpr] at hnorm
    obtain ⟨m', hm'⟩ := hk (.var name) n
    rw [hm'] at hnorm; exact absurd hnorm (by intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1)
  | this =>
    exfalso
    simp only [ANF.normalizeExpr] at hnorm
    obtain ⟨m', hm'⟩ := hk (.var "this") n
    rw [hm'] at hnorm; exact absurd hnorm (by intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1)
  | lit v =>
    exfalso
    simp only [ANF.normalizeExpr] at hnorm
    cases htv : ANF.trivialOfFlatValue v with
    | error msg =>
      simp [htv] at hnorm
      exact absurd hnorm (by simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map])
    | ok triv =>
      simp [htv] at hnorm
      obtain ⟨m', hm'⟩ := hk triv n
      rw [hm'] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  | «break» l =>
    exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  | «continue» l =>
    exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  | «return» arg =>
    cases arg with
    | none =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
    | some _ => sorry -- return (some v) wrapping .labeled in sub-expression
  | yield arg delegate =>
    cases arg with
    | none =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
    | some _ => sorry -- yield (some v) wrapping .labeled
  | while_ cond body_w =>
    -- while produces .seq (.while_ ...) rest, never .labeled
    exfalso; unfold ANF.normalizeExpr at hnorm
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
    repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm))
  | tryCatch body_tc catchParam catchBody finally_ =>
    -- tryCatch always produces .tryCatch constructor, never .labeled
    exfalso; unfold ANF.normalizeExpr at hnorm
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
    cases finally_ with
    | none =>
      simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
      repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
    | some fin =>
      simp only [Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
      repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
  | _ => sorry -- remaining compound cases and seq

/-- Stuttering simulation: one ANF step corresponds to one or more Flat steps,
    preserving observable events and the simulation relation.
    This is the key theorem requiring detailed case analysis over expression forms. -/
private theorem anfConvert_step_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (ev : Core.TraceEvent) (sa' : ANF.State),
      ANF_SimRel s t sa sf →
      ExprWellFormed sf.expr sf.env →
      ANF.Step sa ev sa' →
      ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
        Flat.Steps sf evs sf' ∧
        observableTrace [ev] = observableTrace evs ∧
        ANF_SimRel s t sa' sf' ∧
        ExprWellFormed sf'.expr sf'.env := by
  intro sa sf ev sa' hrel hewf hstep
  obtain ⟨hstep_eq⟩ := hstep
  -- Decompose SimRel
  obtain ⟨hheap, henv, htrace, k, n, m, hnorm, hk_triv⟩ := hrel
  -- Case split on the ANF expression
  cases hsa : sa.expr with
  | trivial t =>
    -- step? on trivial: only .var steps, rest are none (absurd)
    cases t with
    | var name =>
      obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
      simp only [] at hsa; subst hsa
      simp only [ANF.step?, ANF.pushTrace] at hstep_eq
      cases hlookup : sa_env.lookup name <;> simp [hlookup] at hstep_eq
      case none =>
        obtain ⟨rfl, rfl⟩ := hstep_eq
        sorry -- var not-found: requires VarFreeIn inversion or .this handling
      case some val =>
        obtain ⟨rfl, rfl⟩ := hstep_eq
        have hval_sf : sf.env.lookup name = some val := by
          simp only [ANF.State.env] at henv; rw [← henv]; exact hlookup
        have hnorm_simp : (ANF.normalizeExpr sf.expr k).run n = .ok (.trivial (.var name), m) := by
          simp only [ANF.State.expr] at hnorm; exact hnorm
        obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace_obs, hobs_evs⟩ :=
          normalizeExpr_var_step_sim sf.expr.depth sf.expr (Nat.le_refl _) k n m name
            hk_triv hnorm_simp sf rfl val hval_sf hewf
        refine ⟨sf', evs, hsteps, ?_, ?_, ?_⟩
        · -- observableTrace [.silent] = observableTrace evs
          show observableTrace [.silent] = observableTrace evs
          rw [hobs_evs]; decide
        · -- ANF_SimRel
          constructor
          · -- heap: sa_heap = sf'.heap
            simp only [ANF.State.heap] at hheap; rw [hheap, ← hheap']
          constructor
          · -- env: sa_env = sf'.env
            simp only [ANF.State.env] at henv; rw [henv, ← henv']
          constructor
          · -- trace: observableTrace (sa_trace ++ [.silent]) = observableTrace sf'.trace
            simp only [ANF.State.trace] at htrace
            rw [observableTrace_append, htrace, ← htrace_obs]
            simp [observableTrace]; decide
          · -- normalizeExpr + k
            exact ⟨fun t => pure (.trivial t), 0, 0,
              by rw [hexpr']; simp [ANF.normalizeExpr, trivialOfFlatValue_eq_trivialOfValue, StateT.run, StateT.pure, pure, Pure.pure, Except.pure],
              fun arg n' => ⟨n', rfl⟩⟩
        · -- ExprWellFormed
          rw [hexpr']; intro x hfx; cases hfx
    | litNull | litUndefined | litBool _ | litNum _ | litStr _ | litObject _ | litClosure _ _ =>
      obtain ⟨_, senv, sheap, strace⟩ := sa
      simp only [] at hsa; subst hsa
      rw [ANF_step?_trivial_non_var] at hstep_eq
      · exact absurd hstep_eq (by intro h; exact nomatch h)
      · intro name; exact ANF.Trivial.noConfusion
  | «let» name rhs body =>
    sorry -- let-binding: evalComplex evaluates rhs, extends env, continues with body
  | seq a b =>
    sorry -- sequence: either a is a value (skip to b) or step inner a
  | «if» cond then_ else_ =>
    sorry -- conditional: evaluate cond trivial, branch
  | while_ cond body =>
    sorry -- while: evaluate cond, unroll or terminate
  | throw arg =>
    sorry -- throw: evaluate trivial arg, produce error event
  | tryCatch body catchParam catchBody finally_ =>
    sorry -- try-catch: step body, catch errors, handle finally
  | «return» arg =>
    sorry -- return: evaluate optional trivial arg
  | yield arg delegate =>
    sorry -- yield: evaluate optional trivial arg
  | await arg =>
    sorry -- await: evaluate trivial arg
  | labeled label body =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp [ANF.step?, ANF.pushTrace] at hstep_eq
    obtain ⟨rfl, rfl⟩ := hstep_eq
    obtain ⟨evs, sf', hsteps, ⟨k', n', m', hbody, hk'⟩, henv', hheap', htrace', hobs, hwf'⟩ :=
      normalizeExpr_labeled_step_sim sf.expr k n m label body hk_triv hnorm sf rfl hewf
    refine ⟨sf', evs, hsteps, ?_, ?_, ?_⟩
    · -- observableTrace [.silent] = observableTrace evs
      show observableTrace [Core.TraceEvent.silent] = observableTrace evs
      rw [hobs]; decide
    · -- ANF_SimRel
      refine ⟨?_, ?_, ?_, k', n', m', hbody, hk'⟩
      · -- heap
        rw [hheap, ← hheap']
      · -- env
        rw [henv, ← henv']
      · -- trace
        rw [observableTrace_append, htrace, ← htrace']
        simp [observableTrace]; decide
    · -- ExprWellFormed
      exact hwf'
  | «break» label =>
    sorry -- break: ANF produces .silent but Flat produces .error — semantic mismatch
  | «continue» label =>
    sorry -- continue: ANF produces .silent but Flat produces .error — semantic mismatch

/-- Auxiliary halt_star with strong induction on Flat expression depth.
    When ANF reaches a terminal state (step? = none), Flat can also reach a
    terminal state after zero or more silent steps.
    Requires well-formedness: all free .var references are bound in the env. -/
private theorem anfConvert_halt_star_aux
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (N : Nat) (sa : ANF.State) (sf : Flat.State),
      sf.expr.depth ≤ N →
      ANF_SimRel s t sa sf →
      ANF.step? sa = none →
      ExprWellFormed sf.expr sf.env →
      ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
        Flat.Steps sf evs sf' ∧
        Flat.step? sf' = none ∧
        observableTrace evs = [] ∧
        ANF_SimRel s t sa sf' := by
  intro N
  induction N with
  | zero =>
    intro sa sf hdepth ⟨hheap, henv, htrace, k, n, m, hnorm, hfaithful⟩ hstuck hwf
    -- Convert strengthened k-constraint to old-style injectivity for call sites below
    have hk_inj : ∀ (arg : ANF.Trivial) (n' m' : Nat) (t : ANF.Trivial),
        (k arg).run n' = .ok (.trivial t, m') → t = arg := by
      intro arg n' m' t' hk
      obtain ⟨m'', hk'⟩ := hfaithful arg n'
      have := hk.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
      exact ANF.Expr.trivial.inj this
    obtain ⟨tv, hat, hnovar⟩ := ANF_step?_none_implies_trivial sa hstuck
    cases hsf : sf.expr with
    | lit v =>
      exact ⟨sf, [], .refl sf,
        by rw [show sf = {sf with expr := .lit v} from by cases sf; simp_all]; unfold Flat.step?; simp,
        rfl, hheap, henv, htrace, k, n, m, hnorm, hfaithful⟩
    | var name =>
      exfalso
      rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
      rw [hat] at hnorm
      exact absurd (hk_inj (.var name) n m tv hnorm) (hnovar name)
    | this =>
      exfalso
      rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
      rw [hat] at hnorm
      exact absurd (hk_inj (.var "this") n m tv hnorm) (hnovar "this")
    | seq _ _ => exfalso; rw [hsf] at hdepth; simp [Flat.Expr.depth] at hdepth
    | _ =>
      -- All other constructors at depth 0: normalizeExpr produces non-trivial result
      exfalso; rw [hat] at hnorm
      have h1 : ∀ v, sf.expr ≠ .lit v := by intro v hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      have h2 : ∀ name, sf.expr ≠ .var name := by intro nm hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      have h3 : sf.expr ≠ .this := by intro hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      have h4 : ∀ a b, sf.expr ≠ .seq a b := by intro a b hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      exact absurd hnorm (normalizeExpr_compound_not_trivial sf.expr k h1 h2 h3 h4 n m tv)
  | succ N ih =>
    intro sa sf hdepth ⟨hheap, henv, htrace, k, n, m, hnorm, hfaithful⟩ hstuck hwf
    have hk_inj : ∀ (arg : ANF.Trivial) (n' m' : Nat) (t : ANF.Trivial),
        (k arg).run n' = .ok (.trivial t, m') → t = arg := by
      intro arg n' m' t' hk
      obtain ⟨m'', hk'⟩ := hfaithful arg n'
      have := hk.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
      exact ANF.Expr.trivial.inj this
    obtain ⟨tv, hat, hnovar⟩ := ANF_step?_none_implies_trivial sa hstuck
    cases hsf : sf.expr with
    | lit v =>
      exact ⟨sf, [], .refl sf,
        by rw [show sf = {sf with expr := .lit v} from by cases sf; simp_all]; unfold Flat.step?; simp,
        rfl, hheap, henv, htrace, k, n, m, hnorm, hfaithful⟩
    | var name =>
      exfalso
      rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
      rw [hat] at hnorm
      exact absurd (hk_inj (.var name) n m tv hnorm) (hnovar name)
    | this =>
      exfalso
      rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
      rw [hat] at hnorm
      exact absurd (hk_inj (.var "this") n m tv hnorm) (hnovar "this")
    | seq a b =>
      rw [hsf] at hnorm; simp only [ANF.normalizeExpr] at hnorm
      rw [hat] at hnorm
      -- hnorm: (normalizeExpr a (fun _ => normalizeExpr b k)).run n = .ok (.trivial tv, m)
      cases ha : a with
      | var name =>
        rw [ha] at hnorm; simp only [ANF.normalizeExpr] at hnorm
        have hbd : b.depth ≤ N := by rw [hsf] at hdepth; simp [Flat.Expr.depth] at hdepth; omega
        cases hvar : sf.env.lookup name with
        | some v =>
          -- Var in scope: 2 silent steps to reach b
          obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent, { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
            rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
            rw [ha]; unfold Flat.step? Flat.exprValue?
            unfold Flat.step?
            rw [hvar]; exact ⟨v, rfl⟩
          let sf2 : Flat.State := { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
          obtain ⟨sf3, hstep2⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
            simp only [sf2]; simp only [Flat.step?, Flat.exprValue?]; exact ⟨_, rfl⟩
          have hsf3_expr : sf3.expr = b := by
            have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
            exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
          have hsf3_env : sf3.env = sf.env := by
            have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
            exact congrArg Flat.State.env (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
          have hsf3_heap : sf3.heap = sf.heap := by
            have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
            exact congrArg Flat.State.heap (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
          have hsf3_trace : observableTrace sf3.trace = observableTrace sf.trace := by
            have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq
            show observableTrace (sf2.trace ++ [.silent]) = observableTrace sf.trace
            simp only [sf2]; show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
            simp [observableTrace, List.filter_append]; decide
          have hrel3 : ANF_SimRel s t sa sf3 := by
            refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
            rw [hsf3_expr, hat]; exact hnorm
          have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
          have hwf3 : ExprWellFormed sf3.expr sf3.env := by
            rw [hsf3_expr, hsf3_env]; intro x hfx
            have : VarFreeIn x (Flat.Expr.seq a b) := by rw [ha]; exact .seq_r _ _ _ hfx
            exact hwf x (by rw [hsf]; exact this)
          obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
          let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2⟩ : Flat.Step sf2 .silent sf3) hsteps')
          have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
          exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
        | none =>
          -- Var not in scope: contradicts well-formedness
          exfalso
          have hfree : VarFreeIn name (Flat.Expr.seq a b) := by rw [ha]; exact .seq_l _ _ _ (.var _)
          have : sf.env.lookup name ≠ none := hwf name (by rw [hsf]; exact hfree)
          exact this hvar
      | this =>
        rw [ha] at hnorm; simp only [ANF.normalizeExpr] at hnorm
        have hbd : b.depth ≤ N := by rw [hsf] at hdepth; simp [Flat.Expr.depth] at hdepth; omega
        -- Both cases (.this in env or not) produce .silent and .seq (.lit val) b
        obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent, { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
          rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
          rw [ha]; exact Flat.step?_seq_this_steps_to_lit sf b
        let sf2 : Flat.State := { expr := .seq (.lit val) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
        -- Step 2: .seq (.lit val) b → b
        obtain ⟨sf3, hstep2⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
          simp only [sf2]; simp only [Flat.step?, Flat.exprValue?]; exact ⟨_, rfl⟩
        have hsf3_expr : sf3.expr = b := by
          have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
          exact congrArg Flat.State.expr (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hsf3_env : sf3.env = sf.env := by
          have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
          exact congrArg Flat.State.env (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hsf3_heap : sf3.heap = sf.heap := by
          have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
          exact congrArg Flat.State.heap (Prod.mk.inj (Option.some.inj h0)).2 ▸ rfl
        have hsf3_trace : observableTrace sf3.trace = observableTrace sf.trace := by
          have h0 := hstep2; simp only [sf2, Flat.step?, Flat.exprValue?] at h0
          have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq
          show observableTrace (sf2.trace ++ [.silent]) = observableTrace sf.trace
          simp only [sf2]; show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
          simp [observableTrace, List.filter_append]; decide
        have hrel3 : ANF_SimRel s t sa sf3 := by
          refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
          rw [hsf3_expr, hat]; exact hnorm
        have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
        have hwf3 : ExprWellFormed sf3.expr sf3.env := by
          rw [hsf3_expr, hsf3_env]; intro x hfx
          have : VarFreeIn x (Flat.Expr.seq a b) := by rw [ha]; exact .seq_r _ _ _ hfx
          exact hwf x (by rw [hsf]; exact this)
        obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
        let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2⟩ : Flat.Step sf2 .silent sf3) hsteps')
        have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
        exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
      | lit v =>
        -- normalizeExpr (.lit v) k' passes through to normalizeExpr b k
        -- Flat steps silently from .seq (.lit v) b to b, then apply IH
        rw [ha] at hnorm
        simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm
        cases v <;> simp at hnorm <;> (
          have hbd : b.depth ≤ N := by rw [hsf] at hdepth; simp [Flat.Expr.depth] at hdepth; omega
          obtain ⟨sf2, hstep_eq⟩ : ∃ sf2, Flat.step? sf = some (.silent, sf2) := by
            rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
            rw [ha]; simp only [Flat.step?, Flat.exprValue?]; exact ⟨_, rfl⟩
          have hsf2_props : sf2.expr = b ∧ sf2.env = sf.env ∧ sf2.heap = sf.heap ∧ observableTrace sf2.trace = observableTrace sf.trace := by
            have h0 := hstep_eq
            rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all] at h0
            rw [ha] at h0; simp only [Flat.step?, Flat.exprValue?] at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2
            constructor; exact congrArg Flat.State.expr heq ▸ rfl
            constructor; exact congrArg Flat.State.env heq ▸ rfl
            constructor; exact congrArg Flat.State.heap heq ▸ rfl
            subst heq; show observableTrace (sf.trace ++ [.silent]) = observableTrace sf.trace
            simp [observableTrace, List.filter_append]; decide
          obtain ⟨he, henv2, hheap2, htrace2⟩ := hsf2_props
          have hrel2 : ANF_SimRel s t sa sf2 := by
            refine ⟨hheap.trans hheap2.symm, henv.trans henv2.symm, htrace.trans htrace2.symm, k, n, m, ?_, hfaithful⟩
            rw [he, hat]; exact hnorm
          have hbd2 : sf2.expr.depth ≤ N := by rw [he]; exact hbd
          have hwf2 : ExprWellFormed sf2.expr sf2.env := by
            rw [he, henv2]; intro x hfx
            have : VarFreeIn x (Flat.Expr.seq a b) := by rw [ha]; exact .seq_r _ _ _ hfx
            exact hwf x (by rw [hsf]; exact this)
          obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ :=
            ih sa sf2 hbd2 hrel2 hstuck hwf2
          exact ⟨sf', .silent :: evs,
            Flat.Steps.tail ⟨hstep_eq⟩ hsteps',
            hhalt', by show observableTrace (.silent :: evs) = []; simp [observableTrace_silent, hobs'],
            hrel'⟩)
      | seq a1 a2 =>
        -- normalizeExpr (.seq a1 a2) k' = normalizeExpr a1 (fun _ => normalizeExpr a2 k')
        -- where k' = (fun _ => normalizeExpr b k)
        rw [ha] at hnorm; simp only [ANF.normalizeExpr] at hnorm
        -- hnorm : (normalizeExpr a1 (fun _ => normalizeExpr a2 (fun _ => normalizeExpr b k))).run n = ...
        cases ha1 : a1 with
        | lit v1 =>
          -- a1 is a literal: Flat steps .seq (.seq (.lit v1) a2) b to .seq a2 b (one silent step)
          rw [ha1] at hnorm; simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm
          cases v1 <;> simp at hnorm <;> (
            have hbd : (Flat.Expr.seq a2 b).depth ≤ N := by
              have : (Flat.Expr.seq a2 b).depth = a2.depth + b.depth + 1 := by
                simp [Flat.Expr.depth]
              rw [this]
              rw [hsf] at hdepth; rw [ha, ha1] at hdepth
              simp [Flat.Expr.depth] at hdepth; omega
            obtain ⟨sf2, hstep_eq⟩ : ∃ sf2, Flat.step? sf = some (.silent, sf2) := by
              rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
              rw [ha, ha1]; unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
            have hsf2_props : sf2.expr = .seq a2 b ∧ sf2.env = sf.env ∧ sf2.heap = sf.heap ∧
                observableTrace sf2.trace = observableTrace sf.trace := by
              have h0 := hstep_eq
              rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all] at h0
              rw [ha, ha1] at h0; unfold Flat.step? Flat.exprValue? at h0
              unfold Flat.step? Flat.exprValue? at h0
              have heq := (Prod.mk.inj (Option.some.inj h0)).2
              constructor; exact congrArg Flat.State.expr heq ▸ rfl
              constructor; exact congrArg Flat.State.env heq ▸ rfl
              constructor; exact congrArg Flat.State.heap heq ▸ rfl
              subst heq; show observableTrace (sf.trace ++ [.silent]) = observableTrace sf.trace
              simp [observableTrace, List.filter_append]; decide
            obtain ⟨he, henv2, hheap2, htrace2⟩ := hsf2_props
            have hrel2 : ANF_SimRel s t sa sf2 := by
              refine ⟨hheap.trans hheap2.symm, henv.trans henv2.symm, htrace.trans htrace2.symm, k, n, m, ?_, hfaithful⟩
              rw [he]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
            have hbd2 : sf2.expr.depth ≤ N := by rw [he]; exact hbd
            have hwf2 : ExprWellFormed sf2.expr sf2.env := by
              rw [he, henv2]; intro x hfx
              apply hwf x; rw [hsf]
              cases hfx with
              | seq_l _ _ hfx' => rw [ha]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx')
              | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
            obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ :=
              ih sa sf2 hbd2 hrel2 hstuck hwf2
            exact ⟨sf', .silent :: evs,
              Flat.Steps.tail ⟨hstep_eq⟩ hsteps',
              hhalt', by show observableTrace (.silent :: evs) = []; simp [observableTrace_silent, hobs'],
              hrel'⟩)
        | var name1 =>
          -- .var in scope (by well-formedness): take 2 steps to .seq a2 b, then IH
          rw [ha1] at hnorm; simp only [ANF.normalizeExpr] at hnorm
          have hbd : (Flat.Expr.seq a2 b).depth ≤ N := by
            have : (Flat.Expr.seq a2 b).depth = a2.depth + b.depth + 1 := by
              simp [Flat.Expr.depth]
            rw [this]
            rw [hsf] at hdepth; rw [ha, ha1] at hdepth
            simp [Flat.Expr.depth] at hdepth; omega
          -- Well-formedness gives us name1 is bound in env
          have hname1_bound : sf.env.lookup name1 ≠ none := by
            apply hwf name1
            rw [hsf, ha, ha1]; exact .seq_l _ _ _ (.seq_l _ _ _ (.var _))
          obtain ⟨val, hval⟩ : ∃ v, sf.env.lookup name1 = some v := by
            cases hlu : sf.env.lookup name1 with
            | some v => exact ⟨v, rfl⟩
            | none => exact absurd hlu hname1_bound
          -- Step 1: .seq (.seq (.var name1) a2) b → .seq (.seq (.lit val) a2) b
          have hstep1 : Flat.step? sf = some (.silent,
              { expr := .seq (.seq (.lit val) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
            rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
            rw [ha, ha1]; unfold Flat.step? Flat.exprValue?
            unfold Flat.step? Flat.exprValue?
            unfold Flat.step?
            rw [hval]; rfl
          let sf2 : Flat.State := { expr := .seq (.seq (.lit val) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
          -- Step 2: .seq (.seq (.lit val) a2) b → .seq a2 b
          obtain ⟨sf3, hstep2_eq⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
            simp only [sf2]; unfold Flat.step? Flat.exprValue?
            unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
          have hsf3_props : sf3.expr = .seq a2 b ∧ sf3.env = sf.env ∧ sf3.heap = sf.heap ∧
              observableTrace sf3.trace = observableTrace sf.trace := by
            have h0 := hstep2_eq; simp only [sf2] at h0
            unfold Flat.step? Flat.exprValue? at h0
            unfold Flat.step? Flat.exprValue? at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2
            refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                    congrArg Flat.State.env heq ▸ rfl,
                    congrArg Flat.State.heap heq ▸ rfl, ?_⟩
            subst heq
            show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
            simp [observableTrace, List.filter_append]; decide
          obtain ⟨hsf3_expr, hsf3_env, hsf3_heap, hsf3_trace⟩ := hsf3_props
          have hrel3 : ANF_SimRel s t sa sf3 := by
            refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
            rw [hsf3_expr]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
          have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
          have hwf3 : ExprWellFormed sf3.expr sf3.env := by
            rw [hsf3_expr, hsf3_env]; intro x hfx
            cases hfx with
            | seq_l _ _ h' =>
              have : VarFreeIn x (Flat.Expr.seq a b) := by rw [ha]; exact .seq_l _ _ _ (.seq_r _ _ _ h')
              exact hwf x (by rw [hsf]; exact this)
            | seq_r _ _ h' =>
              exact hwf x (by rw [hsf]; exact .seq_r _ _ _ h')
          obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
          let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2_eq⟩ : Flat.Step sf2 .silent sf3) hsteps')
          have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
          exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
        | «this» =>
          -- .this always steps silently: take 2 steps to .seq a2 b, then IH
          rw [ha1] at hnorm; simp only [ANF.normalizeExpr] at hnorm
          have hbd : (Flat.Expr.seq a2 b).depth ≤ N := by
            have : (Flat.Expr.seq a2 b).depth = a2.depth + b.depth + 1 := by
              simp [Flat.Expr.depth]
            rw [this]
            rw [hsf] at hdepth; rw [ha, ha1] at hdepth
            simp [Flat.Expr.depth] at hdepth; omega
          -- Step 1: .seq (.seq .this a2) b → .seq (.seq (.lit v) a2) b
          obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent,
              { expr := .seq (.seq (.lit val) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
            rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
            rw [ha, ha1]; unfold Flat.step? Flat.exprValue?
            unfold Flat.step? Flat.exprValue?
            unfold Flat.step?
            cases sf.env.lookup "this" with
            | some v => exact ⟨v, rfl⟩
            | none => exact ⟨.undefined, rfl⟩
          let sf2 : Flat.State := { expr := .seq (.seq (.lit val) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
          -- Step 2: .seq (.seq (.lit val) a2) b → .seq a2 b
          obtain ⟨sf3, hstep2_eq⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
            simp only [sf2]; unfold Flat.step? Flat.exprValue?
            unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
          -- Extract sf3 properties from hstep2_eq by unfolding step? on sf2
          -- sf2 = { expr := .seq (.seq (.lit val) a2) b, ... }
          -- step? sf2 unfolds the outer .seq (value check fails on inner .seq),
          -- then steps the inner .seq (.lit val) a2 → a2, yielding .seq a2 b
          have hsf3_props : sf3.expr = .seq a2 b ∧ sf3.env = sf.env ∧ sf3.heap = sf.heap ∧
              observableTrace sf3.trace = observableTrace sf.trace := by
            have h0 := hstep2_eq; simp only [sf2] at h0
            unfold Flat.step? Flat.exprValue? at h0
            unfold Flat.step? Flat.exprValue? at h0
            have heq := (Prod.mk.inj (Option.some.inj h0)).2
            refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                    congrArg Flat.State.env heq ▸ rfl,
                    congrArg Flat.State.heap heq ▸ rfl, ?_⟩
            subst heq
            show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
            simp [observableTrace, List.filter_append]; decide
          obtain ⟨hsf3_expr, hsf3_env, hsf3_heap, hsf3_trace⟩ := hsf3_props
          have hrel3 : ANF_SimRel s t sa sf3 := by
            refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
            rw [hsf3_expr]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
          have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
          have hwf3 : ExprWellFormed sf3.expr sf3.env := by
            rw [hsf3_expr, hsf3_env]; intro x hfx
            cases hfx with
            | seq_l _ _ h' =>
              have : VarFreeIn x (Flat.Expr.seq a b) := by rw [ha]; exact .seq_l _ _ _ (.seq_r _ _ _ h')
              exact hwf x (by rw [hsf]; exact this)
            | seq_r _ _ h' =>
              exact hwf x (by rw [hsf]; exact .seq_r _ _ _ h')
          obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
          let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2_eq⟩ : Flat.Step sf2 .silent sf3) hsteps')
          have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
          exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
        | seq c d =>
          -- .seq(.seq(.seq c d) a2) b: case-split c to flatten the left-seq spine.
          -- Each base case (lit/var/this) takes 1-2 steps to eliminate the innermost seq,
          -- reducing depth from ≤ N+1 to ≤ N so the IH applies.
          rw [ha1] at hnorm; simp only [ANF.normalizeExpr] at hnorm
          -- hnorm : (normalizeExpr c (fun _ => normalizeExpr d (fun _ => normalizeExpr a2 (fun _ => normalizeExpr b k)))).run n = .ok (.trivial tv, m)
          cases hc : c with
          | lit v0 =>
            -- c = .lit v0: one step .seq(.seq(.seq(.lit v0) d) a2) b → .seq(.seq d a2) b
            rw [hc] at hnorm; simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm
            have hbd : (Flat.Expr.seq (Flat.Expr.seq d a2) b).depth ≤ N := by
              simp [Flat.Expr.depth]
              rw [hsf] at hdepth; rw [ha, ha1, hc] at hdepth
              simp [Flat.Expr.depth] at hdepth; omega
            cases v0 <;> simp at hnorm <;> (
              obtain ⟨sf2, hstep_eq⟩ : ∃ sf2, Flat.step? sf = some (.silent, sf2) := by
                rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
                rw [ha, ha1, hc]; unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
              have hsf2_props : sf2.expr = .seq (.seq d a2) b ∧ sf2.env = sf.env ∧ sf2.heap = sf.heap ∧
                  observableTrace sf2.trace = observableTrace sf.trace := by
                have h0 := hstep_eq
                rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all] at h0
                rw [ha, ha1, hc] at h0; unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                have heq := (Prod.mk.inj (Option.some.inj h0)).2
                refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                        congrArg Flat.State.env heq ▸ rfl,
                        congrArg Flat.State.heap heq ▸ rfl, ?_⟩
                subst heq; show observableTrace (sf.trace ++ [.silent]) = observableTrace sf.trace
                simp [observableTrace, List.filter_append]; decide
              obtain ⟨he, henv2, hheap2, htrace2⟩ := hsf2_props
              have hrel2 : ANF_SimRel s t sa sf2 := by
                refine ⟨hheap.trans hheap2.symm, henv.trans henv2.symm, htrace.trans htrace2.symm, k, n, m, ?_, hfaithful⟩
                rw [he]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
              have hbd2 : sf2.expr.depth ≤ N := by rw [he]; exact hbd
              have hwf2 : ExprWellFormed sf2.expr sf2.env := by
                rw [he, henv2]; intro x hfx
                apply hwf x; rw [hsf]
                cases hfx with
                | seq_l _ _ hfx' =>
                  rw [ha]; exact .seq_l _ _ _ (by
                    cases hfx' with
                    | seq_l _ _ hfx'' => rw [ha1, hc]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx'')
                    | seq_r _ _ hfx'' => exact .seq_r _ _ _ hfx'')
                | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
              obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ :=
                ih sa sf2 hbd2 hrel2 hstuck hwf2
              exact ⟨sf', .silent :: evs,
                Flat.Steps.tail ⟨hstep_eq⟩ hsteps',
                hhalt', by show observableTrace (.silent :: evs) = []; simp [observableTrace_silent, hobs'],
                hrel'⟩)
          | var name0 =>
            -- c = .var name0: two steps (resolve var, then eliminate seq-lit)
            rw [hc] at hnorm; simp only [ANF.normalizeExpr] at hnorm
            have hbd : (Flat.Expr.seq (Flat.Expr.seq d a2) b).depth ≤ N := by
              simp [Flat.Expr.depth]
              rw [hsf] at hdepth; rw [ha, ha1, hc] at hdepth
              simp [Flat.Expr.depth] at hdepth; omega
            -- Well-formedness gives us name0 is bound in env
            have hname0_bound : sf.env.lookup name0 ≠ none := by
              apply hwf name0
              rw [hsf, ha, ha1, hc]; exact .seq_l _ _ _ (.seq_l _ _ _ (.seq_l _ _ _ (.var _)))
            obtain ⟨val, hval⟩ : ∃ v, sf.env.lookup name0 = some v := by
              cases hlu : sf.env.lookup name0 with
              | some v => exact ⟨v, rfl⟩
              | none => exact absurd hlu hname0_bound
            -- Step 1: resolve .var name0 → .lit val inside nested seqs
            have hstep1 : Flat.step? sf = some (.silent,
                { expr := .seq (.seq (.seq (.lit val) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
              rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
              rw [ha, ha1, hc]; unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?
              unfold Flat.step?
              rw [hval]; rfl
            let sf2 : Flat.State := { expr := .seq (.seq (.seq (.lit val) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
            -- Step 2: .seq(.seq(.seq(.lit val) d) a2) b → .seq(.seq d a2) b
            obtain ⟨sf3, hstep2_eq⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
              simp only [sf2]; unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
            have hsf3_props : sf3.expr = .seq (.seq d a2) b ∧ sf3.env = sf.env ∧ sf3.heap = sf.heap ∧
                observableTrace sf3.trace = observableTrace sf.trace := by
              have h0 := hstep2_eq; simp only [sf2] at h0
              unfold Flat.step? Flat.exprValue? at h0
              unfold Flat.step? Flat.exprValue? at h0
              unfold Flat.step? Flat.exprValue? at h0
              have heq := (Prod.mk.inj (Option.some.inj h0)).2
              refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                      congrArg Flat.State.env heq ▸ rfl,
                      congrArg Flat.State.heap heq ▸ rfl, ?_⟩
              subst heq
              show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
              simp [observableTrace, List.filter_append]; decide
            obtain ⟨hsf3_expr, hsf3_env, hsf3_heap, hsf3_trace⟩ := hsf3_props
            have hrel3 : ANF_SimRel s t sa sf3 := by
              refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
              rw [hsf3_expr]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
            have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
            have hwf3 : ExprWellFormed sf3.expr sf3.env := by
              rw [hsf3_expr, hsf3_env]; intro x hfx
              apply hwf x; rw [hsf]
              cases hfx with
              | seq_l _ _ hfx' =>
                rw [ha]; exact .seq_l _ _ _ (by
                  cases hfx' with
                  | seq_l _ _ hfx'' => rw [ha1, hc]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx'')
                  | seq_r _ _ hfx'' => exact .seq_r _ _ _ hfx'')
              | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
            obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
            let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2_eq⟩ : Flat.Step sf2 .silent sf3) hsteps')
            have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
            exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
          | «this» =>
            -- c = .this: two steps (resolve this, then eliminate seq-lit)
            rw [hc] at hnorm; simp only [ANF.normalizeExpr] at hnorm
            have hbd : (Flat.Expr.seq (Flat.Expr.seq d a2) b).depth ≤ N := by
              simp [Flat.Expr.depth]
              rw [hsf] at hdepth; rw [ha, ha1, hc] at hdepth
              simp [Flat.Expr.depth] at hdepth; omega
            obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent,
                { expr := .seq (.seq (.seq (.lit val) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
              rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
              rw [ha, ha1, hc]; unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?
              unfold Flat.step?
              cases sf.env.lookup "this" with
              | some v => exact ⟨v, rfl⟩
              | none => exact ⟨.undefined, rfl⟩
            let sf2 : Flat.State := { expr := .seq (.seq (.seq (.lit val) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
            obtain ⟨sf3, hstep2_eq⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
              simp only [sf2]; unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?
              unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
            have hsf3_props : sf3.expr = .seq (.seq d a2) b ∧ sf3.env = sf.env ∧ sf3.heap = sf.heap ∧
                observableTrace sf3.trace = observableTrace sf.trace := by
              have h0 := hstep2_eq; simp only [sf2] at h0
              unfold Flat.step? Flat.exprValue? at h0
              unfold Flat.step? Flat.exprValue? at h0
              unfold Flat.step? Flat.exprValue? at h0
              have heq := (Prod.mk.inj (Option.some.inj h0)).2
              refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                      congrArg Flat.State.env heq ▸ rfl,
                      congrArg Flat.State.heap heq ▸ rfl, ?_⟩
              subst heq
              show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
              simp [observableTrace, List.filter_append]; decide
            obtain ⟨hsf3_expr, hsf3_env, hsf3_heap, hsf3_trace⟩ := hsf3_props
            have hrel3 : ANF_SimRel s t sa sf3 := by
              refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
              rw [hsf3_expr]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
            have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
            have hwf3 : ExprWellFormed sf3.expr sf3.env := by
              rw [hsf3_expr, hsf3_env]; intro x hfx
              apply hwf x; rw [hsf]
              cases hfx with
              | seq_l _ _ hfx' =>
                rw [ha]; exact .seq_l _ _ _ (by
                  cases hfx' with
                  | seq_l _ _ hfx'' => rw [ha1, hc]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx'')
                  | seq_r _ _ hfx'' => exact .seq_r _ _ _ hfx'')
              | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
            obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
            let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2_eq⟩ : Flat.Step sf2 .silent sf3) hsteps')
            have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
            exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
          | seq c1 c2 =>
            -- Nested seq c = .seq c1 c2: case-split c1 to flatten one more level.
            -- sf.expr = .seq(.seq(.seq(.seq c1 c2) d) a2) b
            -- After flattening c1, target = .seq(.seq(.seq c2 d) a2) b with depth ≤ N.
            rw [hc] at hnorm; simp only [ANF.normalizeExpr] at hnorm
            cases hc1 : c1 with
            | lit v1 =>
              -- c1 = .lit v1: one step eliminates innermost seq
              rw [hc1] at hnorm; simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm
              have hbd : (Flat.Expr.seq (Flat.Expr.seq (Flat.Expr.seq c2 d) a2) b).depth ≤ N := by
                simp [Flat.Expr.depth]
                rw [hsf] at hdepth; rw [ha, ha1, hc, hc1] at hdepth
                simp [Flat.Expr.depth] at hdepth; omega
              cases v1 <;> simp at hnorm <;> (
                obtain ⟨sf2, hstep_eq⟩ : ∃ sf2, Flat.step? sf = some (.silent, sf2) := by
                  rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
                  rw [ha, ha1, hc, hc1]; unfold Flat.step? Flat.exprValue?
                  unfold Flat.step? Flat.exprValue?
                  unfold Flat.step? Flat.exprValue?
                  unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
                have hsf2_props : sf2.expr = .seq (.seq (.seq c2 d) a2) b ∧ sf2.env = sf.env ∧ sf2.heap = sf.heap ∧
                    observableTrace sf2.trace = observableTrace sf.trace := by
                  have h0 := hstep_eq
                  rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all] at h0
                  rw [ha, ha1, hc, hc1] at h0; unfold Flat.step? Flat.exprValue? at h0
                  unfold Flat.step? Flat.exprValue? at h0
                  unfold Flat.step? Flat.exprValue? at h0
                  unfold Flat.step? Flat.exprValue? at h0
                  have heq := (Prod.mk.inj (Option.some.inj h0)).2
                  refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                          congrArg Flat.State.env heq ▸ rfl,
                          congrArg Flat.State.heap heq ▸ rfl, ?_⟩
                  subst heq; show observableTrace (sf.trace ++ [.silent]) = observableTrace sf.trace
                  simp [observableTrace, List.filter_append]; decide
                obtain ⟨he, henv2, hheap2, htrace2⟩ := hsf2_props
                have hrel2 : ANF_SimRel s t sa sf2 := by
                  refine ⟨hheap.trans hheap2.symm, henv.trans henv2.symm, htrace.trans htrace2.symm, k, n, m, ?_, hfaithful⟩
                  rw [he]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
                have hbd2 : sf2.expr.depth ≤ N := by rw [he]; exact hbd
                have hwf2 : ExprWellFormed sf2.expr sf2.env := by
                  rw [he, henv2]; intro x hfx
                  apply hwf x; rw [hsf]
                  cases hfx with
                  | seq_l _ _ hfx' =>
                    rw [ha]; exact .seq_l _ _ _ (by
                      cases hfx' with
                      | seq_l _ _ hfx'' =>
                        rw [ha1]; exact .seq_l _ _ _ (by
                          cases hfx'' with
                          | seq_l _ _ hfx''' => rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                          | seq_r _ _ hfx''' => exact .seq_r _ _ _ hfx''')
                      | seq_r _ _ hfx'' => exact .seq_r _ _ _ hfx'')
                  | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
                obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ :=
                  ih sa sf2 hbd2 hrel2 hstuck hwf2
                exact ⟨sf', .silent :: evs,
                  Flat.Steps.tail ⟨hstep_eq⟩ hsteps',
                  hhalt', by show observableTrace (.silent :: evs) = []; simp [observableTrace_silent, hobs'],
                  hrel'⟩)
            | var name1 =>
              -- c1 = .var name1: two steps (evaluate var, then eliminate seq-lit)
              rw [hc1] at hnorm; simp only [ANF.normalizeExpr] at hnorm
              have hbd : (Flat.Expr.seq (Flat.Expr.seq (Flat.Expr.seq c2 d) a2) b).depth ≤ N := by
                simp [Flat.Expr.depth]
                rw [hsf] at hdepth; rw [ha, ha1, hc, hc1] at hdepth
                simp [Flat.Expr.depth] at hdepth; omega
              have hname1_bound : sf.env.lookup name1 ≠ none := by
                apply hwf name1
                rw [hsf, ha, ha1, hc, hc1]; exact .seq_l _ _ _ (.seq_l _ _ _ (.seq_l _ _ _ (.seq_l _ _ _ (.var _))))
              obtain ⟨val, hval⟩ : ∃ v, sf.env.lookup name1 = some v := by
                cases hlu : sf.env.lookup name1 with
                | some v => exact ⟨v, rfl⟩
                | none => exact absurd hlu hname1_bound
              have hstep1 : Flat.step? sf = some (.silent,
                  { expr := .seq (.seq (.seq (.seq (.lit val) c2) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
                rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
                rw [ha, ha1, hc, hc1]; unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step?
                rw [hval]; rfl
              let sf2 : Flat.State := { expr := .seq (.seq (.seq (.seq (.lit val) c2) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
              obtain ⟨sf3, hstep2_eq⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
                simp only [sf2]; unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
              have hsf3_props : sf3.expr = .seq (.seq (.seq c2 d) a2) b ∧ sf3.env = sf.env ∧ sf3.heap = sf.heap ∧
                  observableTrace sf3.trace = observableTrace sf.trace := by
                have h0 := hstep2_eq; simp only [sf2] at h0
                unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                have heq := (Prod.mk.inj (Option.some.inj h0)).2
                refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                        congrArg Flat.State.env heq ▸ rfl,
                        congrArg Flat.State.heap heq ▸ rfl, ?_⟩
                subst heq
                show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
                simp [observableTrace, List.filter_append]; decide
              obtain ⟨hsf3_expr, hsf3_env, hsf3_heap, hsf3_trace⟩ := hsf3_props
              have hrel3 : ANF_SimRel s t sa sf3 := by
                refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
                rw [hsf3_expr]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
              have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
              have hwf3 : ExprWellFormed sf3.expr sf3.env := by
                rw [hsf3_expr, hsf3_env]; intro x hfx
                apply hwf x; rw [hsf]
                cases hfx with
                | seq_l _ _ hfx' =>
                  rw [ha]; exact .seq_l _ _ _ (by
                    cases hfx' with
                    | seq_l _ _ hfx'' =>
                      rw [ha1]; exact .seq_l _ _ _ (by
                        cases hfx'' with
                        | seq_l _ _ hfx''' => rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                        | seq_r _ _ hfx''' => exact .seq_r _ _ _ hfx''')
                    | seq_r _ _ hfx'' => exact .seq_r _ _ _ hfx'')
                | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
              obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
              let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2_eq⟩ : Flat.Step sf2 .silent sf3) hsteps')
              have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
              exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
            | «this» =>
              -- c1 = .this: two steps (resolve this, then eliminate seq-lit)
              rw [hc1] at hnorm; simp only [ANF.normalizeExpr] at hnorm
              have hbd : (Flat.Expr.seq (Flat.Expr.seq (Flat.Expr.seq c2 d) a2) b).depth ≤ N := by
                simp [Flat.Expr.depth]
                rw [hsf] at hdepth; rw [ha, ha1, hc, hc1] at hdepth
                simp [Flat.Expr.depth] at hdepth; omega
              obtain ⟨val, hstep1⟩ : ∃ val, Flat.step? sf = some (.silent,
                  { expr := .seq (.seq (.seq (.seq (.lit val) c2) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }) := by
                rw [show sf = {sf with expr := .seq a b} from by cases sf; simp_all]
                rw [ha, ha1, hc, hc1]; unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step?
                cases sf.env.lookup "this" with
                | some v => exact ⟨v, rfl⟩
                | none => exact ⟨.undefined, rfl⟩
              let sf2 : Flat.State := { expr := .seq (.seq (.seq (.seq (.lit val) c2) d) a2) b, env := sf.env, heap := sf.heap, trace := sf.trace ++ [.silent], funcs := sf.funcs, callStack := sf.callStack }
              obtain ⟨sf3, hstep2_eq⟩ : ∃ sf3, Flat.step? sf2 = some (.silent, sf3) := by
                simp only [sf2]; unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?
                unfold Flat.step? Flat.exprValue?; exact ⟨_, rfl⟩
              have hsf3_props : sf3.expr = .seq (.seq (.seq c2 d) a2) b ∧ sf3.env = sf.env ∧ sf3.heap = sf.heap ∧
                  observableTrace sf3.trace = observableTrace sf.trace := by
                have h0 := hstep2_eq; simp only [sf2] at h0
                unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                unfold Flat.step? Flat.exprValue? at h0
                have heq := (Prod.mk.inj (Option.some.inj h0)).2
                refine ⟨congrArg Flat.State.expr heq ▸ rfl,
                        congrArg Flat.State.env heq ▸ rfl,
                        congrArg Flat.State.heap heq ▸ rfl, ?_⟩
                subst heq
                show observableTrace ((sf.trace ++ [.silent]) ++ [.silent]) = observableTrace sf.trace
                simp [observableTrace, List.filter_append]; decide
              obtain ⟨hsf3_expr, hsf3_env, hsf3_heap, hsf3_trace⟩ := hsf3_props
              have hrel3 : ANF_SimRel s t sa sf3 := by
                refine ⟨hheap.trans hsf3_heap.symm, henv.trans hsf3_env.symm, htrace.trans hsf3_trace.symm, k, n, m, ?_, hfaithful⟩
                rw [hsf3_expr]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm
              have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
              have hwf3 : ExprWellFormed sf3.expr sf3.env := by
                rw [hsf3_expr, hsf3_env]; intro x hfx
                apply hwf x; rw [hsf]
                cases hfx with
                | seq_l _ _ hfx' =>
                  rw [ha]; exact .seq_l _ _ _ (by
                    cases hfx' with
                    | seq_l _ _ hfx'' =>
                      rw [ha1]; exact .seq_l _ _ _ (by
                        cases hfx'' with
                        | seq_l _ _ hfx''' => rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                        | seq_r _ _ hfx''' => exact .seq_r _ _ _ hfx''')
                    | seq_r _ _ hfx'' => exact .seq_r _ _ _ hfx'')
                | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
              obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
              let steps12 := Flat.Steps.tail (⟨hstep1⟩ : Flat.Step sf .silent sf2) (Flat.Steps.tail (⟨hstep2_eq⟩ : Flat.Step sf2 .silent sf3) hsteps')
              have hobsAll : observableTrace (.silent :: .silent :: evs) = [] := by simp [observableTrace_silent, hobs']
              exact ⟨sf', .silent :: .silent :: evs, steps12, hhalt', hobsAll, hrel'⟩
            | seq c1a c1b =>
              -- c1 = .seq c1a c1b: use normalizeExpr_ignored_bypass_trivial to bypass c1
              rw [hc1] at hnorm; simp only [ANF.normalizeExpr] at hnorm
              -- Bypass both sub-expressions of c1
              have hnorm_c1b := normalizeExpr_ignored_bypass_trivial c1a.depth c1a (Nat.le_refl _) _ n m tv hnorm
              have hnorm_c2 := normalizeExpr_ignored_bypass_trivial c1b.depth c1b (Nat.le_refl _) _ n m tv hnorm_c1b
              -- Depth bound for target expression
              have hbd : (Flat.Expr.seq (Flat.Expr.seq (Flat.Expr.seq c2 d) a2) b).depth ≤ N := by
                simp [Flat.Expr.depth]
                rw [hsf] at hdepth; rw [ha, ha1, hc, hc1] at hdepth
                simp [Flat.Expr.depth] at hdepth; omega
              -- Derive trivial chain property
              have htc_a := normalizeExpr_trivial_implies_chain c1a.depth c1a (Nat.le_refl _) _ n m tv hnorm
              have htc_b := normalizeExpr_trivial_implies_chain c1b.depth c1b (Nat.le_refl _) _ n m tv hnorm_c1b
              have htc_seq : isTrivialChain (Flat.Expr.seq c1a c1b) = true := by
                simp [isTrivialChain]; exact ⟨htc_a, htc_b⟩
              -- sf.expr = wrapSeqCtx (.seq c1a c1b) [c2, d, a2, b]
              have hsf_tc : sf.expr = wrapSeqCtx (Flat.Expr.seq c1a c1b) [c2, d, a2, b] := by
                rw [hsf, ha, ha1, hc, hc1]; rfl
              have hwf_tc : ∀ x, VarFreeIn x (Flat.Expr.seq c1a c1b) → sf.env.lookup x ≠ none := by
                intro x hfx; apply hwf x; rw [hsf, ha, ha1, hc, hc1]
                exact .seq_l _ _ _ (.seq_l _ _ _ (.seq_l _ _ _ (.seq_l _ _ _ hfx)))
              obtain ⟨evs_tc, sf3, hsteps_tc, hexpr3, henv3, hheap3, htrace3, hobs_tc⟩ :=
                trivialChain_consume_ctx (trivialChainCost (Flat.Expr.seq c1a c1b))
                  (Flat.Expr.seq c1a c1b) [c2, d, a2, b] sf htc_seq (Nat.le_refl _)
                  (List.cons_ne_nil _ _) hsf_tc hwf_tc
              have hsf3_expr : sf3.expr = Flat.Expr.seq (Flat.Expr.seq (Flat.Expr.seq c2 d) a2) b := by
                rw [hexpr3]; rfl
              have hrel3 : ANF_SimRel s t sa sf3 := by
                refine ⟨hheap.trans hheap3.symm, henv.trans henv3.symm, htrace.trans htrace3.symm, k, n, m, ?_, hfaithful⟩
                rw [hsf3_expr]; simp only [ANF.normalizeExpr]; rw [hat]; exact hnorm_c2
              have hbd3 : sf3.expr.depth ≤ N := by rw [hsf3_expr]; exact hbd
              have hwf3 : ExprWellFormed sf3.expr sf3.env := by
                rw [hsf3_expr, henv3]; intro x hfx
                apply hwf x; rw [hsf]
                cases hfx with
                | seq_l _ _ hfx' =>
                  rw [ha]; exact .seq_l _ _ _ (by
                    cases hfx' with
                    | seq_l _ _ hfx'' =>
                      rw [ha1]; exact .seq_l _ _ _ (by
                        cases hfx'' with
                        | seq_l _ _ hfx''' => rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                        | seq_r _ _ hfx''' => exact .seq_r _ _ _ hfx''')
                    | seq_r _ _ hfx'' => exact .seq_r _ _ _ hfx'')
                | seq_r _ _ hfx' => exact .seq_r _ _ _ hfx'
              obtain ⟨sf', evs, hsteps', hhalt', hobs', hrel'⟩ := ih sa sf3 hbd3 hrel3 hstuck hwf3
              exact ⟨sf', evs_tc ++ evs, Flat.Steps.append hsteps_tc hsteps', hhalt',
                by rw [observableTrace_append, hobs_tc, hobs']; rfl, hrel'⟩
            | _ =>
              -- Compound c1: normalizeExpr c1 can't produce trivial
              exfalso
              exact absurd hnorm (normalizeExpr_compound_not_trivial c1 _
                (by intro v; rw [hc1]; exact Flat.Expr.noConfusion)
                (by intro nm; rw [hc1]; exact Flat.Expr.noConfusion)
                (by rw [hc1]; exact Flat.Expr.noConfusion)
                (by intro a' b'; rw [hc1]; exact Flat.Expr.noConfusion) n m tv)
          | _ =>
            -- Compound c (not lit/var/this/seq): normalizeExpr c never produces .trivial
            exfalso
            exact absurd hnorm (normalizeExpr_compound_not_trivial c _
              (by intro v; rw [hc]; exact Flat.Expr.noConfusion)
              (by intro nm; rw [hc]; exact Flat.Expr.noConfusion)
              (by rw [hc]; exact Flat.Expr.noConfusion)
              (by intro a' b'; rw [hc]; exact Flat.Expr.noConfusion) n m tv)
        | _ =>
          -- Compound a1: normalizeExpr a1 never produces .trivial → contradiction
          exfalso
          exact absurd hnorm (normalizeExpr_compound_not_trivial a1 _
            (by intro v; rw [ha1]; exact Flat.Expr.noConfusion)
            (by intro nm; rw [ha1]; exact Flat.Expr.noConfusion)
            (by rw [ha1]; exact Flat.Expr.noConfusion)
            (by intro a' b'; rw [ha1]; exact Flat.Expr.noConfusion) n m tv)
      | _ =>
        exfalso
        exact absurd hnorm (normalizeExpr_compound_not_trivial a _
          (by intro v; rw [ha]; exact Flat.Expr.noConfusion)
          (by intro nm; rw [ha]; exact Flat.Expr.noConfusion)
          (by rw [ha]; exact Flat.Expr.noConfusion)
          (by intro a' b'; rw [ha]; exact Flat.Expr.noConfusion) n m tv)
    | _ =>
      exfalso; rw [hat] at hnorm
      have h1 : ∀ v, sf.expr ≠ .lit v := by intro v hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      have h2 : ∀ name, sf.expr ≠ .var name := by intro nm hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      have h3 : sf.expr ≠ .this := by intro hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      have h4 : ∀ a b, sf.expr ≠ .seq a b := by intro a b hc; rw [hsf] at hc; exact Flat.Expr.noConfusion hc
      exact absurd hnorm (normalizeExpr_compound_not_trivial sf.expr k h1 h2 h3 h4 n m tv)

/-- When ANF reaches a terminal state (step? = none), Flat can also reach a
    terminal state after zero or more silent steps. -/
private theorem anfConvert_halt_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State),
      ANF_SimRel s t sa sf →
      ANF.step? sa = none →
      ExprWellFormed sf.expr sf.env →
      ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
        Flat.Steps sf evs sf' ∧
        Flat.step? sf' = none ∧
        observableTrace evs = [] ∧
        ANF_SimRel s t sa sf' :=
  fun sa sf hrel hstuck hwf =>
    anfConvert_halt_star_aux s t h sf.expr.depth sa sf (Nat.le_refl _) hrel hstuck hwf

/-- Multi-step simulation derived from single-step stuttering simulation. -/
private theorem anfConvert_steps_star
    (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t) :
    ∀ (sa : ANF.State) (sf : Flat.State) (tr : List Core.TraceEvent) (sa' : ANF.State),
      ANF_SimRel s t sa sf →
      ExprWellFormed sf.expr sf.env →
      ANF.Steps sa tr sa' →
      ∃ (sf' : Flat.State) (tr' : List Core.TraceEvent),
        Flat.Steps sf tr' sf' ∧
        observableTrace tr = observableTrace tr' ∧
        ANF_SimRel s t sa' sf' ∧
        ExprWellFormed sf'.expr sf'.env := by
  intro sa sf tr sa' hrel hwf hsteps
  induction hsteps generalizing sf with
  | refl => exact ⟨sf, [], .refl sf, rfl, hrel, hwf⟩
  | tail hstep _ ih =>
    obtain ⟨sf2, evs1, hfsteps1, hobsev, hrel2, hwf2⟩ :=
      anfConvert_step_star s t h _ _ _ _ hrel hwf hstep
    obtain ⟨sf3, evs2, hfsteps2, hobstr, hrel3, hwf3⟩ :=
      ih sf2 hrel2 hwf2
    exact ⟨sf3, evs1 ++ evs2,
      Flat.Steps.append hfsteps1 hfsteps2,
      by rw [show ∀ (a : Core.TraceEvent) l, a :: l = [a] ++ l from fun _ _ => rfl,
             observableTrace_append, observableTrace_append, hobsev, hobstr],
      hrel3, hwf3⟩

/-- ANF conversion preserves observable behavior:
    For every terminating ANF execution, there exists a terminating Flat
    execution with the same observable trace (non-silent events).
    Precondition: the initial expression is well-scoped (all top-level
    free .var references in .seq chains are bound in the initial env). -/
theorem anfConvert_correct (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t)
    (hwf_prog : ExprWellFormed s.main (Flat.initialState s).env) :
    ∀ b, ANF.Behaves t b →
      ∃ b', Flat.Behaves s b' ∧ observableTrace b = observableTrace b' := by
  intro b ⟨sa, hsteps, hhalt⟩
  have hinit := anfConvert_init_related s t h
  have hwf_init : ExprWellFormed (Flat.initialState s).expr (Flat.initialState s).env :=
    hwf_prog
  -- Multi-step simulation (now threads WF)
  obtain ⟨sf, tr', hfsteps, hobstr, hrel, hwf_sf⟩ :=
    anfConvert_steps_star s t h _ _ _ _ hinit hwf_init hsteps
  obtain ⟨sf', evs', hfsteps', hhalt', hobsevs, hrel'⟩ :=
    anfConvert_halt_star s t h _ _ hrel hhalt hwf_sf
  -- Combine: Flat reaches sf via tr', then sf' via evs' (all silent)
  exact ⟨tr' ++ evs', ⟨sf', Flat.Steps.append hfsteps hfsteps', hhalt'⟩,
    by rw [observableTrace_append, hobsevs, List.append_nil]; exact hobstr⟩

end VerifiedJS.Proofs
