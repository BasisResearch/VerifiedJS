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
  | this_var : VarFreeIn "this" .this
  | return_some_arg (x : String) (v : Flat.Expr) : VarFreeIn x v → VarFreeIn x (.«return» (some v))
  | await_arg (x : String) (arg : Flat.Expr) : VarFreeIn x arg → VarFreeIn x (.await arg)
  | yield_some_arg (x : String) (v : Flat.Expr) (d : Bool) : VarFreeIn x v → VarFreeIn x (.yield (some v) d)
  | assign_value (x name : String) (v : Flat.Expr) : VarFreeIn x v → VarFreeIn x (.assign name v)
  | unary_arg (x : String) (op : Core.UnaryOp) (arg : Flat.Expr) :
      VarFreeIn x arg → VarFreeIn x (.unary op arg)
  | binary_lhs (x : String) (op : Core.BinOp) (l r : Flat.Expr) :
      VarFreeIn x l → VarFreeIn x (.binary op l r)
  | binary_rhs (x : String) (op : Core.BinOp) (l r : Flat.Expr) :
      VarFreeIn x r → VarFreeIn x (.binary op l r)
  | typeof_arg (x : String) (arg : Flat.Expr) : VarFreeIn x arg → VarFreeIn x (.typeof arg)
  | getProp_obj (x : String) (obj : Flat.Expr) (prop : Flat.PropName) :
      VarFreeIn x obj → VarFreeIn x (.getProp obj prop)
  | setProp_obj (x : String) (obj : Flat.Expr) (prop : Flat.PropName) (val : Flat.Expr) :
      VarFreeIn x obj → VarFreeIn x (.setProp obj prop val)
  | setProp_value (x : String) (obj : Flat.Expr) (prop : Flat.PropName) (val : Flat.Expr) :
      VarFreeIn x val → VarFreeIn x (.setProp obj prop val)
  | getIndex_obj (x : String) (obj idx : Flat.Expr) :
      VarFreeIn x obj → VarFreeIn x (.getIndex obj idx)
  | getIndex_idx (x : String) (obj idx : Flat.Expr) :
      VarFreeIn x idx → VarFreeIn x (.getIndex obj idx)
  | setIndex_obj (x : String) (obj idx val : Flat.Expr) :
      VarFreeIn x obj → VarFreeIn x (.setIndex obj idx val)
  | setIndex_idx (x : String) (obj idx val : Flat.Expr) :
      VarFreeIn x idx → VarFreeIn x (.setIndex obj idx val)
  | setIndex_value (x : String) (obj idx val : Flat.Expr) :
      VarFreeIn x val → VarFreeIn x (.setIndex obj idx val)
  | deleteProp_obj (x : String) (obj : Flat.Expr) (prop : Flat.PropName) :
      VarFreeIn x obj → VarFreeIn x (.deleteProp obj prop)
  | getEnv_env (x : String) (envPtr : Flat.Expr) (idx : Nat) :
      VarFreeIn x envPtr → VarFreeIn x (.getEnv envPtr idx)
  | makeClosure_env (x : String) (funcIdx : Core.FuncIdx) (env : Flat.Expr) :
      VarFreeIn x env → VarFreeIn x (.makeClosure funcIdx env)
  | call_func (x : String) (f e : Flat.Expr) (args : List Flat.Expr) :
      VarFreeIn x f → VarFreeIn x (.call f e args)
  | call_env (x : String) (f e : Flat.Expr) (args : List Flat.Expr) :
      VarFreeIn x e → VarFreeIn x (.call f e args)
  | call_arg (x : String) (f e : Flat.Expr) (args : List Flat.Expr) (a : Flat.Expr) :
      a ∈ args → VarFreeIn x a → VarFreeIn x (.call f e args)
  | newObj_func (x : String) (f e : Flat.Expr) (args : List Flat.Expr) :
      VarFreeIn x f → VarFreeIn x (.newObj f e args)
  | newObj_env (x : String) (f e : Flat.Expr) (args : List Flat.Expr) :
      VarFreeIn x e → VarFreeIn x (.newObj f e args)
  | newObj_arg (x : String) (f e : Flat.Expr) (args : List Flat.Expr) (a : Flat.Expr) :
      a ∈ args → VarFreeIn x a → VarFreeIn x (.newObj f e args)
  | makeEnv_elem (x : String) (values : List Flat.Expr) (v : Flat.Expr) :
      v ∈ values → VarFreeIn x v → VarFreeIn x (.makeEnv values)
  | arrayLit_elem (x : String) (elems : List Flat.Expr) (e : Flat.Expr) :
      e ∈ elems → VarFreeIn x e → VarFreeIn x (.arrayLit elems)
  | objectLit_value (x : String) (props : List (Flat.PropName × Flat.Expr)) (p : Flat.PropName × Flat.Expr) :
      p ∈ props → VarFreeIn x p.2 → VarFreeIn x (.objectLit props)
  | tryCatch_finally (x : String) (b : Flat.Expr) (cp : String) (cb fin : Flat.Expr) :
      VarFreeIn x fin → VarFreeIn x (.tryCatch b cp cb (some fin))

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

/-- bindComplex always produces .let, never .while_. -/
private theorem bindComplex_not_while (rhs : ANF.ComplexExpr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (c b : ANF.Expr) :
    (ANF.bindComplex rhs k).run n ≠ .ok (.while_ c b, m) := by
  show ANF.bindComplex rhs k n ≠ .ok (.while_ c b, m)
  simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
             get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
             StateT.set, pure, Pure.pure, StateT.pure, Except.pure, getThe, MonadStateOf.get]
  cases hk : k (.var (toString "_anf" ++ toString (Nat.repr n))) (n + 1) with
  | error => simp [hk]
  | ok v => intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1

private theorem bindComplex_not_seq (rhs : ANF.ComplexExpr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (a b : ANF.Expr) :
    (ANF.bindComplex rhs k).run n ≠ .ok (.seq a b, m) := by
  show ANF.bindComplex rhs k n ≠ .ok (.seq a b, m)
  simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
             get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
             StateT.set, pure, Pure.pure, StateT.pure, Except.pure, getThe, MonadStateOf.get]
  cases hk : k (.var (toString "_anf" ++ toString (Nat.repr n))) (n + 1) with
  | error => simp [hk]
  | ok v => intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1

private theorem bindComplex_not_if (rhs : ANF.ComplexExpr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (c : ANF.Trivial) (t e : ANF.Expr) :
    (ANF.bindComplex rhs k).run n ≠ .ok (.if c t e, m) := by
  show ANF.bindComplex rhs k n ≠ .ok (.if c t e, m)
  simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
             get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
             StateT.set, pure, Pure.pure, StateT.pure, Except.pure, getThe, MonadStateOf.get]
  cases hk : k (.var (toString "_anf" ++ toString (Nat.repr n))) (n + 1) with
  | error => simp [hk]
  | ok v => intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1

private theorem bindComplex_not_tryCatch (rhs : ANF.ComplexExpr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (body : ANF.Expr) (cp : ANF.VarName) (cb : ANF.Expr) (fin : Option ANF.Expr) :
    (ANF.bindComplex rhs k).run n ≠ .ok (.tryCatch body cp cb fin, m) := by
  show ANF.bindComplex rhs k n ≠ .ok (.tryCatch body cp cb fin, m)
  simp only [ANF.bindComplex, ANF.freshName, bind, Bind.bind, StateT.bind, Except.bind,
             get, GetElem.getElem, MonadState.get, StateT.get, set, MonadState.set,
             StateT.set, pure, Pure.pure, StateT.pure, Except.pure, getThe, MonadStateOf.get]
  cases hk : k (.var (toString "_anf" ++ toString (Nat.repr n))) (n + 1) with
  | error => simp [hk]
  | ok v => intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1

/-- normalizeExpr never produces .while_ at the top level when k doesn't.
    Combined with normalizeExprList and normalizeProps by strong induction on depth. -/
private theorem normalizeExpr_not_while_family :
    ∀ (d : Nat),
      (∀ (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr),
        (∀ x n' m' c b, (k x) n' ≠ .ok (.while_ c b, m')) →
        e.depth ≤ d → ∀ n m c b, (ANF.normalizeExpr e k) n ≠ .ok (.while_ c b, m)) ∧
      (∀ (es : List Flat.Expr) (k : List ANF.Trivial → ANF.ConvM ANF.Expr),
        (∀ xs n' m' c b, (k xs) n' ≠ .ok (.while_ c b, m')) →
        Flat.Expr.listDepth es ≤ d → ∀ n m c b, (ANF.normalizeExprList es k) n ≠ .ok (.while_ c b, m)) ∧
      (∀ (ps : List (Flat.PropName × Flat.Expr)) (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr),
        (∀ xs n' m' c b, (k xs) n' ≠ .ok (.while_ c b, m')) →
        Flat.Expr.propListDepth ps ≤ d → ∀ n m c b, (ANF.normalizeProps ps k) n ≠ .ok (.while_ c b, m))
    := by
  intro d
  induction d with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e k hk hd n m c b
      cases e with
      | lit v =>
        simp only [ANF.normalizeExpr]
        cases ANF.trivialOfFlatValue v with
        | ok tv => exact hk tv n m c b
        | error _ => nofun
      | var name => simp only [ANF.normalizeExpr]; exact hk (.var name) n m c b
      | this => simp only [ANF.normalizeExpr]; exact hk (.var "this") n m c b
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
    · intro es k hk hd n m c b
      cases es with
      | nil => simp only [ANF.normalizeExprList]; exact hk [] n m c b
      | cons e rest => exfalso; simp [Flat.Expr.listDepth] at hd
    · intro ps k hk hd n m c b
      cases ps with
      | nil => simp only [ANF.normalizeProps]; exact hk [] n m c b
      | cons p rest => exfalso; simp [Flat.Expr.propListDepth] at hd
  | succ d ih =>
    obtain ⟨ihe, ihes, ihps⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- normalizeExpr
    · intro e k hk hd n m c b
      cases e with
      | lit v =>
        simp only [ANF.normalizeExpr]
        cases ANF.trivialOfFlatValue v with
        | ok tv => exact hk tv n m c b
        | error _ => nofun
      | var name => simp only [ANF.normalizeExpr]; exact hk (.var name) n m c b
      | this => simp only [ANF.normalizeExpr]; exact hk (.var "this") n m c b
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
            (by intro x n' m' c' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
            (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | yield arg delegate =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1
        | some value =>
          simp only [ANF.normalizeExpr]
          exact ihe value (fun t => pure (.yield (some t) delegate))
            (by intro x n' m' c' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
            (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | throw arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun t => pure (.throw t))
          (by intro x n' m' c' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | await arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun t => pure (.await t))
          (by intro x n' m' c' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | assign name value =>
        simp only [ANF.normalizeExpr]
        exact ihe value (fun vt => ANF.bindComplex (.assign name vt) k)
          (by intro x n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | unary op arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun at_ => ANF.bindComplex (.unary op at_) k)
          (by intro x n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | typeof arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun at_ => ANF.bindComplex (.typeof at_) k)
          (by intro x n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | getProp obj prop =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.bindComplex (.getProp ot prop) k)
          (by intro x n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.bindComplex (.deleteProp ot prop) k)
          (by intro x n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr]
        exact ihe envPtr (fun et => ANF.bindComplex (.getEnv et idx) k)
          (by intro x n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr]
        exact ihe env (fun et => ANF.bindComplex (.makeClosure funcIdx et) k)
          (by intro x n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | setProp obj prop value =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setProp ot prop vt) k))
          (by intro x n' m' c' b'
              exact ihe value (fun vt => ANF.bindComplex (.setProp x prop vt) k)
                (by intro y n'' m'' c'' b''; exact bindComplex_not_while _ k n'' m'' c'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.normalizeExpr idx (fun it => ANF.bindComplex (.getIndex ot it) k))
          (by intro x n' m' c' b'
              exact ihe idx (fun it => ANF.bindComplex (.getIndex x it) k)
                (by intro y n'' m'' c'' b''; exact bindComplex_not_while _ k n'' m'' c'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | setIndex obj idx value =>
        simp only [ANF.normalizeExpr]
        exact ihe obj
          (fun ot => ANF.normalizeExpr idx (fun it => ANF.normalizeExpr value
            (fun vt => ANF.bindComplex (.setIndex ot it vt) k)))
          (by intro x n' m' c' b'
              exact ihe idx (fun it => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setIndex x it vt) k))
                (by intro y n'' m'' c'' b''
                    exact ihe value (fun vt => ANF.bindComplex (.setIndex x y vt) k)
                      (by intro z n3 m3 c3 b3; exact bindComplex_not_while _ k n3 m3 c3 b3)
                      (by simp [Flat.Expr.depth] at hd ⊢; omega) n'' m'' c'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr]
        exact ihe lhs (fun lt => ANF.normalizeExpr rhs (fun rt => ANF.bindComplex (.binary op lt rt) k))
          (by intro x n' m' c' b'
              exact ihe rhs (fun rt => ANF.bindComplex (.binary op x rt) k)
                (by intro y n'' m'' c'' b''; exact bindComplex_not_while _ k n'' m'' c'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | «let» name init body =>
        simp only [ANF.normalizeExpr]
        exact ihe init (fun initTriv => do
            let bodyExpr ← ANF.normalizeExpr body k
            pure (.let name (.trivial initTriv) bodyExpr))
          (by intro x n' m' c' b'
              simp only [bind, Bind.bind, StateT.bind, Except.bind]
              intro habs; split at habs
              · cases habs
              · simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | «if» cond then_ else_ =>
        simp only [ANF.normalizeExpr]
        exact ihe cond (fun condTriv => do
            let thenExpr ← ANF.normalizeExpr then_ k
            let elseExpr ← ANF.normalizeExpr else_ k
            pure (.if condTriv thenExpr elseExpr))
          (by intro x n' m' c' b'
              simp only [bind, Bind.bind, StateT.bind, Except.bind]
              intro habs
              repeat (first | split at habs | (simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | seq a₁ b₁ =>
        simp only [ANF.normalizeExpr]
        exact ihe a₁ (fun _ => ANF.normalizeExpr b₁ k)
          (by intro x n' m' c' b'
              exact ihe b₁ k hk (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | labeled label body₁ =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro habs
        split at habs
        · cases habs
        · simp [pure, Pure.pure, StateT.pure, Except.pure] at habs
      | while_ cond body₁ =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro habs
        repeat (first | split at habs | (simp [pure, Pure.pure, StateT.pure, Except.pure] at habs) | cases habs)
      | tryCatch body₁ catchParam catchBody finally_ =>
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
          (by intro x n' m' c' b'
              exact ihe envPtr (fun et =>
                  ANF.normalizeExprList args (fun ats => ANF.bindComplex (.call x et ats) k))
                (by intro y n'' m'' c'' b''
                    exact ihes args (fun ats => ANF.bindComplex (.call x y ats) k)
                      (by intro xs n3 m3 c3 b3; exact bindComplex_not_while _ k n3 m3 c3 b3)
                      (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n'' m'' c'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | newObj funcIdx envPtr args =>
        simp only [ANF.normalizeExpr]
        exact ihe funcIdx (fun ft => ANF.normalizeExpr envPtr (fun et =>
            ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj ft et ats) k)))
          (by intro x n' m' c' b'
              exact ihe envPtr (fun et =>
                  ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj x et ats) k))
                (by intro y n'' m'' c'' b''
                    exact ihes args (fun ats => ANF.bindComplex (.newObj x y ats) k)
                      (by intro xs n3 m3 c3 b3; exact bindComplex_not_while _ k n3 m3 c3 b3)
                      (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n'' m'' c'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m c b
      | makeEnv values =>
        simp only [ANF.normalizeExpr]
        exact ihes values (fun vts => ANF.bindComplex (.makeEnv vts) k)
          (by intro xs n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n m c b
      | objectLit props =>
        simp only [ANF.normalizeExpr]
        exact ihps props (fun pts => ANF.bindComplex (.objectLit pts) k)
          (by intro xs n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth, Flat.Expr.propListDepth] at hd ⊢; omega) n m c b
      | arrayLit elems =>
        simp only [ANF.normalizeExpr]
        exact ihes elems (fun ets => ANF.bindComplex (.arrayLit ets) k)
          (by intro xs n' m' c' b'; exact bindComplex_not_while _ k n' m' c' b')
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n m c b
    -- normalizeExprList
    · intro es k hk hd n m c b
      cases es with
      | nil => simp only [ANF.normalizeExprList]; exact hk [] n m c b
      | cons e rest =>
        simp only [ANF.normalizeExprList]
        exact ihe e (fun et => ANF.normalizeExprList rest (fun ts => k (et :: ts)))
          (by intro x n' m' c' b'
              exact ihes rest (fun ts => k (x :: ts))
                (by intro xs n'' m'' c'' b''; exact hk (x :: xs) n'' m'' c'' b'')
                (by simp [Flat.Expr.listDepth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.listDepth] at hd ⊢; omega) n m c b
    -- normalizeProps
    · intro ps k hk hd n m c b
      cases ps with
      | nil => simp only [ANF.normalizeProps]; exact hk [] n m c b
      | cons p rest =>
        obtain ⟨pn, pe⟩ := p
        simp only [ANF.normalizeProps]
        exact ihe pe (fun pt => ANF.normalizeProps rest (fun pts => k ((pn, pt) :: pts)))
          (by intro x n' m' c' b'
              exact ihps rest (fun pts => k ((pn, x) :: pts))
                (by intro xs n'' m'' c'' b''; exact hk ((pn, x) :: xs) n'' m'' c'' b'')
                (by simp [Flat.Expr.propListDepth] at hd ⊢; omega) n' m' c' b')
          (by simp [Flat.Expr.propListDepth] at hd ⊢; omega) n m c b

/-- Convenience wrapper: normalizeExpr never produces .while_ when k doesn't. -/
private theorem normalizeExpr_not_while
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ x n' m' c b, (k x).run n' ≠ .ok (.while_ c b, m'))
    (n m : Nat) (c b : ANF.Expr) :
    (ANF.normalizeExpr e k).run n ≠ .ok (.while_ c b, m) :=
  (normalizeExpr_not_while_family e.depth).1 e k hk (Nat.le_refl _) n m c b

/-- If normalizeExpr e k produces .seq a b, then either a = .while_ c d (the only direct
    source of .seq in normalizeExpr) or k produced .seq with the same first component.
    Combined with normalizeExprList and normalizeProps by strong induction on depth. -/
private theorem normalizeExpr_seq_while_first_family :
    ∀ (d : Nat),
      (∀ (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr),
        (∀ x n' m' a' b', (k x) n' = .ok (.seq a' b', m') → ∃ c d, a' = .while_ c d) →
        e.depth ≤ d → ∀ n m a b, (ANF.normalizeExpr e k) n = .ok (.seq a b, m) →
        ∃ c d, a = .while_ c d) ∧
      (∀ (es : List Flat.Expr) (k : List ANF.Trivial → ANF.ConvM ANF.Expr),
        (∀ xs n' m' a' b', (k xs) n' = .ok (.seq a' b', m') → ∃ c d, a' = .while_ c d) →
        Flat.Expr.listDepth es ≤ d → ∀ n m a b, (ANF.normalizeExprList es k) n = .ok (.seq a b, m) →
        ∃ c d, a = .while_ c d) ∧
      (∀ (ps : List (Flat.PropName × Flat.Expr)) (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr),
        (∀ xs n' m' a' b', (k xs) n' = .ok (.seq a' b', m') → ∃ c d, a' = .while_ c d) →
        Flat.Expr.propListDepth ps ≤ d → ∀ n m a b, (ANF.normalizeProps ps k) n = .ok (.seq a b, m) →
        ∃ c d, a = .while_ c d)
    := by
  intro d
  induction d with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e k hk hd n m a b
      cases e with
      | lit v =>
        simp only [ANF.normalizeExpr]
        cases ANF.trivialOfFlatValue v with
        | ok tv => exact hk tv n m a b
        | error _ => nofun
      | var name => simp only [ANF.normalizeExpr]; exact hk (.var name) n m a b
      | this => simp only [ANF.normalizeExpr]; exact hk (.var "this") n m a b
      | «break» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
      | «continue» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
      | «return» arg =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
        | some _ => exfalso; simp [Flat.Expr.depth] at hd
      | yield arg _ =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
        | some _ => exfalso; simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => exfalso; cases fin <;> simp [Flat.Expr.depth] at hd
      | _ => exfalso; simp [Flat.Expr.depth] at hd
    · intro es k hk hd n m a b
      cases es with
      | nil => simp only [ANF.normalizeExprList]; exact hk [] n m a b
      | cons e rest => exfalso; simp [Flat.Expr.listDepth] at hd
    · intro ps k hk hd n m a b
      cases ps with
      | nil => simp only [ANF.normalizeProps]; exact hk [] n m a b
      | cons p rest => exfalso; simp [Flat.Expr.propListDepth] at hd
  | succ d ih =>
    obtain ⟨ihe, ihes, ihps⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- normalizeExpr
    · intro e k hk hd n m a b
      cases e with
      | lit v =>
        simp only [ANF.normalizeExpr]
        cases ANF.trivialOfFlatValue v with
        | ok tv => exact hk tv n m a b
        | error _ => nofun
      | var name => simp only [ANF.normalizeExpr]; exact hk (.var name) n m a b
      | this => simp only [ANF.normalizeExpr]; exact hk (.var "this") n m a b
      | «break» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
      | «continue» _ =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
        intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
      | «return» arg =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
        | some value =>
          simp only [ANF.normalizeExpr]
          exact ihe value (fun t => pure (.return (some t)))
            (by intro x n' m' a' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
            (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | yield arg delegate =>
        cases arg with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure]
          intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
        | some value =>
          simp only [ANF.normalizeExpr]
          exact ihe value (fun t => pure (.yield (some t) delegate))
            (by intro x n' m' a' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
            (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | throw arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun t => pure (.throw t))
          (by intro x n' m' a' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | await arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun t => pure (.await t))
          (by intro x n' m' a' b' habs; simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | assign name value =>
        simp only [ANF.normalizeExpr]
        exact ihe value (fun vt => ANF.bindComplex (.assign name vt) k)
          (by intro x n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | unary op arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun at_ => ANF.bindComplex (.unary op at_) k)
          (by intro x n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | typeof arg =>
        simp only [ANF.normalizeExpr]
        exact ihe arg (fun at_ => ANF.bindComplex (.typeof at_) k)
          (by intro x n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | getProp obj prop =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.bindComplex (.getProp ot prop) k)
          (by intro x n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.bindComplex (.deleteProp ot prop) k)
          (by intro x n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr]
        exact ihe envPtr (fun et => ANF.bindComplex (.getEnv et idx) k)
          (by intro x n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr]
        exact ihe env (fun et => ANF.bindComplex (.makeClosure funcIdx et) k)
          (by intro x n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | setProp obj prop value =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setProp ot prop vt) k))
          (by intro x n' m' a' b'
              exact ihe value (fun vt => ANF.bindComplex (.setProp x prop vt) k)
                (by intro y n'' m'' a'' b'' habs; exact absurd habs (bindComplex_not_seq _ k n'' m'' a'' b''))
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr]
        exact ihe obj (fun ot => ANF.normalizeExpr idx (fun it => ANF.bindComplex (.getIndex ot it) k))
          (by intro x n' m' a' b'
              exact ihe idx (fun it => ANF.bindComplex (.getIndex x it) k)
                (by intro y n'' m'' a'' b'' habs; exact absurd habs (bindComplex_not_seq _ k n'' m'' a'' b''))
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | setIndex obj idx value =>
        simp only [ANF.normalizeExpr]
        exact ihe obj
          (fun ot => ANF.normalizeExpr idx (fun it => ANF.normalizeExpr value
            (fun vt => ANF.bindComplex (.setIndex ot it vt) k)))
          (by intro x n' m' a' b'
              exact ihe idx (fun it => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setIndex x it vt) k))
                (by intro y n'' m'' a'' b''
                    exact ihe value (fun vt => ANF.bindComplex (.setIndex x y vt) k)
                      (by intro z n3 m3 a3 b3 habs; exact absurd habs (bindComplex_not_seq _ k n3 m3 a3 b3))
                      (by simp [Flat.Expr.depth] at hd ⊢; omega) n'' m'' a'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr]
        exact ihe lhs (fun lt => ANF.normalizeExpr rhs (fun rt => ANF.bindComplex (.binary op lt rt) k))
          (by intro x n' m' a' b'
              exact ihe rhs (fun rt => ANF.bindComplex (.binary op x rt) k)
                (by intro y n'' m'' a'' b'' habs; exact absurd habs (bindComplex_not_seq _ k n'' m'' a'' b''))
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | «let» name init body =>
        simp only [ANF.normalizeExpr]
        exact ihe init (fun initTriv => do
            let bodyExpr ← ANF.normalizeExpr body k
            pure (.let name (.trivial initTriv) bodyExpr))
          (by intro x n' m' a' b'
              simp only [bind, Bind.bind, StateT.bind, Except.bind]
              intro habs; split at habs
              · cases habs
              · simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | «if» cond then_ else_ =>
        simp only [ANF.normalizeExpr]
        exact ihe cond (fun condTriv => do
            let thenExpr ← ANF.normalizeExpr then_ k
            let elseExpr ← ANF.normalizeExpr else_ k
            pure (.if condTriv thenExpr elseExpr))
          (by intro x n' m' a' b'
              simp only [bind, Bind.bind, StateT.bind, Except.bind]
              intro habs
              repeat (first | split at habs | (simp [pure, Pure.pure, StateT.pure, Except.pure] at habs)))
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | seq a₁ b₁ =>
        simp only [ANF.normalizeExpr]
        exact ihe a₁ (fun _ => ANF.normalizeExpr b₁ k)
          (by intro x n' m' a' b'
              exact ihe b₁ k hk (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | labeled label body₁ =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro hprod; split at hprod
        · cases hprod
        · simp [pure, Pure.pure, StateT.pure, Except.pure] at hprod
      | while_ cond body₁ =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
          Except.bind, pure, Pure.pure, StateT.pure, Except.pure]
        intro hprod; split at hprod
        · cases hprod
        · split at hprod
          · cases hprod
          · split at hprod
            · cases hprod
            · have heq := Prod.mk.inj (Except.ok.inj hprod)
              exact ⟨_, _, (ANF.Expr.seq.inj heq.1).1.symm⟩
      | tryCatch body₁ catchParam catchBody finally_ =>
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, Except.bind]
        intro hprod; cases finally_ with
        | none =>
          repeat (first | split at hprod | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hprod) | cases hprod)
        | some fin =>
          simp only [Functor.map, StateT.map, bind, Bind.bind, StateT.bind, Except.bind] at hprod
          repeat (first | split at hprod | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hprod) | cases hprod)
      | call funcIdx envPtr args =>
        simp only [ANF.normalizeExpr]
        exact ihe funcIdx (fun ft => ANF.normalizeExpr envPtr (fun et =>
            ANF.normalizeExprList args (fun ats => ANF.bindComplex (.call ft et ats) k)))
          (by intro x n' m' a' b'
              exact ihe envPtr (fun et =>
                  ANF.normalizeExprList args (fun ats => ANF.bindComplex (.call x et ats) k))
                (by intro y n'' m'' a'' b''
                    exact ihes args (fun ats => ANF.bindComplex (.call x y ats) k)
                      (by intro xs n3 m3 a3 b3 habs; exact absurd habs (bindComplex_not_seq _ k n3 m3 a3 b3))
                      (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n'' m'' a'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | newObj funcIdx envPtr args =>
        simp only [ANF.normalizeExpr]
        exact ihe funcIdx (fun ft => ANF.normalizeExpr envPtr (fun et =>
            ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj ft et ats) k)))
          (by intro x n' m' a' b'
              exact ihe envPtr (fun et =>
                  ANF.normalizeExprList args (fun ats => ANF.bindComplex (.newObj x et ats) k))
                (by intro y n'' m'' a'' b''
                    exact ihes args (fun ats => ANF.bindComplex (.newObj x y ats) k)
                      (by intro xs n3 m3 a3 b3 habs; exact absurd habs (bindComplex_not_seq _ k n3 m3 a3 b3))
                      (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n'' m'' a'' b'')
                (by simp [Flat.Expr.depth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.depth] at hd ⊢; omega) n m a b
      | makeEnv values =>
        simp only [ANF.normalizeExpr]
        exact ihes values (fun vts => ANF.bindComplex (.makeEnv vts) k)
          (by intro xs n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n m a b
      | objectLit props =>
        simp only [ANF.normalizeExpr]
        exact ihps props (fun pts => ANF.bindComplex (.objectLit pts) k)
          (by intro xs n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth, Flat.Expr.propListDepth] at hd ⊢; omega) n m a b
      | arrayLit elems =>
        simp only [ANF.normalizeExpr]
        exact ihes elems (fun ets => ANF.bindComplex (.arrayLit ets) k)
          (by intro xs n' m' a' b' habs; exact absurd habs (bindComplex_not_seq _ k n' m' a' b'))
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd ⊢; omega) n m a b
    -- normalizeExprList
    · intro es k hk hd n m a b
      cases es with
      | nil => simp only [ANF.normalizeExprList]; exact hk [] n m a b
      | cons e rest =>
        simp only [ANF.normalizeExprList]
        exact ihe e (fun et => ANF.normalizeExprList rest (fun ts => k (et :: ts)))
          (by intro x n' m' a' b'
              exact ihes rest (fun ts => k (x :: ts))
                (by intro xs n'' m'' a'' b''; exact hk (x :: xs) n'' m'' a'' b'')
                (by simp [Flat.Expr.listDepth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.listDepth] at hd ⊢; omega) n m a b
    -- normalizeProps
    · intro ps k hk hd n m a b
      cases ps with
      | nil => simp only [ANF.normalizeProps]; exact hk [] n m a b
      | cons p rest =>
        obtain ⟨pn, pe⟩ := p
        simp only [ANF.normalizeProps]
        exact ihe pe (fun pt => ANF.normalizeProps rest (fun pts => k ((pn, pt) :: pts)))
          (by intro x n' m' a' b'
              exact ihps rest (fun pts => k ((pn, x) :: pts))
                (by intro xs n'' m'' a'' b''; exact hk ((pn, x) :: xs) n'' m'' a'' b'')
                (by simp [Flat.Expr.propListDepth] at hd ⊢; omega) n' m' a' b')
          (by simp [Flat.Expr.propListDepth] at hd ⊢; omega) n m a b

/-- Convenience wrapper: if normalizeExpr e k with trivial-preserving k produces .seq a b,
    then a = .while_ c d for some c d. -/
private theorem normalizeExpr_seq_while_first
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (n m : Nat) (a b : ANF.Expr)
    (h : (ANF.normalizeExpr e k).run n = .ok (.seq a b, m)) :
    ∃ c d, a = .while_ c d :=
  (normalizeExpr_seq_while_first_family e.depth).1 e k
    (by intro x n' m' a' b' habs
        obtain ⟨m'', hm''⟩ := hk x n'
        simp only [StateT.run] at hm''
        rw [hm''] at habs; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
    (Nat.le_refl _) n m a b h

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
    (hstep : Flat.step? { s with expr := a } = some (t, sa))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .seq a b } = some (t, s') ∧
      s'.expr = .seq sa.expr b ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Contextual stepping: if cond is not a value and steps (non-error),
    .if cond then_ else_ steps with the result wrapped. -/
private theorem step?_if_cond_step (s : Flat.State) (cond then_ else_ : Flat.Expr)
    (hnotval : Flat.exprValue? cond = none)
    (t : Core.TraceEvent) (sc : Flat.State)
    (hstep : Flat.step? { s with expr := cond } = some (t, sc))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .«if» cond then_ else_ } = some (t, s') ∧
      s'.expr = .«if» sc.expr then_ else_ ∧ s'.env = sc.env ∧ s'.heap = sc.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Contextual stepping: if e is not a value and steps (non-error),
    .return (some e) steps with the result wrapped in .return (some ·). -/
private theorem step?_return_some_ctx (s : Flat.State) (e : Flat.Expr)
    (hnotval : Flat.exprValue? e = none)
    (t : Core.TraceEvent) (se : Flat.State)
    (hstep : Flat.step? { s with expr := e } = some (t, se))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .«return» (some e) } = some (t, s') ∧
      s'.expr = .«return» (some se.expr) ∧ s'.env = se.env ∧ s'.heap = se.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- If step? s = some (t, s'), then s.expr is not a value. -/
private theorem step?_some_implies_not_value {s : Flat.State} {t : Core.TraceEvent} {s' : Flat.State}
    (h : Flat.step? s = some (t, s')) : Flat.exprValue? s.expr = none := by
  cases s with
  | mk e env heap trace funcs cs =>
    cases e with
    | lit v =>
      have : Flat.step? { expr := Flat.Expr.lit v, env := env, heap := heap, trace := trace, funcs := funcs, callStack := cs } = none := by
        unfold Flat.step?; simp [Flat.exprValue?]
      rw [this] at h; exact nomatch h
    | _ => simp [Flat.exprValue?]

/-- Contextual stepping: if e is not a value and steps (non-error),
    .yield (some e) delegate steps with the result wrapped in .yield (some ·) delegate. -/
private theorem step?_yield_some_ctx (s : Flat.State) (e : Flat.Expr) (delegate : Bool)
    (hnotval : Flat.exprValue? e = none)
    (t : Core.TraceEvent) (se : Flat.State)
    (hstep : Flat.step? { s with expr := e } = some (t, se))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .yield (some e) delegate } = some (t, s') ∧
      s'.expr = .yield (some se.expr) delegate ∧ s'.env = se.env ∧ s'.heap = se.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Contextual stepping: if e is not a value and steps (non-error),
    .await e steps with the result wrapped in .await (·). -/
private theorem step?_await_ctx (s : Flat.State) (e : Flat.Expr)
    (hnotval : Flat.exprValue? e = none)
    (t : Core.TraceEvent) (se : Flat.State)
    (hstep : Flat.step? { s with expr := e } = some (t, se))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .await e } = some (t, s') ∧
      s'.expr = .await se.expr ∧ s'.env = se.env ∧ s'.heap = se.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Contextual stepping: if arg is not a value and steps (non-error),
    .throw arg steps with the result wrapped in .throw (·). -/
private theorem step?_throw_ctx (s : Flat.State) (arg : Flat.Expr)
    (hnotval : Flat.exprValue? arg = none)
    (t : Core.TraceEvent) (se : Flat.State)
    (hstep : Flat.step? { s with expr := arg } = some (t, se))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .throw arg } = some (t, s') ∧
      s'.expr = .throw se.expr ∧ s'.env = se.env ∧ s'.heap = se.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Context stepping: if init is not a value and steps (non-error),
    .let name init body steps with the result wrapped. -/
private theorem step?_let_init_ctx (s : Flat.State) (name : String) (init body : Flat.Expr)
    (hnotval : Flat.exprValue? init = none)
    (t : Core.TraceEvent) (si : Flat.State)
    (hstep : Flat.step? { s with expr := init } = some (t, si))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .«let» name init body } = some (t, s') ∧
      s'.expr = .«let» name si.expr body ∧ s'.env = si.env ∧ s'.heap = si.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Context stepping: if arg is not a value and steps (non-error),
    .unary op arg steps with the result wrapped. -/
private theorem step?_unary_ctx (s : Flat.State) (op : Core.UnaryOp) (arg : Flat.Expr)
    (hnotval : Flat.exprValue? arg = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := arg } = some (t, sa))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .unary op arg } = some (t, s') ∧
      s'.expr = .unary op sa.expr ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Context stepping: if lhs is not a value and steps (non-error),
    .binary op lhs rhs steps with the result wrapped. -/
private theorem step?_binary_lhs_ctx (s : Flat.State) (op : Core.BinOp) (lhs rhs : Flat.Expr)
    (hnotval : Flat.exprValue? lhs = none)
    (t : Core.TraceEvent) (sl : Flat.State)
    (hstep : Flat.step? { s with expr := lhs } = some (t, sl))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .binary op lhs rhs } = some (t, s') ∧
      s'.expr = .binary op sl.expr rhs ∧ s'.env = sl.env ∧ s'.heap = sl.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for seq: when inner step errors, seq propagates. -/
private theorem step?_seq_error (s : Flat.State) (a b : Flat.Expr)
    (hnotval : Flat.exprValue? a = none)
    (msg : String) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := a } = some (.error msg, sa)) :
    ∃ s', Flat.step? { s with expr := .seq a b } = some (.error msg, s') ∧
      s'.expr = .seq sa.expr b ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for let: when inner step errors, let propagates. -/
private theorem step?_let_init_error (s : Flat.State) (name : String) (init body : Flat.Expr)
    (hnotval : Flat.exprValue? init = none)
    (msg : String) (si : Flat.State)
    (hstep : Flat.step? { s with expr := init } = some (.error msg, si)) :
    ∃ s', Flat.step? { s with expr := .«let» name init body } = some (.error msg, s') ∧
      s'.expr = .«let» name si.expr body ∧ s'.env = si.env ∧ s'.heap = si.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for unary: when inner step errors, unary propagates. -/
private theorem step?_unary_error (s : Flat.State) (op : Core.UnaryOp) (arg : Flat.Expr)
    (hnotval : Flat.exprValue? arg = none)
    (msg : String) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := arg } = some (.error msg, sa)) :
    ∃ s', Flat.step? { s with expr := .unary op arg } = some (.error msg, s') ∧
      s'.expr = .unary op sa.expr ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for binary (lhs): when lhs step errors, binary propagates. -/
private theorem step?_binary_lhs_error (s : Flat.State) (op : Core.BinOp) (lhs rhs : Flat.Expr)
    (hnotval : Flat.exprValue? lhs = none)
    (msg : String) (sl : Flat.State)
    (hstep : Flat.step? { s with expr := lhs } = some (.error msg, sl)) :
    ∃ s', Flat.step? { s with expr := .binary op lhs rhs } = some (.error msg, s') ∧
      s'.expr = .binary op sl.expr rhs ∧ s'.env = sl.env ∧ s'.heap = sl.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for throw: when arg step errors, throw propagates. -/
private theorem step?_throw_error (s : Flat.State) (arg : Flat.Expr)
    (hnotval : Flat.exprValue? arg = none)
    (msg : String) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := arg } = some (.error msg, sa)) :
    ∃ s', Flat.step? { s with expr := .throw arg } = some (.error msg, s') ∧
      s'.expr = .throw sa.expr ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for return (some): when inner step errors, return propagates. -/
private theorem step?_return_some_error (s : Flat.State) (e : Flat.Expr)
    (hnotval : Flat.exprValue? e = none)
    (msg : String) (se : Flat.State)
    (hstep : Flat.step? { s with expr := e } = some (.error msg, se)) :
    ∃ s', Flat.step? { s with expr := .«return» (some e) } = some (.error msg, s') ∧
      s'.expr = .«return» (some se.expr) ∧ s'.env = se.env ∧ s'.heap = se.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for yield (some): when inner step errors, yield propagates. -/
private theorem step?_yield_some_error (s : Flat.State) (e : Flat.Expr) (delegate : Bool)
    (hnotval : Flat.exprValue? e = none)
    (msg : String) (se : Flat.State)
    (hstep : Flat.step? { s with expr := e } = some (.error msg, se)) :
    ∃ s', Flat.step? { s with expr := .yield (some e) delegate } = some (.error msg, s') ∧
      s'.expr = .yield (some se.expr) delegate ∧ s'.env = se.env ∧ s'.heap = se.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for await: when inner step errors, await propagates. -/
private theorem step?_await_error (s : Flat.State) (e : Flat.Expr)
    (hnotval : Flat.exprValue? e = none)
    (msg : String) (se : Flat.State)
    (hstep : Flat.step? { s with expr := e } = some (.error msg, se)) :
    ∃ s', Flat.step? { s with expr := .await e } = some (.error msg, s') ∧
      s'.expr = .await se.expr ∧ s'.env = se.env ∧ s'.heap = se.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Error propagation for if: when cond step errors, if propagates. -/
private theorem step?_if_cond_error (s : Flat.State) (cond then_ else_ : Flat.Expr)
    (hnotval : Flat.exprValue? cond = none)
    (msg : String) (sc : Flat.State)
    (hstep : Flat.step? { s with expr := cond } = some (.error msg, sc)) :
    ∃ s', Flat.step? { s with expr := .«if» cond then_ else_ } = some (.error msg, s') ∧
      s'.expr = .«if» sc.expr then_ else_ ∧ s'.env = sc.env ∧ s'.heap = sc.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [.error msg] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Stepping .if with a literal condition branches directly. -/
private theorem step?_if_lit_branch (s : Flat.State) (v : Flat.Value)
    (then_ else_ : Flat.Expr) :
    ∃ s', Flat.step? { s with expr := .«if» (.lit v) then_ else_ } = some (.silent, s') ∧
      s'.expr = (if Flat.toBoolean v then then_ else else_) ∧
      s'.env = s.env ∧ s'.heap = s.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [Core.TraceEvent.silent] := by
  simp only [Flat.step?, Flat.exprValue?]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Build left-associated seq spine: wrapSeqCtx e [a,b,c] = .seq (.seq (.seq e a) b) c -/
private def wrapSeqCtx (inner : Flat.Expr) : List Flat.Expr → Flat.Expr
  | [] => inner
  | r :: rs => wrapSeqCtx (.seq inner r) rs

/-- Lift a single Flat step through N layers of left-seq context. -/
private theorem step_wrapSeqCtx (s : Flat.State) (t : Core.TraceEvent)
    (ctx : List Flat.Expr) (hnoerr : ∀ msg, t ≠ .error msg) :
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
      step?_seq_ctx s inner r hnotval t s_inner hstep hnoerr
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

/-- Evaluating .if (.var name) then_ else_ when name is bound: two steps (lookup + branch). -/
private theorem steps_if_var_branch (sf : Flat.State) (name : String) (val : Flat.Value)
    (then_ else_ : Flat.Expr)
    (hval : sf.env.lookup name = some val) :
    ∃ (sf' : Flat.State),
      Flat.Steps { sf with expr := .«if» (.var name) then_ else_ }
        [.silent, .silent] sf' ∧
      sf'.expr = (if Flat.toBoolean val then then_ else else_) ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.trace = sf.trace ++ [.silent, .silent] := by
  -- Step 1: resolve .var name inside .if context
  obtain ⟨s_var, hstep_var, hexpr_var, henv_var, hheap_var, hf_var, hc_var, ht_var⟩ :=
    step?_var_bound sf name val hval
  have hnotval : Flat.exprValue? (Flat.Expr.var name) = none := by simp [Flat.exprValue?]
  obtain ⟨s1, hs1, he1, henv1, hheap1, hf1, hc1, ht1⟩ :=
    step?_if_cond_step sf (.var name) then_ else_ hnotval .silent s_var hstep_var (fun _ h => nomatch h)
  -- s1.expr = .if (.lit val) then_ else_
  have hs1_expr : s1.expr = .«if» (.lit val) then_ else_ := by rw [he1, hexpr_var]
  -- Step 2: branch
  obtain ⟨s2, hs2, he2, henv2, hheap2, hf2, hc2, ht2⟩ :=
    step?_if_lit_branch s1 val then_ else_
  have hs2' : Flat.step? s1 = some (.silent, s2) := by
    have : s1 = { s1 with expr := .«if» (.lit val) then_ else_ } := by
      cases s1; simp_all
    rw [this]; exact hs2
  exact ⟨s2,
    .tail ⟨hs1⟩ (.tail ⟨hs2'⟩ (.refl _)),
    he2,
    by rw [henv2, henv1, henv_var],
    by rw [hheap2, hheap1, hheap_var],
    by rw [ht2, ht1]; simp [List.append_assoc]⟩

/-- Evaluating .if (.lit v) then_ else_: one step (branch). -/
private theorem steps_if_lit_branch (sf : Flat.State) (v : Flat.Value)
    (then_ else_ : Flat.Expr) :
    ∃ (sf' : Flat.State),
      Flat.Steps { sf with expr := .«if» (.lit v) then_ else_ }
        [.silent] sf' ∧
      sf'.expr = (if Flat.toBoolean v then then_ else else_) ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.trace = sf.trace ++ [.silent] := by
  obtain ⟨s', hstep, hexpr, henv, hheap, _, _, htrace⟩ :=
    step?_if_lit_branch sf v then_ else_
  exact ⟨s', .tail ⟨hstep⟩ (.refl _), hexpr, henv, hheap, htrace⟩

/-- Evaluating .if .this then_ else_: two steps (resolve this + branch). -/
private theorem steps_if_this_branch (sf : Flat.State)
    (then_ else_ : Flat.Expr) :
    ∃ (val : Flat.Value) (sf' : Flat.State),
      Flat.Steps { sf with expr := .«if» .this then_ else_ }
        [.silent, .silent] sf' ∧
      sf'.expr = (if Flat.toBoolean val then then_ else else_) ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.trace = sf.trace ++ [.silent, .silent] := by
  obtain ⟨val, s_this, hstep_this, hexpr_this, henv_this, hheap_this, hf_this, hc_this, ht_this⟩ :=
    step?_this_resolve sf
  have hnotval : Flat.exprValue? Flat.Expr.this = none := by simp [Flat.exprValue?]
  obtain ⟨s1, hs1, he1, henv1, hheap1, hf1, hc1, ht1⟩ :=
    step?_if_cond_step sf .this then_ else_ hnotval .silent s_this hstep_this (fun _ h => nomatch h)
  have hs1_expr : s1.expr = .«if» (.lit val) then_ else_ := by rw [he1, hexpr_this]
  obtain ⟨s2, hs2, he2, henv2, hheap2, hf2, hc2, ht2⟩ :=
    step?_if_lit_branch s1 val then_ else_
  have hs2' : Flat.step? s1 = some (.silent, s2) := by
    have : s1 = { s1 with expr := .«if» (.lit val) then_ else_ } := by
      cases s1; simp_all
    rw [this]; exact hs2
  exact ⟨val, s2,
    .tail ⟨hs1⟩ (.tail ⟨hs2'⟩ (.refl _)),
    he2,
    by rw [henv2, henv1, henv_this],
    by rw [hheap2, hheap1, hheap_this],
    by rw [ht2, ht1]; simp [List.append_assoc]⟩

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
        step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) _ s_i hnotval hstep_i hfuncs_i hcs_i htrace_i
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
        step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) _ s_i hnotval hstep_i hfuncs_i hcs_i htrace_i
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
        step_wrapSeqCtx sf .silent ctx (fun _ h => nomatch h) _ s_v hnotval_v hstep_v hfuncs_v hcs_v htrace_v
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
        step_wrapSeqCtx sf .silent ctx (fun _ h => nomatch h) _ s_t hnotval_t hstep_t hfuncs_t hcs_t htrace_t
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

/-- If normalizeExpr e k produces .if (.var name) at the top level, and k only produces
    .if (.var name) when the argument is .var name, then VarFreeIn name e.
    Uses Classical.em to handle seq/compound cases where the continuation ignores its argument.
    Proved by strong mutual induction on depth. -/
private theorem normalizeExpr_if_cond_source :
    ∀ (d : Nat),
      (∀ (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr),
        e.depth ≤ d →
        ∀ n m (name : ANF.VarName) (then_ else_ : ANF.Expr),
        (∀ (arg : ANF.Trivial) (n' m' : Nat) (t' e' : ANF.Expr),
           (k arg).run n' = .ok (.if (.var name) t' e', m') → arg = .var name) →
        (ANF.normalizeExpr e k).run n = .ok (.if (.var name) then_ else_, m) →
        VarFreeIn name e) ∧
      (∀ (es : List Flat.Expr) (k : List ANF.Trivial → ANF.ConvM ANF.Expr),
        Flat.Expr.listDepth es ≤ d →
        ∀ n m (name : ANF.VarName) (then_ else_ : ANF.Expr),
        (∀ (args : List ANF.Trivial) (n' m' : Nat) (t' e' : ANF.Expr),
           (k args).run n' ≠ .ok (.if (.var name) t' e', m')) →
        (ANF.normalizeExprList es k).run n = .ok (.if (.var name) then_ else_, m) →
        ∃ e ∈ es, VarFreeIn name e) ∧
      (∀ (ps : List (Flat.PropName × Flat.Expr)) (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr),
        Flat.Expr.propListDepth ps ≤ d →
        ∀ n m (name : ANF.VarName) (then_ else_ : ANF.Expr),
        (∀ (args : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat) (t' e' : ANF.Expr),
           (k args).run n' ≠ .ok (.if (.var name) t' e', m')) →
        (ANF.normalizeProps ps k).run n = .ok (.if (.var name) then_ else_, m) →
        ∃ p ∈ ps, VarFreeIn name p.2)
    := by
  intro d; induction d with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e k hd n m name then_ else_ hk_cond hnorm
      cases e with
      | var vname =>
        simp only [ANF.normalizeExpr] at hnorm
        have := ANF.Trivial.var.inj (hk_cond (.var vname) n m then_ else_ hnorm)
        subst this; exact .var _
      | this =>
        simp only [ANF.normalizeExpr] at hnorm
        have := ANF.Trivial.var.inj (hk_cond (.var "this") n m then_ else_ hnorm)
        subst this; exact .this_var
      | lit v =>
        exfalso; simp only [ANF.normalizeExpr] at hnorm
        rw [trivialOfFlatValue_eq_trivialOfValue] at hnorm
        exact absurd (hk_cond _ n m then_ else_ hnorm) (ANF.trivialOfValue_ne_var v name)
      | «break» _ =>
        exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
        exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | «continue» _ =>
        exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
        exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | «return» arg =>
        cases arg with
        | none =>
          exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        | some _ => exfalso; simp [Flat.Expr.depth] at hd
      | yield arg _ =>
        cases arg with
        | none =>
          exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        | some _ => exfalso; simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => exfalso; cases fin <;> simp [Flat.Expr.depth] at hd
      | _ => exfalso; simp [Flat.Expr.depth] at hd
    · intro es k hd n m name then_ else_ hk hnorm
      cases es with
      | nil => simp only [ANF.normalizeExprList] at hnorm; exact absurd hnorm (hk [] n m then_ else_)
      | cons _ _ => exfalso; simp [Flat.Expr.listDepth] at hd
    · intro ps k hd n m name then_ else_ hk hnorm
      cases ps with
      | nil => simp only [ANF.normalizeProps] at hnorm; exact absurd hnorm (hk [] n m then_ else_)
      | cons _ _ => exfalso; simp [Flat.Expr.propListDepth] at hd
  | succ d ih =>
    obtain ⟨ihe, ihes, ihps⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro e k hd n m name then_ else_ hk_cond hnorm
      cases e with
      | var vname =>
        simp only [ANF.normalizeExpr] at hnorm
        have := ANF.Trivial.var.inj (hk_cond (.var vname) n m then_ else_ hnorm)
        subst this; exact .var _
      | this =>
        simp only [ANF.normalizeExpr] at hnorm
        have := ANF.Trivial.var.inj (hk_cond (.var "this") n m then_ else_ hnorm)
        subst this; exact .this_var
      | lit v =>
        exfalso; simp only [ANF.normalizeExpr] at hnorm
        rw [trivialOfFlatValue_eq_trivialOfValue] at hnorm
        exact absurd (hk_cond _ n m then_ else_ hnorm) (ANF.trivialOfValue_ne_var v name)
      | «break» _ =>
        exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
        exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | «continue» _ =>
        exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
        exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | labeled label body =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
        revert hnorm; split
        · intro h; simp [Except.ok.injEq, Prod.mk.injEq] at h
        · intro h; exact absurd h (by simp)
      | while_ cond body =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
        repeat (first | split at hnorm | simp at hnorm | exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1)
      | tryCatch body₁ catchParam catchBody finally_ =>
        exfalso; unfold ANF.normalizeExpr at hnorm
        simp only [bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map, StateT.run] at hnorm
        cases finally_ with
        | none =>
          simp only [bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
          repeat (first | split at hnorm | simp at hnorm | exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1)
        | some fin =>
          simp only [bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map, StateT.run] at hnorm
          repeat (first | split at hnorm | simp at hnorm | exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1)
      | «return» arg =>
        cases arg with
        | none =>
          exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        | some value =>
          simp only [ANF.normalizeExpr] at hnorm
          exact .return_some_arg _ _ (ihe value (fun t => pure (.return (some t)))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro arg n' m' t' e' habs
                exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
            hnorm)
      | yield arg delegate =>
        cases arg with
        | none =>
          exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        | some value =>
          simp only [ANF.normalizeExpr] at hnorm
          exact .yield_some_arg _ _ delegate (ihe value (fun t => pure (.yield (some t) delegate))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro arg n' m' t' e' habs
                exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
            hnorm)
      | throw arg =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .throw_arg _ _ (ihe arg (fun t => pure (.throw t))
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
          hnorm)
      | await arg =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .await_arg _ _ (ihe arg (fun t => pure (.await t))
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj habs)).1)
          hnorm)
      | «if» cond then₁ else₁ =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .if_cond _ _ _ _ (ihe cond (fun condTriv => do
            let thenExpr ← ANF.normalizeExpr then₁ k
            let elseExpr ← ANF.normalizeExpr else₁ k
            pure (.if condTriv thenExpr elseExpr))
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro condTriv n' m' t' e' habs
              revert habs
              simp only [bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure, StateT.pure, Except.pure, StateT.run]
              intro habs
              revert habs; split
              · intro h; exact absurd h (by simp)
              · split
                · intro h; exact absurd h (by simp)
                · simp only [Except.ok.injEq, Prod.mk.injEq, ANF.Expr.if.injEq, and_imp]
                  intro h _ _ _; exact h)
          hnorm)
      | seq a b =>
        simp only [ANF.normalizeExpr] at hnorm
        rcases Classical.em (∃ (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExpr b k).run n₁ = .ok (.if (.var name) t₁ e₁, m₁))
          with ⟨n₁, m₁, t₁, e₁, hb⟩ | hno
        · exact .seq_r _ _ _ (ihe b k
            (by simp [Flat.Expr.depth] at hd; omega) n₁ m₁ name t₁ e₁ hk_cond hb)
        · exact .seq_l _ _ _ (ihe a (fun _ => ANF.normalizeExpr b k)
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro arg n' m' t' e' habs; exact absurd ⟨n', m', t', e', habs⟩ hno)
            hnorm)
      | «let» name₁ init body =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .let_init _ _ _ _ (ihe init (fun initTriv => do
            let bodyExpr ← ANF.normalizeExpr body k
            pure (.let name₁ (.trivial initTriv) bodyExpr))
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              revert habs
              simp only [bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure, StateT.pure, Except.pure, StateT.run]
              intro habs
              revert habs; split
              · intro h; exact absurd h (by simp)
              · simp [Except.ok.injEq, Prod.mk.injEq])
          hnorm)
      | assign name₂ value =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .assign_value _ _ _ (ihe value (fun vt => ANF.bindComplex (.assign name₂ vt) k)
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact absurd habs (bindComplex_not_if _ k n' m' (.var name) t' e'))
          hnorm)
      | unary op arg =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .unary_arg _ _ _ (ihe arg (fun at_ => ANF.bindComplex (.unary op at_) k)
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact absurd habs (bindComplex_not_if _ k n' m' (.var name) t' e'))
          hnorm)
      | typeof arg =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .typeof_arg _ _ (ihe arg (fun at_ => ANF.bindComplex (.typeof at_) k)
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact absurd habs (bindComplex_not_if _ k n' m' (.var name) t' e'))
          hnorm)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .getProp_obj _ _ _ (ihe obj (fun ot => ANF.bindComplex (.getProp ot prop) k)
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact absurd habs (bindComplex_not_if _ k n' m' (.var name) t' e'))
          hnorm)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .deleteProp_obj _ _ _ (ihe obj (fun ot => ANF.bindComplex (.deleteProp ot prop) k)
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact absurd habs (bindComplex_not_if _ k n' m' (.var name) t' e'))
          hnorm)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .getEnv_env _ _ _ (ihe envPtr (fun et => ANF.bindComplex (.getEnv et idx) k)
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact absurd habs (bindComplex_not_if _ k n' m' (.var name) t' e'))
          hnorm)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at hnorm
        exact .makeClosure_env _ _ _ (ihe env (fun et => ANF.bindComplex (.makeClosure funcIdx et) k)
          (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
          (by intro arg n' m' t' e' habs
              exact absurd habs (bindComplex_not_if _ k n' m' (.var name) t' e'))
          hnorm)
      | setProp obj prop value =>
        simp only [ANF.normalizeExpr] at hnorm
        rcases Classical.em (∃ (arg : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setProp arg prop vt) k)).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨arg, n₁, m₁, t₁, e₁, hinner⟩ | hno
        · exact .setProp_value _ _ _ _ (ihe value (fun vt => ANF.bindComplex (.setProp arg prop vt) k)
            (by simp [Flat.Expr.depth] at hd; omega) n₁ m₁ name t₁ e₁
            (by intro a n' m' t' e' h; exact absurd h (bindComplex_not_if _ k n' m' (.var name) t' e'))
            hinner)
        · exact .setProp_obj _ _ _ _ (ihe obj
            (fun ot => ANF.normalizeExpr value (fun vt => ANF.bindComplex (.setProp ot prop vt) k))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno)
            hnorm)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at hnorm
        rcases Classical.em (∃ (arg : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExpr idx (fun it => ANF.bindComplex (.getIndex arg it) k)).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨arg, n₁, m₁, t₁, e₁, hinner⟩ | hno
        · exact .getIndex_idx _ _ _ (ihe idx (fun it => ANF.bindComplex (.getIndex arg it) k)
            (by simp [Flat.Expr.depth] at hd; omega) n₁ m₁ name t₁ e₁
            (by intro a n' m' t' e' h; exact absurd h (bindComplex_not_if _ k n' m' (.var name) t' e'))
            hinner)
        · exact .getIndex_obj _ _ _ (ihe obj
            (fun ot => ANF.normalizeExpr idx (fun it => ANF.bindComplex (.getIndex ot it) k))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno)
            hnorm)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at hnorm
        rcases Classical.em (∃ (arg : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExpr rhs (fun rt => ANF.bindComplex (.binary op arg rt) k)).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨arg, n₁, m₁, t₁, e₁, hinner⟩ | hno
        · exact .binary_rhs _ _ _ _ (ihe rhs (fun rt => ANF.bindComplex (.binary op arg rt) k)
            (by simp [Flat.Expr.depth] at hd; omega) n₁ m₁ name t₁ e₁
            (by intro a n' m' t' e' h; exact absurd h (bindComplex_not_if _ k n' m' (.var name) t' e'))
            hinner)
        · exact .binary_lhs _ _ _ _ (ihe lhs
            (fun lt => ANF.normalizeExpr rhs (fun rt => ANF.bindComplex (.binary op lt rt) k))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno)
            hnorm)
      | setIndex obj idx value =>
        simp only [ANF.normalizeExpr] at hnorm
        rcases Classical.em (∃ (a₁ : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExpr idx (fun it => ANF.normalizeExpr value
            (fun vt => ANF.bindComplex (.setIndex a₁ it vt) k))).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨a₁, n₁, m₁, t₁, e₁, h₁⟩ | hno₁
        · rcases Classical.em (∃ (a₂ : ANF.Trivial) (n₂ m₂ : Nat) (t₂ e₂ : ANF.Expr),
            (ANF.normalizeExpr value
              (fun vt => ANF.bindComplex (.setIndex a₁ a₂ vt) k)).run n₂ =
              .ok (.if (.var name) t₂ e₂, m₂)) with ⟨a₂, n₂, m₂, t₂, e₂, h₂⟩ | hno₂
          · exact .setIndex_value _ _ _ _ (ihe value
              (fun vt => ANF.bindComplex (.setIndex a₁ a₂ vt) k)
              (by simp [Flat.Expr.depth] at hd; omega) n₂ m₂ name t₂ e₂
              (by intro a n' m' t' e' h
                  exact absurd h (bindComplex_not_if _ k n' m' (.var name) t' e'))
              h₂)
          · exact .setIndex_idx _ _ _ _ (ihe idx
              (fun it => ANF.normalizeExpr value
                (fun vt => ANF.bindComplex (.setIndex a₁ it vt) k))
              (by simp [Flat.Expr.depth] at hd; omega) n₁ m₁ name t₁ e₁
              (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno₂)
              h₁)
        · exact .setIndex_obj _ _ _ _ (ihe obj
            (fun ot => ANF.normalizeExpr idx (fun it => ANF.normalizeExpr value
              (fun vt => ANF.bindComplex (.setIndex ot it vt) k)))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno₁)
            hnorm)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at hnorm
        obtain ⟨v, hv_mem, hv_free⟩ := ihes values (fun vts => ANF.bindComplex (.makeEnv vts) k)
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd; omega) n m name then_ else_
          (by intro args n' m' t' e'; exact bindComplex_not_if _ k n' m' (.var name) t' e')
          hnorm
        exact .makeEnv_elem _ _ _ hv_mem hv_free
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at hnorm
        obtain ⟨v, hv_mem, hv_free⟩ := ihes elems (fun ets => ANF.bindComplex (.arrayLit ets) k)
          (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd; omega) n m name then_ else_
          (by intro args n' m' t' e'; exact bindComplex_not_if _ k n' m' (.var name) t' e')
          hnorm
        exact .arrayLit_elem _ _ _ hv_mem hv_free
      | objectLit props =>
        simp only [ANF.normalizeExpr] at hnorm
        obtain ⟨p, hp_mem, hp_free⟩ := ihps props (fun pts => ANF.bindComplex (.objectLit pts) k)
          (by simp [Flat.Expr.depth, Flat.Expr.propListDepth] at hd; omega) n m name then_ else_
          (by intro args n' m' t' e'; exact bindComplex_not_if _ k n' m' (.var name) t' e')
          hnorm
        exact .objectLit_value _ _ _ hp_mem hp_free
      | call funcIdx envPtr args =>
        simp only [ANF.normalizeExpr] at hnorm
        rcases Classical.em (∃ (ft : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExpr envPtr (fun et =>
            ANF.normalizeExprList args (fun ats =>
              ANF.bindComplex (.call ft et ats) k))).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨ft, n₁, m₁, t₁, e₁, h₁⟩ | hno₁
        · rcases Classical.em (∃ (et : ANF.Trivial) (n₂ m₂ : Nat) (t₂ e₂ : ANF.Expr),
            (ANF.normalizeExprList args (fun ats =>
              ANF.bindComplex (.call ft et ats) k)).run n₂ =
              .ok (.if (.var name) t₂ e₂, m₂)) with ⟨et, n₂, m₂, t₂, e₂, h₂⟩ | hno₂
          · obtain ⟨a, ha_mem, ha_free⟩ := ihes args
              (fun ats => ANF.bindComplex (.call ft et ats) k)
              (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd; omega) n₂ m₂ name t₂ e₂
              (by intro ats n' m' t' e'; exact bindComplex_not_if _ k n' m' (.var name) t' e')
              h₂
            exact .call_arg _ _ _ _ _ ha_mem ha_free
          · exact .call_env _ _ _ _ (ihe envPtr
              (fun et => ANF.normalizeExprList args (fun ats =>
                ANF.bindComplex (.call ft et ats) k))
              (by simp [Flat.Expr.depth] at hd; omega) n₁ m₁ name t₁ e₁
              (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno₂)
              h₁)
        · exact .call_func _ _ _ _ (ihe funcIdx
            (fun ft => ANF.normalizeExpr envPtr (fun et =>
              ANF.normalizeExprList args (fun ats =>
                ANF.bindComplex (.call ft et ats) k)))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno₁)
            hnorm)
      | newObj funcIdx envPtr args =>
        simp only [ANF.normalizeExpr] at hnorm
        rcases Classical.em (∃ (ft : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExpr envPtr (fun et =>
            ANF.normalizeExprList args (fun ats =>
              ANF.bindComplex (.newObj ft et ats) k))).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨ft, n₁, m₁, t₁, e₁, h₁⟩ | hno₁
        · rcases Classical.em (∃ (et : ANF.Trivial) (n₂ m₂ : Nat) (t₂ e₂ : ANF.Expr),
            (ANF.normalizeExprList args (fun ats =>
              ANF.bindComplex (.newObj ft et ats) k)).run n₂ =
              .ok (.if (.var name) t₂ e₂, m₂)) with ⟨et, n₂, m₂, t₂, e₂, h₂⟩ | hno₂
          · obtain ⟨a, ha_mem, ha_free⟩ := ihes args
              (fun ats => ANF.bindComplex (.newObj ft et ats) k)
              (by simp [Flat.Expr.depth, Flat.Expr.listDepth] at hd; omega) n₂ m₂ name t₂ e₂
              (by intro ats n' m' t' e'; exact bindComplex_not_if _ k n' m' (.var name) t' e')
              h₂
            exact .newObj_arg _ _ _ _ _ ha_mem ha_free
          · exact .newObj_env _ _ _ _ (ihe envPtr
              (fun et => ANF.normalizeExprList args (fun ats =>
                ANF.bindComplex (.newObj ft et ats) k))
              (by simp [Flat.Expr.depth] at hd; omega) n₁ m₁ name t₁ e₁
              (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno₂)
              h₁)
        · exact .newObj_func _ _ _ _ (ihe funcIdx
            (fun ft => ANF.normalizeExpr envPtr (fun et =>
              ANF.normalizeExprList args (fun ats =>
                ANF.bindComplex (.newObj ft et ats) k)))
            (by simp [Flat.Expr.depth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno₁)
            hnorm)
    · intro es k hd n m name then_ else_ hk hnorm
      cases es with
      | nil => simp only [ANF.normalizeExprList] at hnorm; exact absurd hnorm (hk [] n m then_ else_)
      | cons e rest =>
        simp only [ANF.normalizeExprList] at hnorm
        rcases Classical.em (∃ (arg : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeExprList rest (fun ts => k (arg :: ts))).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨arg, n₁, m₁, t₁, e₁, hinner⟩ | hno
        · obtain ⟨elem, hmem, hfree⟩ := ihes rest (fun ts => k (arg :: ts))
            (by simp [Flat.Expr.listDepth] at hd; omega) n₁ m₁ name t₁ e₁
            (by intro args n' m' t' e'; exact hk (arg :: args) n' m' t' e')
            hinner
          exact ⟨elem, List.mem_cons_of_mem _ hmem, hfree⟩
        · exact ⟨e, @List.mem_cons_self _ e rest, ihe e
            (fun t => ANF.normalizeExprList rest (fun ts => k (t :: ts)))
            (by simp [Flat.Expr.listDepth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno)
            hnorm⟩
    · intro ps k hd n m name then_ else_ hk hnorm
      cases ps with
      | nil => simp only [ANF.normalizeProps] at hnorm; exact absurd hnorm (hk [] n m then_ else_)
      | cons p rest =>
        obtain ⟨pn, pe⟩ := p
        simp only [ANF.normalizeProps] at hnorm
        rcases Classical.em (∃ (arg : ANF.Trivial) (n₁ m₁ : Nat) (t₁ e₁ : ANF.Expr),
          (ANF.normalizeProps rest (fun pts => k ((pn, arg) :: pts))).run n₁ =
            .ok (.if (.var name) t₁ e₁, m₁)) with ⟨arg, n₁, m₁, t₁, e₁, hinner⟩ | hno
        · obtain ⟨elem, hmem, hfree⟩ := ihps rest (fun pts => k ((pn, arg) :: pts))
            (by simp [Flat.Expr.propListDepth] at hd; omega) n₁ m₁ name t₁ e₁
            (by intro args n' m' t' e'; exact hk ((pn, arg) :: args) n' m' t' e')
            hinner
          exact ⟨elem, List.mem_cons_of_mem _ hmem, hfree⟩
        · exact ⟨(pn, pe), @List.mem_cons_self _ (pn, pe) rest, ihe pe
            (fun vt => ANF.normalizeProps rest (fun pts => k ((pn, vt) :: pts)))
            (by simp [Flat.Expr.propListDepth] at hd; omega) n m name then_ else_
            (by intro a n' m' t' e' h; exact absurd ⟨a, n', m', t', e', h⟩ hno)
            hnorm⟩

/-- When normalizeExpr e k produces .if (.var name) with k trivial-preserving,
    the variable name is free in e. Since k only produces .trivial (never .if),
    the .if must come from e. -/
private theorem normalizeExpr_if_cond_var_free
    (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (name : ANF.VarName) (then_ else_ : ANF.Expr)
    (hk : ∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (.if (.var name) then_ else_, m)) :
    VarFreeIn name e := by
  have hk_cond : ∀ (arg : ANF.Trivial) (n' m' : Nat) (t' e' : ANF.Expr),
      (k arg).run n' = .ok (.if (.var name) t' e', m') → arg = .var name := by
    intro arg n' m' t' e' habs
    obtain ⟨m'', hk''⟩ := hk arg n'
    rw [hk''] at habs
    exact absurd habs (by intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1)
  exact (normalizeExpr_if_cond_source d).1 e k hd n m name then_ else_ hk_cond hnorm

/-- When normalizeExpr e k produces .trivial (.var name) with k trivial-preserving,
    the variable name (or "this") is free in e. This is used to derive a contradiction
    in the var-not-found case via ExprWellFormed. -/
private theorem normalizeExpr_var_implies_free :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat) (name : ANF.VarName),
    (∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m')) →
    (ANF.normalizeExpr e k).run n = .ok (.trivial (.var name), m) →
    VarFreeIn name e := by
  intro d; induction d with
  | zero =>
    intro e hd k n m name hk hnorm
    cases e with
    | var vname =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var vname) n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq; exact .var name
    | this =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var "this") n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq; exact .this_var
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
    intro e hd k n m name hk hnorm
    cases e with
    | var vname =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var vname) n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq; exact .var name
    | this =>
      simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hk'⟩ := hk (.var "this") n
      have hname_eq := hnorm.symm.trans hk' |> Except.ok.inj |> Prod.mk.inj |>.1
        |> ANF.Expr.trivial.inj |> ANF.Trivial.var.inj
      subst hname_eq; exact .this_var
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
      have hdb : b.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      have hb_norm : (ANF.normalizeExpr b k).run n = .ok (.trivial (.var name), m) :=
        normalizeExpr_ignored_bypass_trivial d a (by simp [Flat.Expr.depth] at hd; omega) _ n m _ hnorm
      exact .seq_r _ _ _ (ih b hdb k n m name hk hb_norm)
    | _ => exfalso; exact absurd hnorm (normalizeExpr_compound_not_trivial _ k
        (by intro v hc; exact Flat.Expr.noConfusion hc) (by intro nm hc; exact Flat.Expr.noConfusion hc)
        (by intro hc; exact Flat.Expr.noConfusion hc) (by intro a' b' hc; exact Flat.Expr.noConfusion hc) n m _)

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


/-\! ### ANF Inversion Infrastructure (inlined from ANFInversion.lean) -/

/-! # Part 1: Break Inversion -/

/-! ## bindComplex never produces .break -/

/-- bindComplex always wraps its result in .let, so it can NEVER produce .break,
    regardless of what k does. -/
theorem ANF.bindComplex_never_break_general (rhs : ANF.ComplexExpr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.bindComplex rhs k).run n = .ok (.break label, m)) : False := by
  unfold ANF.bindComplex at h
  unfold ANF.freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure,
    StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-! ## Wrapping constructors NEVER produce .break -/

/-- normalizeExpr (.labeled l body) k never produces .break — result is always .labeled -/
theorem ANF.normalizeExpr_labeled_not_break (l : Flat.LabelName) (body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr (.labeled l body) k).run n = .ok (.break label, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    pure, Pure.pure, StateT.pure, Except.pure, Except.bind] at h
  split at h <;> simp_all

/-- normalizeExpr (.while_ cond body) k never produces .break — result is always .seq -/
theorem ANF.normalizeExpr_while_not_break (cond_ body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr (.while_ cond_ body) k).run n = .ok (.break label, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    pure, Pure.pure, StateT.pure, Except.pure, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-- normalizeExpr (.tryCatch body cp cb fin) k never produces .break — always .tryCatch -/
theorem ANF.normalizeExpr_tryCatch_not_break (body : Flat.Expr) (cp : Flat.VarName)
    (cb : Flat.Expr) (fin : Option Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr (.tryCatch body cp cb fin) k).run n = .ok (.break label, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    pure, Pure.pure, StateT.pure, Except.pure, Except.bind,
    Functor.map, StateT.map, Except.map] at h
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h
  · simp only [Except.bind, Functor.map, StateT.map, StateT.bind, StateT.run,
      bind, Bind.bind, Except.map, pure, Pure.pure, StateT.pure, Except.pure] at h
    split at h
    · nomatch h
    · exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
  · simp only [StateT.bind, StateT.pure, Except.bind, Except.pure,
      pure, Pure.pure, bind, Bind.bind] at h
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-! ## HasBreakInHead mutual inductive -/

set_option autoImplicit true in
mutual
/-- An expression has .break label reachable through normalizeExpr's CPS evaluation path. -/
inductive HasBreakInHead : Flat.Expr → Option Flat.LabelName → Prop where
  | break_direct : HasBreakInHead (.break label) label
  | seq_left : HasBreakInHead a label → HasBreakInHead (.seq a b) label
  | seq_right : HasBreakInHead b label → HasBreakInHead (.seq a b) label
  | let_init : HasBreakInHead init label → HasBreakInHead (.let name init body) label
  | getProp_obj : HasBreakInHead obj label → HasBreakInHead (.getProp obj prop) label
  | setProp_obj : HasBreakInHead obj label → HasBreakInHead (.setProp obj prop val) label
  | setProp_val : HasBreakInHead val label → HasBreakInHead (.setProp obj prop val) label
  | binary_lhs : HasBreakInHead lhs label → HasBreakInHead (.binary op lhs rhs) label
  | binary_rhs : HasBreakInHead rhs label → HasBreakInHead (.binary op lhs rhs) label
  | unary_arg : HasBreakInHead arg label → HasBreakInHead (.unary op arg) label
  | typeof_arg : HasBreakInHead arg label → HasBreakInHead (.typeof arg) label
  | deleteProp_obj : HasBreakInHead obj label → HasBreakInHead (.deleteProp obj prop) label
  | assign_val : HasBreakInHead val label → HasBreakInHead (.assign name val) label
  | call_func : HasBreakInHead f label → HasBreakInHead (.call f env args) label
  | call_env : HasBreakInHead env label → HasBreakInHead (.call f env args) label
  | call_args : HasBreakInHeadList args label → HasBreakInHead (.call f env args) label
  | newObj_func : HasBreakInHead f label → HasBreakInHead (.newObj f env args) label
  | newObj_env : HasBreakInHead env label → HasBreakInHead (.newObj f env args) label
  | newObj_args : HasBreakInHeadList args label → HasBreakInHead (.newObj f env args) label
  | if_cond : HasBreakInHead c label → HasBreakInHead (.if c t e) label
  | throw_arg : HasBreakInHead arg label → HasBreakInHead (.throw arg) label
  | return_some_arg : HasBreakInHead v label → HasBreakInHead (.return (some v)) label
  | yield_some_arg : HasBreakInHead v label → HasBreakInHead (.yield (some v) d) label
  | await_arg : HasBreakInHead arg label → HasBreakInHead (.await arg) label
  | getIndex_obj : HasBreakInHead obj label → HasBreakInHead (.getIndex obj idx) label
  | getIndex_idx : HasBreakInHead idx label → HasBreakInHead (.getIndex obj idx) label
  | setIndex_obj : HasBreakInHead obj label → HasBreakInHead (.setIndex obj idx val) label
  | setIndex_idx : HasBreakInHead idx label → HasBreakInHead (.setIndex obj idx val) label
  | setIndex_val : HasBreakInHead val label → HasBreakInHead (.setIndex obj idx val) label
  | getEnv_env : HasBreakInHead env label → HasBreakInHead (.getEnv env idx) label
  | makeClosure_env : HasBreakInHead env label → HasBreakInHead (.makeClosure funcIdx env) label
  | makeEnv_values : HasBreakInHeadList values label → HasBreakInHead (.makeEnv values) label
  | objectLit_props : HasBreakInHeadProps props label → HasBreakInHead (.objectLit props) label
  | arrayLit_elems : HasBreakInHeadList elems label → HasBreakInHead (.arrayLit elems) label

/-- HasBreakInHead for lists (some element has break in head) -/
inductive HasBreakInHeadList : List Flat.Expr → Option Flat.LabelName → Prop where
  | head : HasBreakInHead e label → HasBreakInHeadList (e :: rest) label
  | tail : HasBreakInHeadList rest label → HasBreakInHeadList (e :: rest) label

/-- HasBreakInHead for prop lists (some prop value has break in head) -/
inductive HasBreakInHeadProps : List (Flat.PropName × Flat.Expr) → Option Flat.LabelName → Prop where
  | head : HasBreakInHead e label → HasBreakInHeadProps ((name, e) :: rest) label
  | tail : HasBreakInHeadProps rest label → HasBreakInHeadProps (p :: rest) label
end

/-- HasBreakInHead expressions are never values. -/
private theorem HasBreakInHead_not_value (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label) : Flat.exprValue? e = none := by
  cases h <;> simp [Flat.exprValue?]

/-- Membership in prop list implies depth bound -/
theorem Flat.Expr.mem_propListDepth_lt {e : Flat.Expr} {name : Flat.PropName}
    {props : List (Flat.PropName × Flat.Expr)} (h : (name, e) ∈ props) :
    e.depth < Flat.Expr.propListDepth props := by
  induction props with
  | nil => simp at h
  | cons hd tl ih =>
    cases h with
    | head => simp [Flat.Expr.propListDepth]; omega
    | tail _ h => have := ih h; simp [Flat.Expr.propListDepth]; omega

/-! ## List break characterization helpers -/

/-- If normalizeExprList es k = .break, then either some element has break in head,
    or k was called and produced break. Parameterized by an IH for normalizeExpr. -/
theorem normalizeExprList_break_or_k
    (es : List Flat.Expr)
    (expr_ih : ∀ e, e ∈ es → ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat),
      (ANF.normalizeExpr e k).run n = .ok (.break label, m) →
      HasBreakInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.break label, m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (.break label, m)) :
    HasBreakInHeadList es label ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat), (k ts).run n' = .ok (.break label, m') := by
  induction es generalizing k label n m with
  | nil =>
    simp only [ANF.normalizeExprList] at h
    exact Or.inr ⟨[], n, m, h⟩
  | cons e rest ih_rest =>
    simp only [ANF.normalizeExprList] at h
    rcases expr_ih e (.head rest) _ _ _ _ h with hleft | ⟨t, n', m', hk⟩
    · exact Or.inl (HasBreakInHeadList.head hleft)
    · rcases ih_rest (fun e' he' => expr_ih e' (.tail e he')) _ _ _ _ hk with hleft | ⟨ts, n'', m'', hk'⟩
      · exact Or.inl (HasBreakInHeadList.tail hleft)
      · exact Or.inr ⟨t :: ts, n'', m'', hk'⟩

/-- If normalizeProps props k = .break, then either some prop value has break in head,
    or k was called and produced break. Parameterized by an IH for normalizeExpr. -/
theorem normalizeProps_break_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (expr_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat),
      (ANF.normalizeExpr e k).run n = .ok (.break label, m) →
      HasBreakInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.break label, m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (.break label, m)) :
    HasBreakInHeadProps props label ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat), (k ts).run n' = .ok (.break label, m') := by
  induction props generalizing k label n m with
  | nil =>
    simp only [ANF.normalizeProps] at h
    exact Or.inr ⟨[], n, m, h⟩
  | cons p rest ih_rest =>
    obtain ⟨name, value⟩ := p
    simp only [ANF.normalizeProps] at h
    rcases expr_ih name value (.head rest) _ _ _ _ h with hleft | ⟨t, n', m', hk⟩
    · exact Or.inl (HasBreakInHeadProps.head hleft)
    · rcases ih_rest (fun n' e' he' => expr_ih n' e' (.tail _ he')) _ _ _ _ hk with hleft | ⟨ts, n'', m'', hk'⟩
      · exact Or.inl (HasBreakInHeadProps.tail hleft)
      · exact Or.inr ⟨(name, t) :: ts, n'', m'', hk'⟩

/-! ## General break source characterization -/

/-- General break characterization: normalizeExpr e k = .break →
    e has break in CPS head position OR k was called and produced .break -/
theorem ANF.normalizeExpr_break_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.break label, m)) :
    HasBreakInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.break label, m') :=
  normalizeExpr_break_or_k_aux e.depth e (Nat.le_refl _) k label n m h
where
  /-- Helper: general break characterization by strong induction on expression depth. -/
  normalizeExpr_break_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (.break label, m)) :
      HasBreakInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.break label, m') := by
    induction d generalizing e k label n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        left; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        cases (Prod.mk.inj (Except.ok.inj h)).1; exact HasBreakInHead.break_direct
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «return» arg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg _ =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | «break» l =>
        left; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        cases (Prod.mk.inj (Except.ok.inj h)).1; exact HasBreakInHead.break_direct
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «return» arg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasBreakInHead.return_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | yield arg dlg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasBreakInHead.yield_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | throw arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.throw_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | await arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.await_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ _ h with hleft | ⟨_, n', m', hkb⟩
        · exact Or.inl (HasBreakInHead.seq_left hleft)
        · rcases ih b hb _ _ _ _ hkb with hleft | hright
          · exact Or.inl (HasBreakInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body =>
        exact absurd h (ANF.normalizeExpr_labeled_not_break l body k label n m)
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_break c b k label n m)
      | tryCatch body cp cb fin =>
        exact absurd h (ANF.normalizeExpr_tryCatch_not_break body cp cb fin k label n m)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ _ h with hleft | ⟨tv, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_never_break_general _ _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_break_general _ _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_break_general _ _ _ _ _)
      | typeof arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_break_general _ _ _ _ _)
      | unary op arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_break_general _ _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_break_general _ _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasBreakInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_break_general _ _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasBreakInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasBreakInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_break_general _ _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasBreakInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasBreakInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_break_general _ _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasBreakInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasBreakInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_break_general _ _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasBreakInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasBreakInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, hk₃⟩
            · exact Or.inl (HasBreakInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_break_general _ _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasBreakInHead.call_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasBreakInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' label n m,
                (ANF.normalizeExpr e k').run n = .ok (.break label, m) →
                HasBreakInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.break label, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_break_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasBreakInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_break_general _ _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasBreakInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasBreakInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' label n m,
                (ANF.normalizeExpr e k').run n = .ok (.break label, m) →
                HasBreakInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.break label, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_break_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasBreakInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_break_general _ _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' label n m,
            (ANF.normalizeExpr e k').run n = .ok (.break label, m) →
            HasBreakInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.break label, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_break_or_k values vals_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasBreakInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_never_break_general _ _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' label n m,
            (ANF.normalizeExpr e k').run n = .ok (.break label, m) →
            HasBreakInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.break label, m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_break_or_k props props_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasBreakInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_never_break_general _ _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' label n m,
            (ANF.normalizeExpr e k').run n = .ok (.break label, m) →
            HasBreakInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.break label, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_break_or_k elems elems_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasBreakInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_never_break_general _ _ _ _ _)

/-- MASTER INVERSION (break):
    If normalizeExpr e k = .ok (.break label, m) with trivial-preserving k,
    then e has .break label in evaluation-head position. -/
theorem ANF.normalizeExpr_break_implies_hasBreakInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.break label, m)) :
    HasBreakInHead e label := by
  rcases ANF.normalizeExpr_break_or_k e k label n m h with hleft | ⟨t, n', m', hk_break⟩
  · exact hleft
  · obtain ⟨m'', hm''⟩ := hk t n'
    rw [hm''] at hk_break
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_break)).1

/-! # Part 2: Labeled Inversion -/

/-! ## HasLabeledInHead mutual inductive -/

set_option autoImplicit true in
mutual
/-- An expression has .labeled label reachable through normalizeExpr's CPS evaluation path. -/
inductive HasLabeledInHead : Flat.Expr → String → Prop where
  | labeled_direct : HasLabeledInHead (.labeled label body) label
  | seq_left : HasLabeledInHead a label → HasLabeledInHead (.seq a b) label
  | seq_right : HasLabeledInHead b label → HasLabeledInHead (.seq a b) label
  | let_init : HasLabeledInHead init label → HasLabeledInHead (.let name init body) label
  | getProp_obj : HasLabeledInHead obj label → HasLabeledInHead (.getProp obj prop) label
  | setProp_obj : HasLabeledInHead obj label → HasLabeledInHead (.setProp obj prop val) label
  | setProp_val : HasLabeledInHead val label → HasLabeledInHead (.setProp obj prop val) label
  | binary_lhs : HasLabeledInHead lhs label → HasLabeledInHead (.binary op lhs rhs) label
  | binary_rhs : HasLabeledInHead rhs label → HasLabeledInHead (.binary op lhs rhs) label
  | unary_arg : HasLabeledInHead arg label → HasLabeledInHead (.unary op arg) label
  | typeof_arg : HasLabeledInHead arg label → HasLabeledInHead (.typeof arg) label
  | deleteProp_obj : HasLabeledInHead obj label → HasLabeledInHead (.deleteProp obj prop) label
  | assign_val : HasLabeledInHead val label → HasLabeledInHead (.assign name val) label
  | call_func : HasLabeledInHead f label → HasLabeledInHead (.call f env args) label
  | call_env : HasLabeledInHead env label → HasLabeledInHead (.call f env args) label
  | call_args : HasLabeledInHeadList args label → HasLabeledInHead (.call f env args) label
  | newObj_func : HasLabeledInHead f label → HasLabeledInHead (.newObj f env args) label
  | newObj_env : HasLabeledInHead env label → HasLabeledInHead (.newObj f env args) label
  | newObj_args : HasLabeledInHeadList args label → HasLabeledInHead (.newObj f env args) label
  | if_cond : HasLabeledInHead c label → HasLabeledInHead (.if c t e) label
  | throw_arg : HasLabeledInHead arg label → HasLabeledInHead (.throw arg) label
  | return_some_arg : HasLabeledInHead v label → HasLabeledInHead (.return (some v)) label
  | yield_some_arg : HasLabeledInHead v label → HasLabeledInHead (.yield (some v) d) label
  | await_arg : HasLabeledInHead arg label → HasLabeledInHead (.await arg) label
  | getIndex_obj : HasLabeledInHead obj label → HasLabeledInHead (.getIndex obj idx) label
  | getIndex_idx : HasLabeledInHead idx label → HasLabeledInHead (.getIndex obj idx) label
  | setIndex_obj : HasLabeledInHead obj label → HasLabeledInHead (.setIndex obj idx val) label
  | setIndex_idx : HasLabeledInHead idx label → HasLabeledInHead (.setIndex obj idx val) label
  | setIndex_val : HasLabeledInHead val label → HasLabeledInHead (.setIndex obj idx val) label
  | getEnv_env : HasLabeledInHead env label → HasLabeledInHead (.getEnv env idx) label
  | makeClosure_env : HasLabeledInHead env label → HasLabeledInHead (.makeClosure funcIdx env) label
  | makeEnv_values : HasLabeledInHeadList values label → HasLabeledInHead (.makeEnv values) label
  | objectLit_props : HasLabeledInHeadProps props label → HasLabeledInHead (.objectLit props) label
  | arrayLit_elems : HasLabeledInHeadList elems label → HasLabeledInHead (.arrayLit elems) label

/-- HasLabeledInHead for lists (some element has labeled in head) -/
inductive HasLabeledInHeadList : List Flat.Expr → String → Prop where
  | head : HasLabeledInHead e label → HasLabeledInHeadList (e :: rest) label
  | tail : HasLabeledInHeadList rest label → HasLabeledInHeadList (e :: rest) label

/-- HasLabeledInHead for prop lists (some prop value has labeled in head) -/
inductive HasLabeledInHeadProps : List (Flat.PropName × Flat.Expr) → String → Prop where
  | head : HasLabeledInHead e label → HasLabeledInHeadProps ((name, e) :: rest) label
  | tail : HasLabeledInHeadProps rest label → HasLabeledInHeadProps (p :: rest) label
end

/-! ## List labeled characterization helpers -/

/-- If normalizeExprList es k = .labeled, then either some element has labeled in head,
    or k was called and produced labeled. -/
theorem normalizeExprList_labeled_or_k
    (es : List Flat.Expr)
    (expr_ih : ∀ e, e ∈ es → ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : String) (body : ANF.Expr) (n m : Nat),
      (ANF.normalizeExpr e k).run n = .ok (.labeled label body, m) →
      HasLabeledInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat) (body' : ANF.Expr), (k t).run n' = .ok (.labeled label body', m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : String) (body : ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (.labeled label body, m)) :
    HasLabeledInHeadList es label ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat) (body' : ANF.Expr), (k ts).run n' = .ok (.labeled label body', m') := by
  induction es generalizing k label body n m with
  | nil =>
    simp only [ANF.normalizeExprList] at h
    exact Or.inr ⟨[], n, m, body, h⟩
  | cons e rest ih_rest =>
    simp only [ANF.normalizeExprList] at h
    rcases expr_ih e (.head rest) _ _ _ _ _ h with hleft | ⟨t, n', m', body', hk⟩
    · exact Or.inl (HasLabeledInHeadList.head hleft)
    · rcases ih_rest (fun e' he' => expr_ih e' (.tail e he')) _ _ _ _ _ hk with hleft | ⟨ts, n'', m'', body'', hk'⟩
      · exact Or.inl (HasLabeledInHeadList.tail hleft)
      · exact Or.inr ⟨t :: ts, n'', m'', body'', hk'⟩

/-- If normalizeProps props k = .labeled, then either some prop value has labeled in head,
    or k was called and produced labeled. -/
theorem normalizeProps_labeled_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (expr_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : String) (body : ANF.Expr) (n m : Nat),
      (ANF.normalizeExpr e k).run n = .ok (.labeled label body, m) →
      HasLabeledInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat) (body' : ANF.Expr), (k t).run n' = .ok (.labeled label body', m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr)
    (label : String) (body : ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (.labeled label body, m)) :
    HasLabeledInHeadProps props label ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat) (body' : ANF.Expr), (k ts).run n' = .ok (.labeled label body', m') := by
  induction props generalizing k label body n m with
  | nil =>
    simp only [ANF.normalizeProps] at h
    exact Or.inr ⟨[], n, m, body, h⟩
  | cons p rest ih_rest =>
    obtain ⟨name, value⟩ := p
    simp only [ANF.normalizeProps] at h
    rcases expr_ih name value (.head rest) _ _ _ _ _ h with hleft | ⟨t, n', m', body', hk⟩
    · exact Or.inl (HasLabeledInHeadProps.head hleft)
    · rcases ih_rest (fun n' e' he' => expr_ih n' e' (.tail _ he')) _ _ _ _ _ hk with hleft | ⟨ts, n'', m'', body'', hk'⟩
      · exact Or.inl (HasLabeledInHeadProps.tail hleft)
      · exact Or.inr ⟨(name, t) :: ts, n'', m'', body'', hk'⟩

/-! ## General labeled source characterization -/

/-- General labeled characterization: normalizeExpr e k = .labeled label body →
    e has labeled in CPS head position OR k was called and produced .labeled -/
theorem ANF.normalizeExpr_labeled_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : String) (body : ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.labeled label body, m)) :
    HasLabeledInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat) (body' : ANF.Expr), (k t).run n' = .ok (.labeled label body', m') :=
  normalizeExpr_labeled_or_k_aux e.depth e (Nat.le_refl _) k label body n m h
where
  /-- Helper: general labeled characterization by strong induction on expression depth. -/
  normalizeExpr_labeled_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : String) (body : ANF.Expr) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (.labeled label body, m)) :
      HasLabeledInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat) (body' : ANF.Expr), (k t).run n' = .ok (.labeled label body', m') := by
    induction d generalizing e k label body n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, body, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, body, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, body, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «return» arg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg _ =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | labeled l body_l =>
        left; simp only [ANF.normalizeExpr] at h
        simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, body, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, body, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, body, h⟩
      | «return» arg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
          · exact Or.inl (HasLabeledInHead.return_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | yield arg dlg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
          · exact Or.inl (HasLabeledInHead.yield_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | throw arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.throw_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | await arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.await_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ _ _ h with hleft | ⟨_, n', m', body', hkb⟩
        · exact Or.inl (HasLabeledInHead.seq_left hleft)
        · rcases ih b hb _ _ _ _ _ hkb with hleft | hright
          · exact Or.inl (HasLabeledInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body_let =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body_lab =>
        left
        simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
          pure, Pure.pure, StateT.pure, Except.pure, Except.bind] at h
        split at h
        · simp at h
        · have heq := (Prod.mk.inj (Except.ok.inj h)).1
          cases heq
          exact HasLabeledInHead.labeled_direct
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_labeled_any_k c b k n m label body)
      | tryCatch body_tc cp cb fin =>
        cases fin with
        | none => exact absurd h (ANF.normalizeExpr_tryCatch_none_not_labeled_any_k body_tc cp cb k n m label body)
        | some fin => exact absurd h (ANF.normalizeExpr_tryCatch_some_not_labeled_any_k body_tc cp cb fin k n m label body)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ _ _ h with hleft | ⟨tv, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | typeof arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | unary op arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ _ _ h with hleft | ⟨t, n', m', body', hkt⟩
        · exact Or.inl (HasLabeledInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, body₁, hk₁⟩
        · exact Or.inl (HasLabeledInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, body₂, hk₂⟩
          · exact Or.inl (HasLabeledInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, body₁, hk₁⟩
        · exact Or.inl (HasLabeledInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, body₂, hk₂⟩
          · exact Or.inl (HasLabeledInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, body₁, hk₁⟩
        · exact Or.inl (HasLabeledInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, body₂, hk₂⟩
          · exact Or.inl (HasLabeledInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, body₁, hk₁⟩
        · exact Or.inl (HasLabeledInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, body₂, hk₂⟩
          · exact Or.inl (HasLabeledInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, body₃, hk₃⟩
            · exact Or.inl (HasLabeledInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, body₁, hk₁⟩
        · exact Or.inl (HasLabeledInHead.call_func hleft)
        · rcases ih env henv _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, body₂, hk₂⟩
          · exact Or.inl (HasLabeledInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' label body n m,
                (ANF.normalizeExpr e k').run n = .ok (.labeled label body, m) →
                HasLabeledInHead e label ∨ ∃ t n' m' body', (k' t).run n' = .ok (.labeled label body', m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_labeled_or_k args args_ih _ _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, body₃, hk₃⟩
            · exact Or.inl (HasLabeledInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, body₁, hk₁⟩
        · exact Or.inl (HasLabeledInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, body₂, hk₂⟩
          · exact Or.inl (HasLabeledInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' label body n m,
                (ANF.normalizeExpr e k').run n = .ok (.labeled label body, m) →
                HasLabeledInHead e label ∨ ∃ t n' m' body', (k' t).run n' = .ok (.labeled label body', m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_labeled_or_k args args_ih _ _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, body₃, hk₃⟩
            · exact Or.inl (HasLabeledInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' label body n m,
            (ANF.normalizeExpr e k').run n = .ok (.labeled label body, m) →
            HasLabeledInHead e label ∨ ∃ t n' m' body', (k' t).run n' = .ok (.labeled label body', m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_labeled_or_k values vals_ih _ _ _ _ _ h with hleft | ⟨ts, n', m', body', hk⟩
        · exact Or.inl (HasLabeledInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' label body n m,
            (ANF.normalizeExpr e k').run n = .ok (.labeled label body, m) →
            HasLabeledInHead e label ∨ ∃ t n' m' body', (k' t).run n' = .ok (.labeled label body', m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_labeled_or_k props props_ih _ _ _ _ _ h with hleft | ⟨ts, n', m', body', hk⟩
        · exact Or.inl (HasLabeledInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_not_labeled _ _ _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' label body n m,
            (ANF.normalizeExpr e k').run n = .ok (.labeled label body, m) →
            HasLabeledInHead e label ∨ ∃ t n' m' body', (k' t).run n' = .ok (.labeled label body', m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_labeled_or_k elems elems_ih _ _ _ _ _ h with hleft | ⟨ts, n', m', body', hk⟩
        · exact Or.inl (HasLabeledInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_not_labeled _ _ _ _ _ _)

/-- MASTER INVERSION (labeled):
    If normalizeExpr e k = .ok (.labeled label body, m) with trivial-preserving k,
    then e has .labeled label in evaluation-head position. -/
theorem ANF.normalizeExpr_labeled_implies_hasLabeledInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (label : String) (body : ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.labeled label body, m)) :
    HasLabeledInHead e label := by
  rcases ANF.normalizeExpr_labeled_or_k e k label body n m h with hleft | ⟨t, n', m', body', hk_labeled⟩
  · exact hleft
  · obtain ⟨m'', hm''⟩ := hk t n'
    rw [hm''] at hk_labeled
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_labeled)).1

/-- Contrapositive: if e has no .labeled in head and k never produces .labeled,
    then normalizeExpr e k never produces .labeled. -/
theorem ANF.normalizeExpr_not_labeled_of_no_head_no_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (he : ∀ label, ¬ HasLabeledInHead e label)
    (hk : ∀ (t : ANF.Trivial) (n m : Nat) (label : String) (body : ANF.Expr),
      (k t).run n ≠ .ok (.labeled label body, m))
    (label : String) (body : ANF.Expr) (n m : Nat) :
    (ANF.normalizeExpr e k).run n ≠ .ok (.labeled label body, m) := by
  intro h
  rcases ANF.normalizeExpr_labeled_or_k e k label body n m h with hleft | ⟨t, n', m', body', hkt⟩
  · exact he label hleft
  · exact hk t n' m' label body' hkt

/-- Contrapositive: if e has no .break in head and k never produces .break,
    then normalizeExpr e k never produces .break. -/
theorem ANF.normalizeExpr_not_break_of_no_head_no_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (he : ∀ label, ¬ HasBreakInHead e label)
    (hk : ∀ (t : ANF.Trivial) (n m : Nat) (label : Option String),
      (k t).run n ≠ .ok (.break label, m))
    (label : Option String) (n m : Nat) :
    (ANF.normalizeExpr e k).run n ≠ .ok (.break label, m) := by
  intro h
  rcases ANF.normalizeExpr_break_or_k e k label n m h with hleft | ⟨t, n', m', hkt⟩
  · exact he label hleft
  · exact hk t n' m' label hkt

/-! # Part 3: Break/Continue Step Simulation Helpers -/

/-- Flat.step? on .break produces an error event. -/
theorem Flat.step?_break_is_some (s : Flat.State) (label : Option Flat.LabelName) :
    ∃ s', Flat.step? { s with expr := .break label } = some (.error ("break:" ++ (label.getD "")), s') := by
  exact ⟨_, by unfold Flat.step?; rfl⟩

/-- Flat.step? on .break produces the exact error event and terminal state. -/
theorem Flat.step?_break_eq (s : Flat.State) (label : Option Flat.LabelName) :
    Flat.step? { s with expr := .break label } =
      some (.error ("break:" ++ (label.getD "")),
            { s with expr := .lit .undefined,
                     trace := s.trace ++ [.error ("break:" ++ (label.getD ""))] }) := by
  unfold Flat.step?; rfl

/-- Flat.step? on .continue produces an error event. -/
theorem Flat.step?_continue_is_some (s : Flat.State) (label : Option Flat.LabelName) :
    ∃ s', Flat.step? { s with expr := .continue label } = some (.error ("continue:" ++ (label.getD "")), s') := by
  exact ⟨_, by unfold Flat.step?; rfl⟩

/-- Flat.step? on .continue produces the exact error event and terminal state. -/
theorem Flat.step?_continue_eq (s : Flat.State) (label : Option Flat.LabelName) :
    Flat.step? { s with expr := .continue label } =
      some (.error ("continue:" ++ (label.getD "")),
            { s with expr := .lit .undefined,
                     trace := s.trace ++ [.error ("continue:" ++ (label.getD ""))] }) := by
  unfold Flat.step?; rfl

/-- normalizeExpr (.break label) k ignores k and produces .break label. -/
theorem ANF.normalizeExpr_break_run (label : Option Flat.LabelName)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n : Nat) :
    (ANF.normalizeExpr (.break label) k).run n = .ok (.break label, n) := by
  simp [ANF.normalizeExpr, StateT.run, pure, Pure.pure, StateT.pure, Except.pure]

/-- normalizeExpr (.continue label) k ignores k and produces .continue label. -/
theorem ANF.normalizeExpr_continue_run (label : Option Flat.LabelName)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n : Nat) :
    (ANF.normalizeExpr (.continue label) k).run n = .ok (.continue label, n) := by
  simp [ANF.normalizeExpr, StateT.run, pure, Pure.pure, StateT.pure, Except.pure]

/-- normalizeExpr (.lit .undefined) with trivial k gives .trivial .litUndefined. -/
theorem ANF.normalizeExpr_lit_undefined_trivial (n : Nat) :
    (ANF.normalizeExpr (.lit .undefined) (fun t => pure (.trivial t))).run n =
      .ok (.trivial .litUndefined, n) := by
  simp [ANF.normalizeExpr, ANF.trivialOfFlatValue, StateT.run, pure, Pure.pure, StateT.pure,
        Except.pure, bind, Bind.bind, StateT.bind, StateT.lift, Functor.map, Except.map]

/-- The trivial identity continuation is trivial-preserving. -/
theorem ANF.trivial_k_preserving :
    ∀ (arg : ANF.Trivial) (n' : Nat), ∃ (m' : Nat),
      ((fun t => pure (.trivial t) : ANF.Trivial → ANF.ConvM ANF.Expr) arg).run n' =
        .ok (.trivial arg, m') := by
  intro arg n'
  exact ⟨n', by simp [StateT.run, pure, Pure.pure, StateT.pure, Except.pure]⟩

/-- If normalizeExpr (.break label) k = .break label, then m = n (state unchanged). -/
theorem normalizeExpr_break_direct_state_eq
    (label : Option Flat.LabelName) (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExpr (.break label) k).run n = .ok (.break label, m)) :
    m = n := by
  simp [ANF.normalizeExpr, StateT.run, pure, Pure.pure, StateT.pure, Except.pure] at h
  exact h.symm

/-- If normalizeExpr (.continue label) k = .continue label, then m = n (state unchanged). -/
theorem normalizeExpr_continue_direct_state_eq
    (label : Option Flat.LabelName) (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExpr (.continue label) k).run n = .ok (.continue label, m)) :
    m = n := by
  simp [ANF.normalizeExpr, StateT.run, pure, Pure.pure, StateT.pure, Except.pure] at h
  exact h.symm

/-! # Part 4: Continue Inversion -/

/-! ## bindComplex never produces .continue -/

/-- bindComplex always wraps its result in .let, so it can NEVER produce .continue. -/
theorem ANF.bindComplex_never_continue_general (rhs : ANF.ComplexExpr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.bindComplex rhs k).run n = .ok (.continue label, m)) : False := by
  unfold ANF.bindComplex at h
  unfold ANF.freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure,
    StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-! ## Wrapping constructors NEVER produce .continue -/

/-- normalizeExpr (.labeled l body) k never produces .continue — result is always .labeled -/
theorem ANF.normalizeExpr_labeled_not_continue (l : Flat.LabelName) (body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr (.labeled l body) k).run n = .ok (.continue label, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    pure, Pure.pure, StateT.pure, Except.pure, Except.bind] at h
  split at h <;> simp_all

/-- normalizeExpr (.while_ cond body) k never produces .continue — result is always .seq -/
theorem ANF.normalizeExpr_while_not_continue (cond_ body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr (.while_ cond_ body) k).run n = .ok (.continue label, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    pure, Pure.pure, StateT.pure, Except.pure, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-- normalizeExpr (.tryCatch body cp cb fin) k never produces .continue — always .tryCatch -/
theorem ANF.normalizeExpr_tryCatch_not_continue (body : Flat.Expr) (cp : Flat.VarName)
    (cb : Flat.Expr) (fin : Option Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr (.tryCatch body cp cb fin) k).run n = .ok (.continue label, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    pure, Pure.pure, StateT.pure, Except.pure, Except.bind,
    Functor.map, StateT.map, Except.map] at h
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h
  · simp only [Except.bind, Functor.map, StateT.map, StateT.bind, StateT.run,
      bind, Bind.bind, Except.map, pure, Pure.pure, StateT.pure, Except.pure] at h
    split at h
    · nomatch h
    · exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
  · simp only [StateT.bind, StateT.pure, Except.bind, Except.pure,
      pure, Pure.pure, bind, Bind.bind] at h
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-! ## HasContinueInHead mutual inductive -/

set_option autoImplicit true in
mutual
/-- An expression has .continue label reachable through normalizeExpr's CPS evaluation path. -/
inductive HasContinueInHead : Flat.Expr → Option Flat.LabelName → Prop where
  | continue_direct : HasContinueInHead (.continue label) label
  | seq_left : HasContinueInHead a label → HasContinueInHead (.seq a b) label
  | seq_right : HasContinueInHead b label → HasContinueInHead (.seq a b) label
  | let_init : HasContinueInHead init label → HasContinueInHead (.let name init body) label
  | getProp_obj : HasContinueInHead obj label → HasContinueInHead (.getProp obj prop) label
  | setProp_obj : HasContinueInHead obj label → HasContinueInHead (.setProp obj prop val) label
  | setProp_val : HasContinueInHead val label → HasContinueInHead (.setProp obj prop val) label
  | binary_lhs : HasContinueInHead lhs label → HasContinueInHead (.binary op lhs rhs) label
  | binary_rhs : HasContinueInHead rhs label → HasContinueInHead (.binary op lhs rhs) label
  | unary_arg : HasContinueInHead arg label → HasContinueInHead (.unary op arg) label
  | typeof_arg : HasContinueInHead arg label → HasContinueInHead (.typeof arg) label
  | deleteProp_obj : HasContinueInHead obj label → HasContinueInHead (.deleteProp obj prop) label
  | assign_val : HasContinueInHead val label → HasContinueInHead (.assign name val) label
  | call_func : HasContinueInHead f label → HasContinueInHead (.call f env args) label
  | call_env : HasContinueInHead env label → HasContinueInHead (.call f env args) label
  | call_args : HasContinueInHeadList args label → HasContinueInHead (.call f env args) label
  | newObj_func : HasContinueInHead f label → HasContinueInHead (.newObj f env args) label
  | newObj_env : HasContinueInHead env label → HasContinueInHead (.newObj f env args) label
  | newObj_args : HasContinueInHeadList args label → HasContinueInHead (.newObj f env args) label
  | if_cond : HasContinueInHead c label → HasContinueInHead (.if c t e) label
  | throw_arg : HasContinueInHead arg label → HasContinueInHead (.throw arg) label
  | return_some_arg : HasContinueInHead v label → HasContinueInHead (.return (some v)) label
  | yield_some_arg : HasContinueInHead v label → HasContinueInHead (.yield (some v) d) label
  | await_arg : HasContinueInHead arg label → HasContinueInHead (.await arg) label
  | getIndex_obj : HasContinueInHead obj label → HasContinueInHead (.getIndex obj idx) label
  | getIndex_idx : HasContinueInHead idx label → HasContinueInHead (.getIndex obj idx) label
  | setIndex_obj : HasContinueInHead obj label → HasContinueInHead (.setIndex obj idx val) label
  | setIndex_idx : HasContinueInHead idx label → HasContinueInHead (.setIndex obj idx val) label
  | setIndex_val : HasContinueInHead val label → HasContinueInHead (.setIndex obj idx val) label
  | getEnv_env : HasContinueInHead env label → HasContinueInHead (.getEnv env idx) label
  | makeClosure_env : HasContinueInHead env label → HasContinueInHead (.makeClosure funcIdx env) label
  | makeEnv_values : HasContinueInHeadList values label → HasContinueInHead (.makeEnv values) label
  | objectLit_props : HasContinueInHeadProps props label → HasContinueInHead (.objectLit props) label
  | arrayLit_elems : HasContinueInHeadList elems label → HasContinueInHead (.arrayLit elems) label

/-- HasContinueInHead for lists (some element has continue in head) -/
inductive HasContinueInHeadList : List Flat.Expr → Option Flat.LabelName → Prop where
  | head : HasContinueInHead e label → HasContinueInHeadList (e :: rest) label
  | tail : HasContinueInHeadList rest label → HasContinueInHeadList (e :: rest) label

/-- HasContinueInHead for prop lists (some prop value has continue in head) -/
inductive HasContinueInHeadProps : List (Flat.PropName × Flat.Expr) → Option Flat.LabelName → Prop where
  | head : HasContinueInHead e label → HasContinueInHeadProps ((name, e) :: rest) label
  | tail : HasContinueInHeadProps rest label → HasContinueInHeadProps (p :: rest) label
end

/-- HasContinueInHead expressions are never values. -/
private theorem HasContinueInHead_not_value (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasContinueInHead e label) : Flat.exprValue? e = none := by
  cases h <;> simp [Flat.exprValue?]

/-! ## List continue characterization helpers -/

/-- If normalizeExprList es k = .continue, then either some element has continue in head,
    or k was called and produced continue. -/
theorem normalizeExprList_continue_or_k
    (es : List Flat.Expr)
    (expr_ih : ∀ e, e ∈ es → ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat),
      (ANF.normalizeExpr e k).run n = .ok (.continue label, m) →
      HasContinueInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.continue label, m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (.continue label, m)) :
    HasContinueInHeadList es label ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat), (k ts).run n' = .ok (.continue label, m') := by
  induction es generalizing k label n m with
  | nil =>
    simp only [ANF.normalizeExprList] at h
    exact Or.inr ⟨[], n, m, h⟩
  | cons e rest ih_rest =>
    simp only [ANF.normalizeExprList] at h
    rcases expr_ih e (.head rest) _ _ _ _ h with hleft | ⟨t, n', m', hk⟩
    · exact Or.inl (HasContinueInHeadList.head hleft)
    · rcases ih_rest (fun e' he' => expr_ih e' (.tail e he')) _ _ _ _ hk with hleft | ⟨ts, n'', m'', hk'⟩
      · exact Or.inl (HasContinueInHeadList.tail hleft)
      · exact Or.inr ⟨t :: ts, n'', m'', hk'⟩

/-- If normalizeProps props k = .continue, then either some prop value has continue in head,
    or k was called and produced continue. -/
theorem normalizeProps_continue_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (expr_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat),
      (ANF.normalizeExpr e k).run n = .ok (.continue label, m) →
      HasContinueInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.continue label, m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (.continue label, m)) :
    HasContinueInHeadProps props label ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat), (k ts).run n' = .ok (.continue label, m') := by
  induction props generalizing k label n m with
  | nil =>
    simp only [ANF.normalizeProps] at h
    exact Or.inr ⟨[], n, m, h⟩
  | cons p rest ih_rest =>
    obtain ⟨name, value⟩ := p
    simp only [ANF.normalizeProps] at h
    rcases expr_ih name value (.head rest) _ _ _ _ h with hleft | ⟨t, n', m', hk⟩
    · exact Or.inl (HasContinueInHeadProps.head hleft)
    · rcases ih_rest (fun n' e' he' => expr_ih n' e' (.tail _ he')) _ _ _ _ hk with hleft | ⟨ts, n'', m'', hk'⟩
      · exact Or.inl (HasContinueInHeadProps.tail hleft)
      · exact Or.inr ⟨(name, t) :: ts, n'', m'', hk'⟩

/-! ## General continue source characterization -/

/-- General continue characterization: normalizeExpr e k = .continue →
    e has continue in CPS head position OR k was called and produced .continue -/
theorem ANF.normalizeExpr_continue_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.continue label, m)) :
    HasContinueInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.continue label, m') :=
  normalizeExpr_continue_or_k_aux e.depth e (Nat.le_refl _) k label n m h
where
  /-- Helper: general continue characterization by strong induction on expression depth. -/
  normalizeExpr_continue_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (label : Option String) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (.continue label, m)) :
      HasContinueInHead e label ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.continue label, m') := by
    induction d generalizing e k label n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        left; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        cases (Prod.mk.inj (Except.ok.inj h)).1; exact HasContinueInHead.continue_direct
      | «return» arg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg _ =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | «continue» l =>
        left; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        cases (Prod.mk.inj (Except.ok.inj h)).1; exact HasContinueInHead.continue_direct
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «return» arg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasContinueInHead.return_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | yield arg dlg =>
        cases arg with
        | none => simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h; exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasContinueInHead.yield_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | throw arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.throw_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | await arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.await_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ _ h with hleft | ⟨_, n', m', hkb⟩
        · exact Or.inl (HasContinueInHead.seq_left hleft)
        · rcases ih b hb _ _ _ _ hkb with hleft | hright
          · exact Or.inl (HasContinueInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body =>
        exact absurd h (ANF.normalizeExpr_labeled_not_continue l body k label n m)
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_continue c b k label n m)
      | tryCatch body cp cb fin =>
        exact absurd h (ANF.normalizeExpr_tryCatch_not_continue body cp cb fin k label n m)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ _ h with hleft | ⟨tv, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | typeof arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | unary op arg =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasContinueInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasContinueInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasContinueInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasContinueInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasContinueInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasContinueInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasContinueInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasContinueInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasContinueInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, hk₃⟩
            · exact Or.inl (HasContinueInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasContinueInHead.call_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasContinueInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' label n m,
                (ANF.normalizeExpr e k').run n = .ok (.continue label, m) →
                HasContinueInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.continue label, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_continue_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasContinueInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasContinueInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasContinueInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' label n m,
                (ANF.normalizeExpr e k').run n = .ok (.continue label, m) →
                HasContinueInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.continue label, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_continue_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasContinueInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' label n m,
            (ANF.normalizeExpr e k').run n = .ok (.continue label, m) →
            HasContinueInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.continue label, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_continue_or_k values vals_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasContinueInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' label n m,
            (ANF.normalizeExpr e k').run n = .ok (.continue label, m) →
            HasContinueInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.continue label, m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_continue_or_k props props_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasContinueInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_never_continue_general _ _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' label n m,
            (ANF.normalizeExpr e k').run n = .ok (.continue label, m) →
            HasContinueInHead e label ∨ ∃ t n' m', (k' t).run n' = .ok (.continue label, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_continue_or_k elems elems_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasContinueInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_never_continue_general _ _ _ _ _)

/-- MASTER INVERSION (continue):
    If normalizeExpr e k = .ok (.continue label, m) with trivial-preserving k,
    then e has .continue label in evaluation-head position. -/
theorem ANF.normalizeExpr_continue_implies_hasContinueInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.continue label, m)) :
    HasContinueInHead e label := by
  rcases ANF.normalizeExpr_continue_or_k e k label n m h with hleft | ⟨t, n', m', hk_continue⟩
  · exact hleft
  · obtain ⟨m'', hm''⟩ := hk t n'
    rw [hm''] at hk_continue
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_continue)).1

/-- Contrapositive: if e has no .continue in head and k never produces .continue,
    then normalizeExpr e k never produces .continue. -/
theorem ANF.normalizeExpr_not_continue_of_no_head_no_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (he : ∀ label, ¬ HasContinueInHead e label)
    (hk : ∀ (t : ANF.Trivial) (n m : Nat) (label : Option String),
      (k t).run n ≠ .ok (.continue label, m))
    (label : Option String) (n m : Nat) :
    (ANF.normalizeExpr e k).run n ≠ .ok (.continue label, m) := by
  intro h
  rcases ANF.normalizeExpr_continue_or_k e k label n m h with hleft | ⟨t, n', m', hkt⟩
  · exact he label hleft
  · exact hk t n' m' label hkt

/-! # Part 4: Throw Inversion -/

/-! ## HasThrowInHead mutual inductive -/

set_option autoImplicit true in
mutual
/-- An expression has .throw reachable through normalizeExpr's CPS evaluation path. -/
inductive HasThrowInHead : Flat.Expr → Prop where
  | throw_direct : HasThrowInHead (.throw arg)
  | seq_left : HasThrowInHead a → HasThrowInHead (.seq a b)
  | seq_right : HasThrowInHead b → HasThrowInHead (.seq a b)
  | let_init : HasThrowInHead init → HasThrowInHead (.let name init body)
  | getProp_obj : HasThrowInHead obj → HasThrowInHead (.getProp obj prop)
  | setProp_obj : HasThrowInHead obj → HasThrowInHead (.setProp obj prop val)
  | setProp_val : HasThrowInHead val → HasThrowInHead (.setProp obj prop val)
  | binary_lhs : HasThrowInHead lhs → HasThrowInHead (.binary op lhs rhs)
  | binary_rhs : HasThrowInHead rhs → HasThrowInHead (.binary op lhs rhs)
  | unary_arg : HasThrowInHead arg → HasThrowInHead (.unary op arg)
  | typeof_arg : HasThrowInHead arg → HasThrowInHead (.typeof arg)
  | deleteProp_obj : HasThrowInHead obj → HasThrowInHead (.deleteProp obj prop)
  | assign_val : HasThrowInHead val → HasThrowInHead (.assign name val)
  | call_func : HasThrowInHead f → HasThrowInHead (.call f env args)
  | call_env : HasThrowInHead env → HasThrowInHead (.call f env args)
  | call_args : HasThrowInHeadList args → HasThrowInHead (.call f env args)
  | newObj_func : HasThrowInHead f → HasThrowInHead (.newObj f env args)
  | newObj_env : HasThrowInHead env → HasThrowInHead (.newObj f env args)
  | newObj_args : HasThrowInHeadList args → HasThrowInHead (.newObj f env args)
  | if_cond : HasThrowInHead c → HasThrowInHead (.if c t e)
  | return_some_arg : HasThrowInHead v → HasThrowInHead (.return (some v))
  | yield_some_arg : HasThrowInHead v → HasThrowInHead (.yield (some v) d)
  | await_arg : HasThrowInHead arg → HasThrowInHead (.await arg)
  | getIndex_obj : HasThrowInHead obj → HasThrowInHead (.getIndex obj idx)
  | getIndex_idx : HasThrowInHead idx → HasThrowInHead (.getIndex obj idx)
  | setIndex_obj : HasThrowInHead obj → HasThrowInHead (.setIndex obj idx val)
  | setIndex_idx : HasThrowInHead idx → HasThrowInHead (.setIndex obj idx val)
  | setIndex_val : HasThrowInHead val → HasThrowInHead (.setIndex obj idx val)
  | getEnv_env : HasThrowInHead env → HasThrowInHead (.getEnv env idx)
  | makeClosure_env : HasThrowInHead env → HasThrowInHead (.makeClosure funcIdx env)
  | makeEnv_values : HasThrowInHeadList values → HasThrowInHead (.makeEnv values)
  | objectLit_props : HasThrowInHeadProps props → HasThrowInHead (.objectLit props)
  | arrayLit_elems : HasThrowInHeadList elems → HasThrowInHead (.arrayLit elems)

/-- HasThrowInHead for lists (some element has throw in head) -/
inductive HasThrowInHeadList : List Flat.Expr → Prop where
  | head : HasThrowInHead e → HasThrowInHeadList (e :: rest)
  | tail : HasThrowInHeadList rest → HasThrowInHeadList (e :: rest)

/-- HasThrowInHead for prop lists (some prop value has throw in head) -/
inductive HasThrowInHeadProps : List (Flat.PropName × Flat.Expr) → Prop where
  | head : HasThrowInHead e → HasThrowInHeadProps ((name, e) :: rest)
  | tail : HasThrowInHeadProps rest → HasThrowInHeadProps (p :: rest)
end

/-- HasThrowInHead expressions are never values. -/
private theorem HasThrowInHead_not_value (e : Flat.Expr)
    (h : HasThrowInHead e) : Flat.exprValue? e = none := by
  cases h <;> simp [Flat.exprValue?]

/-! ## Helper: bindComplex never produces .throw -/

/-- bindComplex always wraps its result in .let, so it can NEVER produce .throw. -/
theorem ANF.bindComplex_never_throw_general (rhs : ANF.ComplexExpr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.bindComplex rhs k).run n = .ok (.throw arg, m)) : False := by
  unfold ANF.bindComplex at h
  unfold ANF.freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure,
    StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-! ## Helpers: wrapping constructors never produce .throw -/

/-- normalizeExpr (.labeled l body) k never produces .throw — result is always .labeled -/
theorem ANF.normalizeExpr_labeled_not_throw (l : Flat.LabelName) (body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.labeled l body) k).run n = .ok (.throw arg, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-- normalizeExpr (.while_ cond body) k never produces .throw — result is always .seq -/
theorem ANF.normalizeExpr_while_not_throw (cond_ body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.while_ cond_ body) k).run n = .ok (.throw arg, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-- normalizeExpr (.tryCatch body cp cb fin) k never produces .throw — always .tryCatch -/
theorem ANF.normalizeExpr_tryCatch_not_throw (body : Flat.Expr) (cp : Flat.VarName)
    (cb : Flat.Expr) (fin : Option Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.tryCatch body cp cb fin) k).run n = .ok (.throw arg, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map] at h
  cases fin with
  | none =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h <;> (try split at h) <;> simp_all
  | some _ =>
    simp only [Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
      Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
    split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-! ## List/Props helpers for throw -/

/-- normalizeExprList: throw in result comes from some element or from k. -/
theorem normalizeExprList_throw_or_k
    (es : List Flat.Expr)
    (ih : ∀ e, e ∈ es → ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.throw arg, m) →
      HasThrowInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.throw arg, m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (.throw arg, m)) :
    HasThrowInHeadList es ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat), (k ts).run n' = .ok (.throw arg, m') := by
  induction es generalizing k arg n m with
  | nil => right; simp only [ANF.normalizeExprList] at h; exact ⟨[], n, m, h⟩
  | cons e rest ih_list =>
    simp only [ANF.normalizeExprList] at h
    rcases ih e (@List.mem_cons_self _ e rest) _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasThrowInHeadList.head hleft)
    · rcases ih_list (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasThrowInHeadList.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨t :: ts, n'', m'', hkts⟩

/-- normalizeProps: throw in result comes from some prop value or from k. -/
theorem normalizeProps_throw_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.throw arg, m) →
      HasThrowInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.throw arg, m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (.throw arg, m)) :
    HasThrowInHeadProps props ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat), (k ts).run n' = .ok (.throw arg, m') := by
  induction props generalizing k arg n m with
  | nil => right; simp only [ANF.normalizeProps] at h; exact ⟨[], n, m, h⟩
  | cons p rest ih_list =>
    unfold ANF.normalizeProps at h
    rcases ih p.1 p.2 (@List.mem_cons_self _ _ rest) _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasThrowInHeadProps.head hleft)
    · rcases ih_list (fun name e he => ih name e (List.mem_cons_of_mem _ he)) _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasThrowInHeadProps.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨(p.1, t) :: ts, n'', m'', hkts⟩

/-! ## Main theorem: normalizeExpr_throw_or_k -/

/-- If normalizeExpr e k produces .throw arg, then either e has throw in
    CPS-head position or k produced .throw arg. -/
theorem ANF.normalizeExpr_throw_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.throw arg, m)) :
    HasThrowInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.throw arg, m') :=
  normalizeExpr_throw_or_k_aux e.depth e (Nat.le_refl _) k arg n m h
where
  /-- Helper: general throw characterization by strong induction on expression depth. -/
  normalizeExpr_throw_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (.throw arg, m)) :
      HasThrowInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.throw arg, m') := by
    induction d generalizing e k arg n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | throw arg_flat =>
        exact Or.inl HasThrowInHead.throw_direct
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg_y _ =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | await _ => simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | throw arg_flat =>
        exact Or.inl HasThrowInHead.throw_direct
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasThrowInHead.return_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | yield arg_y dlg =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasThrowInHead.yield_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | await arg_a =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_a ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.await_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ _ h with hleft | ⟨_, n', m', hkb⟩
        · exact Or.inl (HasThrowInHead.seq_left hleft)
        · rcases ih b hb _ _ _ _ hkb with hleft | hright
          · exact Or.inl (HasThrowInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body =>
        exact absurd h (ANF.normalizeExpr_labeled_not_throw l body k arg n m)
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_throw c b k arg n m)
      | tryCatch body cp cb fin =>
        exact absurd h (ANF.normalizeExpr_tryCatch_not_throw body cp cb fin k arg n m)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ _ h with hleft | ⟨tv, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | typeof arg_t =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_t.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_t ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | unary op arg_u =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_u.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_u ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasThrowInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasThrowInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasThrowInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasThrowInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasThrowInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasThrowInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasThrowInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasThrowInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasThrowInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, hk₃⟩
            · exact Or.inl (HasThrowInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasThrowInHead.call_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasThrowInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : ANF.Trivial) n m,
                (ANF.normalizeExpr e k').run n = .ok (.throw arg', m) →
                HasThrowInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.throw arg', m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_throw_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasThrowInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasThrowInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasThrowInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : ANF.Trivial) n m,
                (ANF.normalizeExpr e k').run n = .ok (.throw arg', m) →
                HasThrowInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.throw arg', m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_throw_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasThrowInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.throw arg', m) →
            HasThrowInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.throw arg', m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_throw_or_k values vals_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasThrowInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.throw arg', m) →
            HasThrowInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.throw arg', m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_throw_or_k props props_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasThrowInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_never_throw_general _ _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.throw arg', m) →
            HasThrowInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.throw arg', m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_throw_or_k elems elems_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasThrowInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_never_throw_general _ _ _ _ _)

/-- MASTER INVERSION (throw):
    If normalizeExpr e k = .ok (.throw arg, m) with trivial-preserving k,
    then e has .throw in evaluation-head position. -/
theorem ANF.normalizeExpr_throw_implies_hasThrowInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.throw arg, m)) :
    HasThrowInHead e := by
  rcases ANF.normalizeExpr_throw_or_k e k arg n m h with hleft | ⟨t, n', m', hk_throw⟩
  · exact hleft
  · obtain ⟨m'', hm''⟩ := hk t n'
    rw [hm''] at hk_throw
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_throw)).1

/-! ## HasAwaitInHead: tracks .await in CPS-head position -/

section AwaitInHead

set_option autoImplicit true in
mutual
/-- Predicate tracking whether an expression has .await in CPS-head position.
    Structurally parallel to HasThrowInHead but with .await_direct instead of .throw_direct. -/
inductive HasAwaitInHead : Flat.Expr → Prop where
  | await_direct : HasAwaitInHead (.await arg)
  | seq_left : HasAwaitInHead a → HasAwaitInHead (.seq a b)
  | seq_right : HasAwaitInHead b → HasAwaitInHead (.seq a b)
  | let_init : HasAwaitInHead init → HasAwaitInHead (.let name init body)
  | getProp_obj : HasAwaitInHead obj → HasAwaitInHead (.getProp obj prop)
  | setProp_obj : HasAwaitInHead obj → HasAwaitInHead (.setProp obj prop val)
  | setProp_val : HasAwaitInHead val → HasAwaitInHead (.setProp obj prop val)
  | binary_lhs : HasAwaitInHead lhs → HasAwaitInHead (.binary op lhs rhs)
  | binary_rhs : HasAwaitInHead rhs → HasAwaitInHead (.binary op lhs rhs)
  | unary_arg : HasAwaitInHead arg → HasAwaitInHead (.unary op arg)
  | typeof_arg : HasAwaitInHead arg → HasAwaitInHead (.typeof arg)
  | deleteProp_obj : HasAwaitInHead obj → HasAwaitInHead (.deleteProp obj prop)
  | assign_val : HasAwaitInHead val → HasAwaitInHead (.assign name val)
  | call_func : HasAwaitInHead f → HasAwaitInHead (.call f env args)
  | call_env : HasAwaitInHead env → HasAwaitInHead (.call f env args)
  | call_args : HasAwaitInHeadList args → HasAwaitInHead (.call f env args)
  | newObj_func : HasAwaitInHead f → HasAwaitInHead (.newObj f env args)
  | newObj_env : HasAwaitInHead env → HasAwaitInHead (.newObj f env args)
  | newObj_args : HasAwaitInHeadList args → HasAwaitInHead (.newObj f env args)
  | if_cond : HasAwaitInHead c → HasAwaitInHead (.if c t e)
  | return_some_arg : HasAwaitInHead v → HasAwaitInHead (.return (some v))
  | yield_some_arg : HasAwaitInHead v → HasAwaitInHead (.yield (some v) d)
  | throw_arg : HasAwaitInHead arg → HasAwaitInHead (.throw arg)
  | getIndex_obj : HasAwaitInHead obj → HasAwaitInHead (.getIndex obj idx)
  | getIndex_idx : HasAwaitInHead idx → HasAwaitInHead (.getIndex obj idx)
  | setIndex_obj : HasAwaitInHead obj → HasAwaitInHead (.setIndex obj idx val)
  | setIndex_idx : HasAwaitInHead idx → HasAwaitInHead (.setIndex obj idx val)
  | setIndex_val : HasAwaitInHead val → HasAwaitInHead (.setIndex obj idx val)
  | getEnv_env : HasAwaitInHead env → HasAwaitInHead (.getEnv env idx)
  | makeClosure_env : HasAwaitInHead env → HasAwaitInHead (.makeClosure funcIdx env)
  | makeEnv_values : HasAwaitInHeadList values → HasAwaitInHead (.makeEnv values)
  | objectLit_props : HasAwaitInHeadProps props → HasAwaitInHead (.objectLit props)
  | arrayLit_elems : HasAwaitInHeadList elems → HasAwaitInHead (.arrayLit elems)

inductive HasAwaitInHeadList : List Flat.Expr → Prop where
  | head : HasAwaitInHead e → HasAwaitInHeadList (e :: rest)
  | tail : HasAwaitInHeadList rest → HasAwaitInHeadList (e :: rest)

inductive HasAwaitInHeadProps : List (Flat.PropName × Flat.Expr) → Prop where
  | head : HasAwaitInHead e → HasAwaitInHeadProps ((name, e) :: rest)
  | tail : HasAwaitInHeadProps rest → HasAwaitInHeadProps (p :: rest)
end

/-- HasAwaitInHead expressions are never values. -/
private theorem HasAwaitInHead_not_value (e : Flat.Expr)
    (h : HasAwaitInHead e) : Flat.exprValue? e = none := by
  cases h <;> simp [Flat.exprValue?]

/-! ## Helper: bindComplex never produces .await -/

/-- bindComplex always wraps its result in .let, so it can NEVER produce .await. -/
theorem ANF.bindComplex_never_await_general (rhs : ANF.ComplexExpr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.bindComplex rhs k).run n = .ok (.await arg, m)) : False := by
  unfold ANF.bindComplex at h
  unfold ANF.freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure,
    StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-! ## Helpers: wrapping constructors never produce .await -/

/-- normalizeExpr (.labeled l body) k never produces .await — result is always .labeled -/
theorem ANF.normalizeExpr_labeled_not_await (l : Flat.LabelName) (body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.labeled l body) k).run n = .ok (.await arg, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-- normalizeExpr (.while_ cond body) k never produces .await — result is always .seq -/
theorem ANF.normalizeExpr_while_not_await (cond_ body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.while_ cond_ body) k).run n = .ok (.await arg, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-- normalizeExpr (.tryCatch body cp cb fin) k never produces .await — always .tryCatch -/
theorem ANF.normalizeExpr_tryCatch_not_await (body : Flat.Expr) (cp : Flat.VarName)
    (cb : Flat.Expr) (fin : Option Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.tryCatch body cp cb fin) k).run n = .ok (.await arg, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map] at h
  cases fin with
  | none =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h <;> (try split at h) <;> simp_all
  | some _ =>
    simp only [Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind,
      Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
    split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-! ## List/Props helpers for await -/

/-- normalizeExprList: await in result comes from some element or from k. -/
theorem normalizeExprList_await_or_k
    (es : List Flat.Expr)
    (ih : ∀ e, e ∈ es → ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.await arg, m) →
      HasAwaitInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.await arg, m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (.await arg, m)) :
    HasAwaitInHeadList es ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat), (k ts).run n' = .ok (.await arg, m') := by
  induction es generalizing k arg n m with
  | nil => right; simp only [ANF.normalizeExprList] at h; exact ⟨[], n, m, h⟩
  | cons e rest ih_list =>
    simp only [ANF.normalizeExprList] at h
    rcases ih e (@List.mem_cons_self _ e rest) _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasAwaitInHeadList.head hleft)
    · rcases ih_list (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasAwaitInHeadList.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨t :: ts, n'', m'', hkts⟩

/-- normalizeProps: await in result comes from some prop value or from k. -/
theorem normalizeProps_await_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.await arg, m) →
      HasAwaitInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.await arg, m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (.await arg, m)) :
    HasAwaitInHeadProps props ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat), (k ts).run n' = .ok (.await arg, m') := by
  induction props generalizing k arg n m with
  | nil => right; simp only [ANF.normalizeProps] at h; exact ⟨[], n, m, h⟩
  | cons p rest ih_list =>
    unfold ANF.normalizeProps at h
    rcases ih p.1 p.2 (@List.mem_cons_self _ _ rest) _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasAwaitInHeadProps.head hleft)
    · rcases ih_list (fun name e he => ih name e (List.mem_cons_of_mem _ he)) _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasAwaitInHeadProps.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨(p.1, t) :: ts, n'', m'', hkts⟩

/-! ## Main theorem: normalizeExpr_await_or_k -/

/-- If normalizeExpr e k produces .await arg, then either e has await in
    CPS-head position or k produced .await arg. -/
theorem ANF.normalizeExpr_await_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.await arg, m)) :
    HasAwaitInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.await arg, m') :=
  normalizeExpr_await_or_k_aux e.depth e (Nat.le_refl _) k arg n m h
where
  /-- Helper: general await characterization by strong induction on expression depth. -/
  normalizeExpr_await_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (.await arg, m)) :
      HasAwaitInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.await arg, m') := by
    induction d generalizing e k arg n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg_y _ =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | await _ => simp [Flat.Expr.depth] at hd
      | throw _ => simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | await arg_a =>
        exact Or.inl HasAwaitInHead.await_direct
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasAwaitInHead.return_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | yield arg_y dlg =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasAwaitInHead.yield_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | throw arg_t =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_t.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_t ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.throw_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ _ h with hleft | ⟨_, n', m', hkb⟩
        · exact Or.inl (HasAwaitInHead.seq_left hleft)
        · rcases ih b hb _ _ _ _ hkb with hleft | hright
          · exact Or.inl (HasAwaitInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body =>
        exact absurd h (ANF.normalizeExpr_labeled_not_await l body k arg n m)
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_await c b k arg n m)
      | tryCatch body cp cb fin =>
        exact absurd h (ANF.normalizeExpr_tryCatch_not_await body cp cb fin k arg n m)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ _ h with hleft | ⟨tv, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_never_await_general _ _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_await_general _ _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_await_general _ _ _ _ _)
      | typeof arg_t =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_t.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_t ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_await_general _ _ _ _ _)
      | unary op arg_u =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_u.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_u ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_await_general _ _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_await_general _ _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasAwaitInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_await_general _ _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasAwaitInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasAwaitInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_await_general _ _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasAwaitInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasAwaitInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_await_general _ _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasAwaitInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasAwaitInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_await_general _ _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasAwaitInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasAwaitInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, hk₃⟩
            · exact Or.inl (HasAwaitInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_await_general _ _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasAwaitInHead.call_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasAwaitInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : ANF.Trivial) n m,
                (ANF.normalizeExpr e k').run n = .ok (.await arg', m) →
                HasAwaitInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.await arg', m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_await_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasAwaitInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_await_general _ _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasAwaitInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasAwaitInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : ANF.Trivial) n m,
                (ANF.normalizeExpr e k').run n = .ok (.await arg', m) →
                HasAwaitInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.await arg', m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_await_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasAwaitInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_await_general _ _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.await arg', m) →
            HasAwaitInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.await arg', m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_await_or_k values vals_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasAwaitInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_never_await_general _ _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.await arg', m) →
            HasAwaitInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.await arg', m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_await_or_k props props_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasAwaitInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_never_await_general _ _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.await arg', m) →
            HasAwaitInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.await arg', m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_await_or_k elems elems_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasAwaitInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_never_await_general _ _ _ _ _)

/-- MASTER INVERSION (await):
    If normalizeExpr e k = .ok (.await arg, m) with trivial-preserving k,
    then e has .await in evaluation-head position. -/
theorem ANF.normalizeExpr_await_implies_hasAwaitInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.await arg, m)) :
    HasAwaitInHead e := by
  rcases ANF.normalizeExpr_await_or_k e k arg n m h with hleft | ⟨t, n', m', hk_await⟩
  · exact hleft
  · obtain ⟨m'', hm''⟩ := hk t n'
    rw [hm''] at hk_await
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_await)).1

end AwaitInHead

/-! ## HasReturnInHead: tracks .return in CPS-head position -/

section ReturnInHead

set_option autoImplicit true in
mutual
/-- Predicate tracking whether an expression has .return in CPS-head position.
    Structurally parallel to HasThrowInHead/HasAwaitInHead.
    Key difference: .return none and .return (some v) are BOTH unconditionally direct
    (the return continuation always produces .return). -/
inductive HasReturnInHead : Flat.Expr → Prop where
  | return_none_direct : HasReturnInHead (.return none)
  | return_some_direct : HasReturnInHead (.return (some v))
  | seq_left : HasReturnInHead a → HasReturnInHead (.seq a b)
  | seq_right : HasReturnInHead b → HasReturnInHead (.seq a b)
  | let_init : HasReturnInHead init → HasReturnInHead (.let name init body)
  | getProp_obj : HasReturnInHead obj → HasReturnInHead (.getProp obj prop)
  | setProp_obj : HasReturnInHead obj → HasReturnInHead (.setProp obj prop val)
  | setProp_val : HasReturnInHead val → HasReturnInHead (.setProp obj prop val)
  | binary_lhs : HasReturnInHead lhs → HasReturnInHead (.binary op lhs rhs)
  | binary_rhs : HasReturnInHead rhs → HasReturnInHead (.binary op lhs rhs)
  | unary_arg : HasReturnInHead arg → HasReturnInHead (.unary op arg)
  | typeof_arg : HasReturnInHead arg → HasReturnInHead (.typeof arg)
  | deleteProp_obj : HasReturnInHead obj → HasReturnInHead (.deleteProp obj prop)
  | assign_val : HasReturnInHead val → HasReturnInHead (.assign name val)
  | call_func : HasReturnInHead f → HasReturnInHead (.call f env args)
  | call_env : HasReturnInHead env → HasReturnInHead (.call f env args)
  | call_args : HasReturnInHeadList args → HasReturnInHead (.call f env args)
  | newObj_func : HasReturnInHead f → HasReturnInHead (.newObj f env args)
  | newObj_env : HasReturnInHead env → HasReturnInHead (.newObj f env args)
  | newObj_args : HasReturnInHeadList args → HasReturnInHead (.newObj f env args)
  | if_cond : HasReturnInHead c → HasReturnInHead (.if c t e)
  | throw_arg : HasReturnInHead arg → HasReturnInHead (.throw arg)
  | yield_some_arg : HasReturnInHead v → HasReturnInHead (.yield (some v) d)
  | await_arg : HasReturnInHead arg → HasReturnInHead (.await arg)
  | getIndex_obj : HasReturnInHead obj → HasReturnInHead (.getIndex obj idx)
  | getIndex_idx : HasReturnInHead idx → HasReturnInHead (.getIndex obj idx)
  | setIndex_obj : HasReturnInHead obj → HasReturnInHead (.setIndex obj idx val)
  | setIndex_idx : HasReturnInHead idx → HasReturnInHead (.setIndex obj idx val)
  | setIndex_val : HasReturnInHead val → HasReturnInHead (.setIndex obj idx val)
  | getEnv_env : HasReturnInHead env → HasReturnInHead (.getEnv env idx)
  | makeClosure_env : HasReturnInHead env → HasReturnInHead (.makeClosure funcIdx env)
  | makeEnv_values : HasReturnInHeadList values → HasReturnInHead (.makeEnv values)
  | objectLit_props : HasReturnInHeadProps props → HasReturnInHead (.objectLit props)
  | arrayLit_elems : HasReturnInHeadList elems → HasReturnInHead (.arrayLit elems)

inductive HasReturnInHeadList : List Flat.Expr → Prop where
  | head : HasReturnInHead e → HasReturnInHeadList (e :: rest)
  | tail : HasReturnInHeadList rest → HasReturnInHeadList (e :: rest)

inductive HasReturnInHeadProps : List (Flat.PropName × Flat.Expr) → Prop where
  | head : HasReturnInHead e → HasReturnInHeadProps ((name, e) :: rest)
  | tail : HasReturnInHeadProps rest → HasReturnInHeadProps (p :: rest)
end

/-- HasReturnInHead expressions are never values. -/
private theorem HasReturnInHead_not_value (e : Flat.Expr)
    (h : HasReturnInHead e) : Flat.exprValue? e = none := by
  cases h <;> simp [Flat.exprValue?]

/-- bindComplex never produces .return — it always produces .let. -/
theorem ANF.bindComplex_never_return_none_general (rhs : ANF.ComplexExpr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat)
    (h : (ANF.bindComplex rhs k).run n = .ok (.return none, m)) : False := by
  unfold ANF.bindComplex at h
  unfold ANF.freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure,
    StateT.pure, Except.pure] at h
  split at h <;> simp_all

theorem ANF.bindComplex_never_return_some_general (rhs : ANF.ComplexExpr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.bindComplex rhs k).run n = .ok (.return (some arg), m)) : False := by
  unfold ANF.bindComplex at h
  unfold ANF.freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure,
    StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-- normalizeExpr (.labeled l body) k never produces .return — result is always .labeled -/
theorem ANF.normalizeExpr_labeled_not_return_none (l : Flat.LabelName) (body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExpr (.labeled l body) k).run n = .ok (ANF.Expr.return none, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> simp_all

theorem ANF.normalizeExpr_labeled_not_return_some (l : Flat.LabelName) (body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.labeled l body) k).run n = .ok (.return (some arg), m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-- normalizeExpr (.while_ cond body) k never produces .return — result is always .seq -/
theorem ANF.normalizeExpr_while_not_return_none (cond_ body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExpr (.while_ cond_ body) k).run n = .ok (ANF.Expr.return none, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

theorem ANF.normalizeExpr_while_not_return_some (cond_ body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.while_ cond_ body) k).run n = .ok (.return (some arg), m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-- normalizeExpr (.tryCatch body cp cb fin) k never produces .return — always .tryCatch -/
theorem ANF.normalizeExpr_tryCatch_not_return_none (body : Flat.Expr) (cp : Flat.VarName)
    (cb : Flat.Expr) (fin : Option Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExpr (.tryCatch body cp cb fin) k).run n = .ok (ANF.Expr.return none, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map] at h
  cases fin with
  | none =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
  | some f =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

theorem ANF.normalizeExpr_tryCatch_not_return_some (body : Flat.Expr) (cp : Flat.VarName)
    (cb : Flat.Expr) (fin : Option Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr (.tryCatch body cp cb fin) k).run n = .ok (.return (some arg), m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map] at h
  cases fin with
  | none =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1
  | some f =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-! ## normalizeExprList/Props return_or_k helpers -/

private theorem normalizeExprList_return_none_or_k
    (es : List Flat.Expr)
    (ih : ∀ e, e ∈ es → ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (ANF.Expr.return none, m) →
      HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (ANF.Expr.return none, m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (ANF.Expr.return none, m)) :
    HasReturnInHeadList es ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat), (k ts).run n' = .ok (ANF.Expr.return none, m') := by
  induction es generalizing k n m with
  | nil => right; simp only [ANF.normalizeExprList] at h; exact ⟨[], n, m, h⟩
  | cons e rest ih_list =>
    simp only [ANF.normalizeExprList] at h
    rcases ih e (@List.mem_cons_self _ e rest) _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasReturnInHeadList.head hleft)
    · rcases ih_list (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) _ _ _ hkt with hleft | hright
      · exact Or.inl (HasReturnInHeadList.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨t :: ts, n'', m'', hkts⟩

private theorem normalizeExprList_return_some_or_k
    (es : List Flat.Expr)
    (ih : ∀ e, e ∈ es → ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.return (some arg), m) →
      HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.return (some arg), m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (.return (some arg), m)) :
    HasReturnInHeadList es ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat), (k ts).run n' = .ok (.return (some arg), m') := by
  induction es generalizing k arg n m with
  | nil => right; simp only [ANF.normalizeExprList] at h; exact ⟨[], n, m, h⟩
  | cons e rest ih_list =>
    simp only [ANF.normalizeExprList] at h
    rcases ih e (@List.mem_cons_self _ e rest) _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasReturnInHeadList.head hleft)
    · rcases ih_list (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasReturnInHeadList.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨t :: ts, n'', m'', hkts⟩

private theorem normalizeProps_return_none_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (ANF.Expr.return none, m) →
      HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (ANF.Expr.return none, m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (ANF.Expr.return none, m)) :
    HasReturnInHeadProps props ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat), (k ts).run n' = .ok (ANF.Expr.return none, m') := by
  induction props generalizing k n m with
  | nil => right; simp only [ANF.normalizeProps] at h; exact ⟨[], n, m, h⟩
  | cons p rest ih_list =>
    unfold ANF.normalizeProps at h
    rcases ih p.1 p.2 (@List.mem_cons_self _ _ rest) _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasReturnInHeadProps.head hleft)
    · rcases ih_list (fun name e he => ih name e (List.mem_cons_of_mem _ he)) _ _ _ hkt with hleft | hright
      · exact Or.inl (HasReturnInHeadProps.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨(p.1, t) :: ts, n'', m'', hkts⟩

private theorem normalizeProps_return_some_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.return (some arg), m) →
      HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.return (some arg), m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (.return (some arg), m)) :
    HasReturnInHeadProps props ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat), (k ts).run n' = .ok (.return (some arg), m') := by
  induction props generalizing k arg n m with
  | nil => right; simp only [ANF.normalizeProps] at h; exact ⟨[], n, m, h⟩
  | cons p rest ih_list =>
    unfold ANF.normalizeProps at h
    rcases ih p.1 p.2 (@List.mem_cons_self _ _ rest) _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasReturnInHeadProps.head hleft)
    · rcases ih_list (fun name e he => ih name e (List.mem_cons_of_mem _ he)) _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasReturnInHeadProps.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨(p.1, t) :: ts, n'', m'', hkts⟩

/-! ## Main theorem: normalizeExpr_return_or_k (none case) -/

/-- If normalizeExpr e k produces .return none, then either e has return in
    CPS-head position or k produced .return none. -/
theorem ANF.normalizeExpr_return_none_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (ANF.Expr.return none, m)) :
    HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (ANF.Expr.return none, m') :=
  normalizeExpr_return_none_or_k_aux e.depth e (Nat.le_refl _) k n m h
where
  normalizeExpr_return_none_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (ANF.Expr.return none, m)) :
      HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (ANF.Expr.return none, m') := by
    induction d generalizing e k n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | throw _ => simp [Flat.Expr.depth] at hd
      | «return» arg_r =>
        cases arg_r with
        | none => exact Or.inl HasReturnInHead.return_none_direct
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg_y _ =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | await _ => simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | «return» arg_r =>
        cases arg_r with
        | none => exact Or.inl HasReturnInHead.return_none_direct
        | some _ => exact Or.inl HasReturnInHead.return_some_direct
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | throw arg_flat =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_flat.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_flat ha _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.throw_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | yield arg_y dlg =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasReturnInHead.yield_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | await arg_a =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_a ha _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.await_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ h with hleft | ⟨_, n', m', hkb⟩
        · exact Or.inl (HasReturnInHead.seq_left hleft)
        · rcases ih b hb _ _ _ hkb with hleft | hright
          · exact Or.inl (HasReturnInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body =>
        exact absurd h (ANF.normalizeExpr_labeled_not_return_none l body k n m)
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_return_none c b k n m)
      | tryCatch body cp cb fin =>
        exact absurd h (ANF.normalizeExpr_tryCatch_not_return_none body cp cb fin k n m)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ h with hleft | ⟨tv, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_none_general _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_none_general _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_none_general _ _ _ _)
      | typeof arg_t =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_t.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_t ha _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_none_general _ _ _ _)
      | unary op arg_u =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_u.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_u ha _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_none_general _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_none_general _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_none_general _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_return_none_general _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_return_none_general _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_return_none_general _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, hk₃⟩
            · exact Or.inl (HasReturnInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_return_none_general _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.call_func hleft)
        · rcases ih env henv _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' n m,
                (ANF.normalizeExpr e k').run n = .ok (ANF.Expr.return none, m) →
                HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (ANF.Expr.return none, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_return_none_or_k args args_ih _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasReturnInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_return_none_general _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' n m,
                (ANF.normalizeExpr e k').run n = .ok (ANF.Expr.return none, m) →
                HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (ANF.Expr.return none, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_return_none_or_k args args_ih _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasReturnInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_return_none_general _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' n m,
            (ANF.normalizeExpr e k').run n = .ok (ANF.Expr.return none, m) →
            HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (ANF.Expr.return none, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_return_none_or_k values vals_ih _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasReturnInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_never_return_none_general _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' n m,
            (ANF.normalizeExpr e k').run n = .ok (ANF.Expr.return none, m) →
            HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (ANF.Expr.return none, m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_return_none_or_k props props_ih _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasReturnInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_never_return_none_general _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' n m,
            (ANF.normalizeExpr e k').run n = .ok (ANF.Expr.return none, m) →
            HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (ANF.Expr.return none, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_return_none_or_k elems elems_ih _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasReturnInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_never_return_none_general _ _ _ _)

/-! ## Main theorem: normalizeExpr_return_or_k (some case) -/

/-- If normalizeExpr e k produces .return (some arg), then either e has return in
    CPS-head position or k produced .return (some arg). -/
theorem ANF.normalizeExpr_return_some_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.return (some arg), m)) :
    HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.return (some arg), m') :=
  normalizeExpr_return_some_or_k_aux e.depth e (Nat.le_refl _) k arg n m h
where
  normalizeExpr_return_some_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (.return (some arg), m)) :
      HasReturnInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.return (some arg), m') := by
    induction d generalizing e k arg n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | throw _ => simp [Flat.Expr.depth] at hd
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg_y _ =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | await _ => simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => exact Or.inl HasReturnInHead.return_some_direct
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | throw arg_flat =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_flat.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_flat ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.throw_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | yield arg_y dlg =>
        cases arg_y with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasReturnInHead.yield_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | await arg_a =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_a ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.await_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ _ h with hleft | ⟨_, n', m', hkb⟩
        · exact Or.inl (HasReturnInHead.seq_left hleft)
        · rcases ih b hb _ _ _ _ hkb with hleft | hright
          · exact Or.inl (HasReturnInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body =>
        exact absurd h (ANF.normalizeExpr_labeled_not_return_some l body k arg n m)
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_return_some c b k arg n m)
      | tryCatch body cp cb fin =>
        exact absurd h (ANF.normalizeExpr_tryCatch_not_return_some body cp cb fin k arg n m)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ _ h with hleft | ⟨tv, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | typeof arg_t =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_t.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_t ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | unary op arg_u =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_u.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_u ha _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasReturnInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, hk₃⟩
            · exact Or.inl (HasReturnInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.call_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : ANF.Trivial) n m,
                (ANF.normalizeExpr e k').run n = .ok (.return (some arg'), m) →
                HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.return (some arg'), m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_return_some_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasReturnInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasReturnInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasReturnInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : ANF.Trivial) n m,
                (ANF.normalizeExpr e k').run n = .ok (.return (some arg'), m) →
                HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.return (some arg'), m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_return_some_or_k args args_ih _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasReturnInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.return (some arg'), m) →
            HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.return (some arg'), m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_return_some_or_k values vals_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasReturnInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.return (some arg'), m) →
            HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.return (some arg'), m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_return_some_or_k props props_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasReturnInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_never_return_some_general _ _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' (arg' : ANF.Trivial) n m,
            (ANF.normalizeExpr e k').run n = .ok (.return (some arg'), m) →
            HasReturnInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.return (some arg'), m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_return_some_or_k elems elems_ih _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasReturnInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_never_return_some_general _ _ _ _ _)

/-- MASTER INVERSION (return):
    If normalizeExpr e k = .ok (.return arg, m) with trivial-preserving k,
    then e has .return in evaluation-head position. -/
theorem ANF.normalizeExpr_return_implies_hasReturnInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (arg : Option ANF.Trivial) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.return arg, m)) :
    HasReturnInHead e := by
  cases arg with
  | none =>
    rcases ANF.normalizeExpr_return_none_or_k e k n m h with hleft | ⟨t, n', m', hk_ret⟩
    · exact hleft
    · obtain ⟨m'', hm''⟩ := hk t n'
      rw [hm''] at hk_ret
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_ret)).1
  | some arg_t =>
    rcases ANF.normalizeExpr_return_some_or_k e k arg_t n m h with hleft | ⟨t, n', m', hk_ret⟩
    · exact hleft
    · obtain ⟨m'', hm''⟩ := hk t n'
      rw [hm''] at hk_ret
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_ret)).1

end ReturnInHead

/-! ## HasYieldInHead: tracks .yield in CPS-head position -/

section YieldInHead

set_option autoImplicit true in
mutual
/-- An expression has .yield reachable through normalizeExpr's CPS evaluation path. -/
inductive HasYieldInHead : Flat.Expr → Prop where
  | yield_none_direct : HasYieldInHead (.yield none d)
  | yield_some_direct : HasYieldInHead (.yield (some v) d)
  | seq_left : HasYieldInHead a → HasYieldInHead (.seq a b)
  | seq_right : HasYieldInHead b → HasYieldInHead (.seq a b)
  | let_init : HasYieldInHead init → HasYieldInHead (.let name init body)
  | getProp_obj : HasYieldInHead obj → HasYieldInHead (.getProp obj prop)
  | setProp_obj : HasYieldInHead obj → HasYieldInHead (.setProp obj prop val)
  | setProp_val : HasYieldInHead val → HasYieldInHead (.setProp obj prop val)
  | binary_lhs : HasYieldInHead lhs → HasYieldInHead (.binary op lhs rhs)
  | binary_rhs : HasYieldInHead rhs → HasYieldInHead (.binary op lhs rhs)
  | unary_arg : HasYieldInHead arg → HasYieldInHead (.unary op arg)
  | typeof_arg : HasYieldInHead arg → HasYieldInHead (.typeof arg)
  | deleteProp_obj : HasYieldInHead obj → HasYieldInHead (.deleteProp obj prop)
  | assign_val : HasYieldInHead val → HasYieldInHead (.assign name val)
  | call_func : HasYieldInHead f → HasYieldInHead (.call f env args)
  | call_env : HasYieldInHead env → HasYieldInHead (.call f env args)
  | call_args : HasYieldInHeadList args → HasYieldInHead (.call f env args)
  | newObj_func : HasYieldInHead f → HasYieldInHead (.newObj f env args)
  | newObj_env : HasYieldInHead env → HasYieldInHead (.newObj f env args)
  | newObj_args : HasYieldInHeadList args → HasYieldInHead (.newObj f env args)
  | if_cond : HasYieldInHead c → HasYieldInHead (.if c t e)
  | throw_arg : HasYieldInHead arg → HasYieldInHead (.throw arg)
  | return_some_arg : HasYieldInHead v → HasYieldInHead (.return (some v))
  | await_arg : HasYieldInHead arg → HasYieldInHead (.await arg)
  | getIndex_obj : HasYieldInHead obj → HasYieldInHead (.getIndex obj idx)
  | getIndex_idx : HasYieldInHead idx → HasYieldInHead (.getIndex obj idx)
  | setIndex_obj : HasYieldInHead obj → HasYieldInHead (.setIndex obj idx val)
  | setIndex_idx : HasYieldInHead idx → HasYieldInHead (.setIndex obj idx val)
  | setIndex_val : HasYieldInHead val → HasYieldInHead (.setIndex obj idx val)
  | getEnv_env : HasYieldInHead env → HasYieldInHead (.getEnv env idx)
  | makeClosure_env : HasYieldInHead env → HasYieldInHead (.makeClosure funcIdx env)
  | makeEnv_values : HasYieldInHeadList values → HasYieldInHead (.makeEnv values)
  | objectLit_props : HasYieldInHeadProps props → HasYieldInHead (.objectLit props)
  | arrayLit_elems : HasYieldInHeadList elems → HasYieldInHead (.arrayLit elems)

/-- HasYieldInHead for lists (some element has yield in head) -/
inductive HasYieldInHeadList : List Flat.Expr → Prop where
  | head : HasYieldInHead e → HasYieldInHeadList (e :: rest)
  | tail : HasYieldInHeadList rest → HasYieldInHeadList (e :: rest)

/-- HasYieldInHead for prop lists (some prop value has yield in head) -/
inductive HasYieldInHeadProps : List (Flat.PropName × Flat.Expr) → Prop where
  | head : HasYieldInHead e → HasYieldInHeadProps ((name, e) :: rest)
  | tail : HasYieldInHeadProps rest → HasYieldInHeadProps (p :: rest)
end

/-- HasYieldInHead expressions are never values. -/
private theorem HasYieldInHead_not_value (e : Flat.Expr)
    (h : HasYieldInHead e) : Flat.exprValue? e = none := by
  cases h <;> simp [Flat.exprValue?]

/-! ## Helper: bindComplex never produces .yield -/

/-- bindComplex always wraps its result in .let, so it can NEVER produce .yield. -/
theorem ANF.bindComplex_never_yield_general (rhs : ANF.ComplexExpr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.bindComplex rhs k).run n = .ok (.yield arg delegate, m)) : False := by
  unfold ANF.bindComplex at h
  unfold ANF.freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure,
    StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-! ## Helpers: wrapping constructors never produce .yield -/

/-- normalizeExpr (.labeled l body) k never produces .yield — result is always .labeled -/
theorem ANF.normalizeExpr_labeled_not_yield (l : Flat.LabelName) (body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.normalizeExpr (.labeled l body) k).run n = .ok (.yield arg delegate, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> simp_all

/-- normalizeExpr (.while_ cond body) k never produces .yield — result is always .seq -/
theorem ANF.normalizeExpr_while_not_yield (cond_ body : Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.normalizeExpr (.while_ cond_ body) k).run n = .ok (.yield arg delegate, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-- normalizeExpr (.tryCatch body cp cb fin) k never produces .yield — always .tryCatch -/
theorem ANF.normalizeExpr_tryCatch_not_yield (body : Flat.Expr) (cp : Flat.VarName)
    (cb : Flat.Expr) (fin : Option Flat.Expr)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.normalizeExpr (.tryCatch body cp cb fin) k).run n = .ok (.yield arg delegate, m)) : False := by
  simp only [ANF.normalizeExpr, bind, Bind.bind, StateT.bind, StateT.run,
    Except.bind, pure, Pure.pure, StateT.pure, Except.pure, Functor.map, StateT.map] at h
  cases fin with
  | none =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h <;> (try split at h) <;> simp_all
  | some f =>
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind, pure, Pure.pure,
      StateT.pure, Except.pure] at h
    split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-! ## normalizeExprList/Props yield_or_k helpers -/

private theorem normalizeExprList_yield_or_k
    (es : List Flat.Expr)
    (ih : ∀ e, e ∈ es → ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr)
      (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.yield arg delegate, m) →
      HasYieldInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.yield arg delegate, m'))
    (k : List ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.normalizeExprList es k).run n = .ok (.yield arg delegate, m)) :
    HasYieldInHeadList es ∨ ∃ (ts : List ANF.Trivial) (n' m' : Nat), (k ts).run n' = .ok (.yield arg delegate, m') := by
  induction es generalizing k arg delegate n m with
  | nil => right; simp only [ANF.normalizeExprList] at h; exact ⟨[], n, m, h⟩
  | cons e rest ih_list =>
    simp only [ANF.normalizeExprList] at h
    rcases ih e (@List.mem_cons_self _ e rest) _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasYieldInHeadList.head hleft)
    · rcases ih_list (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) _ _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasYieldInHeadList.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨t :: ts, n'', m'', hkts⟩

/-- normalizeProps: yield in result comes from some prop value or from k. -/
private theorem normalizeProps_yield_or_k
    (props : List (Flat.PropName × Flat.Expr))
    (ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
      ∀ (k' : ANF.Trivial → ANF.ConvM ANF.Expr)
      (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat),
      (ANF.normalizeExpr e k').run n = .ok (.yield arg delegate, m) →
      HasYieldInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k' t).run n' = .ok (.yield arg delegate, m'))
    (k : List (ANF.PropName × ANF.Trivial) → ANF.ConvM ANF.Expr)
    (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.normalizeProps props k).run n = .ok (.yield arg delegate, m)) :
    HasYieldInHeadProps props ∨ ∃ (ts : List (ANF.PropName × ANF.Trivial)) (n' m' : Nat), (k ts).run n' = .ok (.yield arg delegate, m') := by
  induction props generalizing k arg delegate n m with
  | nil => right; simp only [ANF.normalizeProps] at h; exact ⟨[], n, m, h⟩
  | cons p rest ih_list =>
    unfold ANF.normalizeProps at h
    rcases ih p.1 p.2 (@List.mem_cons_self _ _ rest) _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
    · exact Or.inl (HasYieldInHeadProps.head hleft)
    · rcases ih_list (fun name e he => ih name e (List.mem_cons_of_mem _ he)) _ _ _ _ _ hkt with hleft | hright
      · exact Or.inl (HasYieldInHeadProps.tail hleft)
      · obtain ⟨ts, n'', m'', hkts⟩ := hright
        exact Or.inr ⟨(p.1, t) :: ts, n'', m'', hkts⟩

/-! ## Main theorem: normalizeExpr_yield_or_k -/

/-- If normalizeExpr e k produces .yield arg delegate, then either e has yield in
    CPS-head position or k produced .yield arg delegate. -/
theorem ANF.normalizeExpr_yield_or_k
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.yield arg delegate, m)) :
    HasYieldInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.yield arg delegate, m') :=
  normalizeExpr_yield_or_k_aux e.depth e (Nat.le_refl _) k arg delegate n m h
where
  /-- Helper: general yield characterization by strong induction on expression depth. -/
  normalizeExpr_yield_or_k_aux (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
      (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
      (h : (ANF.normalizeExpr e k).run n = .ok (.yield arg delegate, m)) :
      HasYieldInHead e ∨ ∃ (t : ANF.Trivial) (n' m' : Nat), (k t).run n' = .ok (.yield arg delegate, m') := by
    induction d generalizing e k arg delegate n m with
    | zero =>
      cases e with
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | throw _ => simp [Flat.Expr.depth] at hd
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some _ => simp [Flat.Expr.depth] at hd
      | yield arg_y _ =>
        cases arg_y with
        | none => exact Or.inl HasYieldInHead.yield_none_direct
        | some _ => simp [Flat.Expr.depth] at hd
      | await _ => simp [Flat.Expr.depth] at hd
      | tryCatch _ _ _ fin => cases fin <;> (simp [Flat.Expr.depth] at hd; try omega)
      | _ => simp [Flat.Expr.depth] at hd; try omega
    | succ d' ih =>
      cases e with
      | yield arg_y dlg =>
        cases arg_y with
        | none => exact Or.inl HasYieldInHead.yield_none_direct
        | some _ => exact Or.inl HasYieldInHead.yield_some_direct
      | var name => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var name, n, m, h⟩
      | this => right; simp only [ANF.normalizeExpr] at h; exact ⟨.var "this", n, m, h⟩
      | lit v =>
        right; simp only [ANF.normalizeExpr] at h
        cases htv : ANF.trivialOfFlatValue v with
        | error msg =>
          rw [htv] at h
          change StateT.lift (Except.error msg) n = _ at h
          simp [StateT.lift, Functor.map, Except.map] at h
        | ok triv => rw [htv] at h; exact ⟨triv, n, m, h⟩
      | «break» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | «continue» l =>
        simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
        exact absurd h (by simp)
      | throw arg_flat =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_flat.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_flat ha _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.throw_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | «return» arg_r =>
        cases arg_r with
        | none =>
          simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at h
          exact absurd h (by simp)
        | some v =>
          simp only [ANF.normalizeExpr] at h
          have hv : v.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
          rcases ih v hv _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
          · exact Or.inl (HasYieldInHead.return_some_arg hleft)
          · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | await arg_a =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_a ha _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.await_arg hleft)
        · simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hkt
      | seq a b =>
        simp only [ANF.normalizeExpr] at h
        have ha : a.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hb : b.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih a ha _ _ _ _ _ h with hleft | ⟨_, n', m', hkb⟩
        · exact Or.inl (HasYieldInHead.seq_left hleft)
        · rcases ih b hb _ _ _ _ _ hkb with hleft | hright
          · exact Or.inl (HasYieldInHead.seq_right hleft)
          · exact Or.inr hright
      | «let» name init body =>
        simp only [ANF.normalizeExpr] at h
        have hi : init.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih init hi _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.let_init hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> simp_all
      | labeled l body =>
        exact absurd h (ANF.normalizeExpr_labeled_not_yield l body k arg delegate n m)
      | while_ c b =>
        exact absurd h (ANF.normalizeExpr_while_not_yield c b k arg delegate n m)
      | tryCatch body cp cb fin =>
        exact absurd h (ANF.normalizeExpr_tryCatch_not_yield body cp cb fin k arg delegate n m)
      | «if» c t e =>
        simp only [ANF.normalizeExpr] at h
        have hc : c.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih c hc _ _ _ _ _ h with hleft | ⟨tv, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.if_cond hleft)
        · simp only [bind, Bind.bind, StateT.bind, StateT.run, pure, Pure.pure, StateT.pure,
            Except.pure, Except.bind] at hkt
          split at hkt <;> (try simp_all)
          split at hkt <;> simp_all
      | assign name val =>
        simp only [ANF.normalizeExpr] at h
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih val hv _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.assign_val hleft)
        · exact absurd hkt (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | getProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.getProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | deleteProp obj prop =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.deleteProp_obj hleft)
        · exact absurd hkt (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | typeof arg_t =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_t.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_t ha _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.typeof_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | unary op arg_u =>
        simp only [ANF.normalizeExpr] at h
        have ha : arg_u.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih arg_u ha _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.unary_arg hleft)
        · exact absurd hkt (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | getEnv envPtr idx =>
        simp only [ANF.normalizeExpr] at h
        have he : envPtr.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih envPtr he _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.getEnv_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | makeClosure funcIdx env =>
        simp only [ANF.normalizeExpr] at h
        have he : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih env he _ _ _ _ _ h with hleft | ⟨t, n', m', hkt⟩
        · exact Or.inl (HasYieldInHead.makeClosure_env hleft)
        · exact absurd hkt (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | setProp obj prop val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasYieldInHead.setProp_obj hleft)
        · rcases ih val hv _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasYieldInHead.setProp_val hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | binary op lhs rhs =>
        simp only [ANF.normalizeExpr] at h
        have hl : lhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hr : rhs.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih lhs hl _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasYieldInHead.binary_lhs hleft)
        · rcases ih rhs hr _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasYieldInHead.binary_rhs hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | getIndex obj idx =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasYieldInHead.getIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasYieldInHead.getIndex_idx hleft)
          · exact absurd hk₂ (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | setIndex obj idx val =>
        simp only [ANF.normalizeExpr] at h
        have ho : obj.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hi : idx.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hv : val.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih obj ho _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasYieldInHead.setIndex_obj hleft)
        · rcases ih idx hi _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasYieldInHead.setIndex_idx hleft)
          · rcases ih val hv _ _ _ _ _ hk₂ with hleft | ⟨t₃, n₃, m₃, hk₃⟩
            · exact Or.inl (HasYieldInHead.setIndex_val hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | call f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasYieldInHead.call_func hleft)
        · rcases ih env henv _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasYieldInHead.call_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : Option ANF.Trivial) (dlg : Bool) n m,
                (ANF.normalizeExpr e k').run n = .ok (.yield arg' dlg, m) →
                HasYieldInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.yield arg' dlg, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_yield_or_k args args_ih _ _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasYieldInHead.call_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | newObj f env args =>
        simp only [ANF.normalizeExpr] at h
        have hf : f.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have henv : env.depth ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have hargs : Flat.Expr.listDepth args ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        rcases ih f hf _ _ _ _ _ h with hleft | ⟨t₁, n₁, m₁, hk₁⟩
        · exact Or.inl (HasYieldInHead.newObj_func hleft)
        · rcases ih env henv _ _ _ _ _ hk₁ with hleft | ⟨t₂, n₂, m₂, hk₂⟩
          · exact Or.inl (HasYieldInHead.newObj_env hleft)
          · have args_ih : ∀ e, e ∈ args → ∀ k' (arg' : Option ANF.Trivial) (dlg : Bool) n m,
                (ANF.normalizeExpr e k').run n = .ok (.yield arg' dlg, m) →
                HasYieldInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.yield arg' dlg, m') :=
              fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
            rcases normalizeExprList_yield_or_k args args_ih _ _ _ _ _ hk₂ with hleft | ⟨ts, n₃, m₃, hk₃⟩
            · exact Or.inl (HasYieldInHead.newObj_args hleft)
            · exact absurd hk₃ (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | makeEnv values =>
        simp only [ANF.normalizeExpr] at h
        have hvals : Flat.Expr.listDepth values ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have vals_ih : ∀ e, e ∈ values → ∀ k' (arg' : Option ANF.Trivial) (dlg : Bool) n m,
            (ANF.normalizeExpr e k').run n = .ok (.yield arg' dlg, m) →
            HasYieldInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.yield arg' dlg, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_yield_or_k values vals_ih _ _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasYieldInHead.makeEnv_values hleft)
        · exact absurd hk (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | objectLit props =>
        simp only [ANF.normalizeExpr] at h
        have hprops : Flat.Expr.propListDepth props ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have props_ih : ∀ (name : Flat.PropName) (e : Flat.Expr), (name, e) ∈ props →
            ∀ k' (arg' : Option ANF.Trivial) (dlg : Bool) n m,
            (ANF.normalizeExpr e k').run n = .ok (.yield arg' dlg, m) →
            HasYieldInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.yield arg' dlg, m') :=
          fun name e he => ih e (by have := Flat.Expr.mem_propListDepth_lt he; omega)
        rcases normalizeProps_yield_or_k props props_ih _ _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasYieldInHead.objectLit_props hleft)
        · exact absurd hk (ANF.bindComplex_never_yield_general _ _ _ _ _ _)
      | arrayLit elems =>
        simp only [ANF.normalizeExpr] at h
        have helems : Flat.Expr.listDepth elems ≤ d' := by simp [Flat.Expr.depth] at hd; omega
        have elems_ih : ∀ e, e ∈ elems → ∀ k' (arg' : Option ANF.Trivial) (dlg : Bool) n m,
            (ANF.normalizeExpr e k').run n = .ok (.yield arg' dlg, m) →
            HasYieldInHead e ∨ ∃ t n' m', (k' t).run n' = .ok (.yield arg' dlg, m') :=
          fun e he => ih e (by have := Flat.Expr.mem_listDepth_lt he; omega)
        rcases normalizeExprList_yield_or_k elems elems_ih _ _ _ _ _ h with hleft | ⟨ts, n', m', hk⟩
        · exact Or.inl (HasYieldInHead.arrayLit_elems hleft)
        · exact absurd hk (ANF.bindComplex_never_yield_general _ _ _ _ _ _)

/-- If normalizeExpr produces .yield with trivial-preserving k, then e has .yield in head. -/
theorem ANF.normalizeExpr_yield_implies_hasYieldInHead
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ (t : ANF.Trivial) (n : Nat), ∃ m, (k t).run n = .ok (.trivial t, m))
    (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.yield arg delegate, m)) :
    HasYieldInHead e := by
  rcases ANF.normalizeExpr_yield_or_k e k arg delegate n m h with hleft | ⟨t, n', m', hk_yield⟩
  · exact hleft
  · obtain ⟨m'', hm''⟩ := hk t n'
    rw [hm''] at hk_yield
    exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hk_yield)).1

end YieldInHead

/-- When normalizeExpr sf.expr k produces .labeled label body, there exist Flat steps
    from sf to sf' such that normalizeExpr sf'.expr k' produces body (with k' trivial-preserving).
    The .labeled may be embedded inside .seq chains or compound expression prefixes;
    the Flat machine steps through these to reach the underlying .labeled statement. -/
private theorem normalizeExpr_labeled_step_sim :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
      (label : String) (body : ANF.Expr),
    (∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m')) →
    (ANF.normalizeExpr e k).run n = .ok (ANF.Expr.labeled label body, m) →
    ∀ (sf : Flat.State), sf.expr = e → ExprWellFormed e sf.env →
    ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
      Flat.Steps sf evs sf' ∧
      (∃ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n' m' : Nat),
        (ANF.normalizeExpr sf'.expr k').run n' = .ok (body, m') ∧
        (∀ (arg : ANF.Trivial) (n'' : Nat), ∃ m'', (k' arg).run n'' = .ok (.trivial arg, m''))) ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      observableTrace sf'.trace = observableTrace sf.trace ∧
      observableTrace evs = [] ∧
      ExprWellFormed sf'.expr sf'.env := by
  intro d
  induction d with
  | zero =>
    intro e hd k n m label body hk hnorm sf hsf hwf
    cases e with
    | var name =>
      exfalso; simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hm'⟩ := hk (.var name) n
      rw [hm'] at hnorm; exact absurd hnorm (by intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1)
    | this =>
      exfalso; simp only [ANF.normalizeExpr] at hnorm
      obtain ⟨m', hm'⟩ := hk (.var "this") n
      rw [hm'] at hnorm; exact absurd hnorm (by intro h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1)
    | lit v =>
      exfalso; simp only [ANF.normalizeExpr] at hnorm
      cases htv : ANF.trivialOfFlatValue v with
      | error msg => simp [htv] at hnorm; exact absurd hnorm (by simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map])
      | ok triv => simp [htv] at hnorm; obtain ⟨m', hm'⟩ := hk triv n; rw [hm'] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
    | «break» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
    | «continue» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
    | «return» arg =>
      cases arg with
      | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | some _ => exfalso; simp [Flat.Expr.depth] at hd
    | yield arg _ =>
      cases arg with
      | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
      | some _ => exfalso; simp [Flat.Expr.depth] at hd
    | tryCatch _ _ _ fin => exfalso; cases fin <;> simp [Flat.Expr.depth] at hd
    | _ => exfalso; simp [Flat.Expr.depth] at hd
  | succ d ih =>
    intro e hd k n m label body hk hnorm sf hsf hwf
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
        | some val =>
          -- normalizeExpr (.return (some val)) k = normalizeExpr val (fun t => pure (.return (some t)))
          -- The outer k is discarded. .labeled can only come from val having .labeled in first position.
          simp only [ANF.normalizeExpr] at hnorm
          -- hnorm : (normalizeExpr val (fun t => pure (.return (some t)))).run n = .ok (.labeled label body, m)
          -- We proceed by cases on val. If val = .labeled, we can directly construct the witness.
          cases val with
          | labeled l b_flat =>
            unfold ANF.normalizeExpr at hnorm
            simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
            -- hnorm now has a match on normalizeExpr b_flat ...
            -- Since RHS is .ok, the match must be .ok
            generalize hbf : ANF.normalizeExpr b_flat
              (fun t => pure (ANF.Expr.return (some t))) n = res at hnorm
            cases res with
            | error msg => simp at hnorm
            | ok v =>
              simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hnorm
              -- One Flat step: .return (some (.labeled label b_flat)) → .return (some b_flat)
              have hstep_ret : ∃ s', Flat.step? sf = some (.silent, s') ∧
                  s'.expr = .return (some b_flat) ∧ s'.env = sf.env ∧ s'.heap = sf.heap ∧
                  s'.trace = sf.trace ++ [Core.TraceEvent.silent] := by
                have hsf_eq : sf = { sf with expr := Flat.Expr.return (some (Flat.Expr.labeled label b_flat)) } := by
                  cases sf; simp_all
                rw [hsf_eq]; unfold Flat.step?; simp [Flat.exprValue?, Flat.step?]
              obtain ⟨s', hstep_s, hexpr_s, henv_s, hheap_s, htrace_s⟩ := hstep_ret
              refine ⟨[.silent], s', .tail ⟨hstep_s⟩ (.refl _), ?_, henv_s, hheap_s, ?_, rfl, ?_⟩
              · -- normalizeExpr (.return (some b_flat)) k' = body
                refine ⟨fun arg => pure (.trivial arg), n, v.2, ?_, ?_⟩
                · rw [hexpr_s]; simp only [ANF.normalizeExpr, StateT.run]; exact hbf
                · intro arg n''; exact ⟨n'', by simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]⟩
              · rw [htrace_s, observableTrace_append]; simp [observableTrace]; decide
              · rw [hexpr_s, henv_s]; intro x hfx; cases hfx with
                | return_some_arg _ _ hinner => exact hwf x (VarFreeIn.return_some_arg _ _ (VarFreeIn.labeled_body _ _ _ hinner))
          | var name =>
            exfalso
            simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
          | lit v =>
            exfalso; simp only [ANF.normalizeExpr] at hnorm
            cases htv : ANF.trivialOfFlatValue v with
            | error msg => simp [htv, StateT.lift, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at hnorm
            | ok triv => simp [htv, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
          | this =>
            exfalso
            simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
          | «break» _ | «continue» _ =>
            exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
          | «return» arg =>
            cases arg with
            | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
            | some inner_val =>
              -- hnorm : normalizeExpr (return (some inner_val)) return_k n = ok (.labeled label body, m)
              -- which equals: normalizeExpr inner_val return_k n = ok (.labeled label body, m)
              -- sf.expr = return (some (return (some inner_val)))
              simp only [ANF.normalizeExpr] at hnorm
              -- Now case split inner_val for the labeled base case
              cases inner_val with
              | labeled l b_flat =>
                unfold ANF.normalizeExpr at hnorm
                simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
                generalize hbf : ANF.normalizeExpr b_flat
                  (fun t => pure (ANF.Expr.return (some t))) n = res at hnorm
                cases res with
                | error msg => simp at hnorm
                | ok v =>
                  simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hnorm
                  -- One Flat step through double return: unwrap .labeled
                  have hstep_ret : ∃ s', Flat.step? sf = some (.silent, s') ∧
                      s'.expr = .return (some (.return (some b_flat))) ∧
                      s'.env = sf.env ∧ s'.heap = sf.heap ∧
                      s'.trace = sf.trace ++ [Core.TraceEvent.silent] := by
                    have hsf_eq : sf = { sf with expr := Flat.Expr.return (some (Flat.Expr.return (some (Flat.Expr.labeled label b_flat)))) } := by
                      cases sf; simp_all
                    rw [hsf_eq]; unfold Flat.step?; simp [Flat.exprValue?, Flat.step?]
                  obtain ⟨s', hstep_s, hexpr_s, henv_s, hheap_s, htrace_s⟩ := hstep_ret
                  refine ⟨[.silent], s', .tail ⟨hstep_s⟩ (.refl _), ?_, henv_s, hheap_s, ?_, rfl, ?_⟩
                  · refine ⟨fun arg => pure (.trivial arg), n, v.2, ?_, ?_⟩
                    · rw [hexpr_s]; simp only [ANF.normalizeExpr, StateT.run]; exact hbf
                    · intro arg n''; exact ⟨n'', by simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]⟩
                  · rw [htrace_s, observableTrace_append]; simp [observableTrace]; decide
                  · rw [hexpr_s, henv_s]; intro x hfx; cases hfx with
                    | return_some_arg _ _ h1 => cases h1 with
                      | return_some_arg _ _ h2 => exact hwf x (VarFreeIn.return_some_arg _ _ (VarFreeIn.return_some_arg _ _ (VarFreeIn.labeled_body _ _ _ h2)))
              | _ => sorry -- non-labeled inner value: needs eval context lifting
          | yield arg delegate =>
            cases arg with
            | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
            | some inner_val =>
              simp only [ANF.normalizeExpr] at hnorm
              cases inner_val with
              | labeled l b_flat =>
                unfold ANF.normalizeExpr at hnorm
                simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
                generalize hbf : ANF.normalizeExpr b_flat
                  (fun t => pure (ANF.Expr.yield (some t) delegate)) n = res at hnorm
                cases res with
                | error msg => simp at hnorm
                | ok v =>
                  simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hnorm
                  have hstep_ret : ∃ s', Flat.step? sf = some (.silent, s') ∧
                      s'.expr = .return (some (.yield (some b_flat) delegate)) ∧
                      s'.env = sf.env ∧ s'.heap = sf.heap ∧
                      s'.trace = sf.trace ++ [Core.TraceEvent.silent] := by
                    have hsf_eq : sf = { sf with expr := Flat.Expr.return (some (Flat.Expr.yield (some (Flat.Expr.labeled label b_flat)) delegate)) } := by
                      cases sf; simp_all
                    rw [hsf_eq]; unfold Flat.step?; simp [Flat.exprValue?, Flat.step?]
                  obtain ⟨s', hstep_s, hexpr_s, henv_s, hheap_s, htrace_s⟩ := hstep_ret
                  refine ⟨[.silent], s', .tail ⟨hstep_s⟩ (.refl _), ?_, henv_s, hheap_s, ?_, rfl, ?_⟩
                  · refine ⟨fun arg => pure (.trivial arg), n, v.2, ?_, ?_⟩
                    · rw [hexpr_s]; simp only [ANF.normalizeExpr, StateT.run]; exact hbf
                    · intro arg n''; exact ⟨n'', by simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]⟩
                  · rw [htrace_s, observableTrace_append]; simp [observableTrace]; decide
                  · rw [hexpr_s, henv_s]; intro x hfx; cases hfx with
                    | return_some_arg _ _ h1 => cases h1 with
                      | yield_some_arg _ _ _ h2 => exact hwf x (VarFreeIn.return_some_arg _ _ (VarFreeIn.yield_some_arg _ _ _ (VarFreeIn.labeled_body _ _ _ h2)))
              | _ => sorry -- non-labeled inner value: needs eval context lifting
          | while_ _ _ =>
            exfalso; unfold ANF.normalizeExpr at hnorm
            simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
            repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm))
          | tryCatch _ _ _ _ =>
            exfalso; unfold ANF.normalizeExpr at hnorm
            simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
            cases ‹Option Flat.Expr› with
            | none => simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm; repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
            | some _ => simp only [Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm; repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
          | _ => sorry -- compound/bindComplex cases: needs induction on depth
      | yield arg delegate =>
        cases arg with
        | none =>
          exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm
          exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
        | some val =>
          simp only [ANF.normalizeExpr] at hnorm
          cases val with
          | labeled l b_flat =>
            unfold ANF.normalizeExpr at hnorm
            simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
            generalize hbf : ANF.normalizeExpr b_flat
              (fun t => pure (ANF.Expr.yield (some t) delegate)) n = res at hnorm
            cases res with
            | error msg => simp at hnorm
            | ok v =>
              simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hnorm
              have hstep_ret : ∃ s', Flat.step? sf = some (.silent, s') ∧
                  s'.expr = .yield (some b_flat) delegate ∧ s'.env = sf.env ∧ s'.heap = sf.heap ∧
                  s'.trace = sf.trace ++ [Core.TraceEvent.silent] := by
                have hsf_eq : sf = { sf with expr := Flat.Expr.yield (some (Flat.Expr.labeled label b_flat)) delegate } := by
                  cases sf; simp_all
                rw [hsf_eq]; unfold Flat.step?; simp [Flat.exprValue?, Flat.step?]
              obtain ⟨s', hstep_s, hexpr_s, henv_s, hheap_s, htrace_s⟩ := hstep_ret
              refine ⟨[.silent], s', .tail ⟨hstep_s⟩ (.refl _), ?_, henv_s, hheap_s, ?_, rfl, ?_⟩
              · refine ⟨fun arg => pure (.trivial arg), n, v.2, ?_, ?_⟩
                · rw [hexpr_s]; simp only [ANF.normalizeExpr, StateT.run]; exact hbf
                · intro arg n''; exact ⟨n'', by simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]⟩
              · rw [htrace_s, observableTrace_append]; simp [observableTrace]; decide
              · rw [hexpr_s, henv_s]; intro x hfx; cases hfx with
                | yield_some_arg _ _ _ h1 => exact hwf x (VarFreeIn.yield_some_arg _ _ _ (VarFreeIn.labeled_body _ _ _ h1))
          | var name =>
            exfalso
            simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
          | lit v =>
            exfalso; simp only [ANF.normalizeExpr] at hnorm
            cases htv : ANF.trivialOfFlatValue v with
            | error msg => simp [htv, StateT.lift, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at hnorm
            | ok triv => simp [htv, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
          | this =>
            exfalso
            simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
          | «break» _ | «continue» _ =>
            exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm
            exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
          | «return» arg =>
            cases arg with
            | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
            | some inner_val =>
              simp only [ANF.normalizeExpr] at hnorm
              cases inner_val with
              | labeled l b_flat =>
                unfold ANF.normalizeExpr at hnorm
                simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
                generalize hbf : ANF.normalizeExpr b_flat
                  (fun t => pure (ANF.Expr.return (some t))) n = res at hnorm
                cases res with
                | error msg => simp at hnorm
                | ok v =>
                  simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hnorm
                  have hstep_ret : ∃ s', Flat.step? sf = some (.silent, s') ∧
                      s'.expr = .yield (some (.return (some b_flat))) delegate ∧
                      s'.env = sf.env ∧ s'.heap = sf.heap ∧
                      s'.trace = sf.trace ++ [Core.TraceEvent.silent] := by
                    have hsf_eq : sf = { sf with expr := Flat.Expr.yield (some (Flat.Expr.return (some (Flat.Expr.labeled label b_flat)))) delegate } := by
                      cases sf; simp_all
                    rw [hsf_eq]; unfold Flat.step?; simp [Flat.exprValue?, Flat.step?]
                  obtain ⟨s', hstep_s, hexpr_s, henv_s, hheap_s, htrace_s⟩ := hstep_ret
                  refine ⟨[.silent], s', .tail ⟨hstep_s⟩ (.refl _), ?_, henv_s, hheap_s, ?_, rfl, ?_⟩
                  · refine ⟨fun arg => pure (.trivial arg), n, v.2, ?_, ?_⟩
                    · rw [hexpr_s]; simp only [ANF.normalizeExpr, StateT.run]; exact hbf
                    · intro arg n''; exact ⟨n'', by simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]⟩
                  · rw [htrace_s, observableTrace_append]; simp [observableTrace]; decide
                  · rw [hexpr_s, henv_s]; intro x hfx; cases hfx with
                    | yield_some_arg _ _ _ h1 => cases h1 with
                      | return_some_arg _ _ h2 => exact hwf x (VarFreeIn.yield_some_arg _ _ _ (VarFreeIn.return_some_arg _ _ (VarFreeIn.labeled_body _ _ _ h2)))
              | _ => sorry -- non-labeled inner value: needs eval context lifting
          | yield arg delegate' =>
            cases arg with
            | none => exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
            | some inner_val =>
              simp only [ANF.normalizeExpr] at hnorm
              cases inner_val with
              | labeled l b_flat =>
                unfold ANF.normalizeExpr at hnorm
                simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
                generalize hbf : ANF.normalizeExpr b_flat
                  (fun t => pure (ANF.Expr.yield (some t) delegate')) n = res at hnorm
                cases res with
                | error msg => simp at hnorm
                | ok v =>
                  simp only [pure, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hnorm
                  have hstep_ret : ∃ s', Flat.step? sf = some (.silent, s') ∧
                      s'.expr = .yield (some (.yield (some b_flat) delegate')) delegate ∧
                      s'.env = sf.env ∧ s'.heap = sf.heap ∧
                      s'.trace = sf.trace ++ [Core.TraceEvent.silent] := by
                    have hsf_eq : sf = { sf with expr := Flat.Expr.yield (some (Flat.Expr.yield (some (Flat.Expr.labeled label b_flat)) delegate')) delegate } := by
                      cases sf; simp_all
                    rw [hsf_eq]; unfold Flat.step?; simp [Flat.exprValue?, Flat.step?]
                  obtain ⟨s', hstep_s, hexpr_s, henv_s, hheap_s, htrace_s⟩ := hstep_ret
                  refine ⟨[.silent], s', .tail ⟨hstep_s⟩ (.refl _), ?_, henv_s, hheap_s, ?_, rfl, ?_⟩
                  · refine ⟨fun arg => pure (.trivial arg), n, v.2, ?_, ?_⟩
                    · rw [hexpr_s]; simp only [ANF.normalizeExpr, StateT.run]; exact hbf
                    · intro arg n''; exact ⟨n'', by simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]⟩
                  · rw [htrace_s, observableTrace_append]; simp [observableTrace]; decide
                  · rw [hexpr_s, henv_s]; intro x hfx; cases hfx with
                    | yield_some_arg _ _ _ h1 => cases h1 with
                      | yield_some_arg _ _ _ h2 => exact hwf x (VarFreeIn.yield_some_arg _ _ _ (VarFreeIn.yield_some_arg _ _ _ (VarFreeIn.labeled_body _ _ _ h2)))
              | _ => sorry -- non-labeled inner value: needs eval context lifting
          | while_ _ _ =>
            exfalso; unfold ANF.normalizeExpr at hnorm
            simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
            repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm))
          | tryCatch _ _ _ _ =>
            exfalso; unfold ANF.normalizeExpr at hnorm
            simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
            cases ‹Option Flat.Expr› with
            | none => simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm; repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
            | some _ => simp only [Functor.map, StateT.map, StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm; repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
          | _ => sorry -- compound/bindComplex cases: needs induction on depth
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
      | _ => sorry -- compound/bindComplex/throw/await cases: needs induction on depth

/-- If an expression has break in its evaluation head, then Flat stepping produces the
    break error. The expression is evaluated through evaluation contexts until the
    break statement is reached, at which point the error propagates via Fix D.
    NOTE: This theorem is FALSE for compound cases. See analysis in
    agents/wasmspec/break_analysis.md. The conclusion `sf'.env = sf.env ∧ sf'.heap = sf.heap`
    fails when evaluation contexts contain env-modifying sub-expressions (assign, let),
    and `sf'.expr = .lit .undefined` fails for seq_left (dead code after break evaluates
    to an arbitrary value, not .lit .undefined).
    The break_direct case IS proved; compound cases remain sorry. -/
private theorem hasBreakInHead_flat_error_steps
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label)
    (sf : Flat.State) (hsf : sf.expr = e)
    (hewf : ExprWellFormed e sf.env) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      sf'.expr = .lit .undefined ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.funcs = sf.funcs ∧ sf'.callStack = sf.callStack ∧
      sf'.trace = sf.trace ++ evs ∧
      observableTrace evs = observableTrace [.error ("break:" ++ label.getD "")] := by
  cases h with
  | break_direct =>
    obtain ⟨e_, env_, heap_, trace_, funcs_, cs_⟩ := sf
    subst hsf
    exact ⟨⟨.lit .undefined, env_, heap_, trace_ ++ [.error ("break:" ++ label.getD "")], funcs_, cs_⟩,
           [.error ("break:" ++ label.getD "")],
           Flat.Steps.tail (Flat.Step.mk (by unfold Flat.step?; rfl)) (Flat.Steps.refl _),
           rfl, rfl, rfl, rfl, rfl, rfl, by simp [observableTrace]⟩
  -- All compound cases below are FALSE as stated — see break_analysis.md
  -- seq_left: break fires in `a` of `.seq a b`, but dead code `b` evaluates to arbitrary value
  | seq_left _ => sorry
  -- seq_right: need to evaluate `a` first, which may change env/heap
  | seq_right _ => sorry
  -- let_init: break fires in init, then let binds → env changes (env.extend)
  | let_init _ => sorry
  -- All remaining: break fires in eval position, surrounding context wraps result
  -- For many (getProp, unary, etc.), env/heap ARE preserved, but for nested
  -- assign/let cases inside the sub-expression, env changes break the invariant
  | _ => sorry
/-- Symmetric version for continue. Same structural issues as break. -/
private theorem hasContinueInHead_flat_error_steps
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasContinueInHead e label)
    (sf : Flat.State) (hsf : sf.expr = e)
    (hewf : ExprWellFormed e sf.env) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      sf'.expr = .lit .undefined ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.funcs = sf.funcs ∧ sf'.callStack = sf.callStack ∧
      sf'.trace = sf.trace ++ evs ∧
      observableTrace evs = observableTrace [.error ("continue:" ++ label.getD "")] := by
  cases h with
  | continue_direct =>
    obtain ⟨e_, env_, heap_, trace_, funcs_, cs_⟩ := sf
    subst hsf
    exact ⟨⟨.lit .undefined, env_, heap_, trace_ ++ [.error ("continue:" ++ label.getD "")], funcs_, cs_⟩,
           [.error ("continue:" ++ label.getD "")],
           Flat.Steps.tail (Flat.Step.mk (by unfold Flat.step?; rfl)) (Flat.Steps.refl _),
           rfl, rfl, rfl, rfl, rfl, rfl, by simp [observableTrace]⟩
  | seq_left _ => sorry
  | seq_right _ => sorry
  | let_init _ => sorry
  | _ => sorry

/-- step? on .throw (.lit v) produces an immediate error. -/
private theorem Flat.step?_throw_lit_eq (v : Flat.Value)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env) :
    Flat.step? ⟨.throw (.lit v), env, heap, trace, funcs, cs⟩ =
    some (.error (Flat.valueToString v),
      ⟨.lit .undefined, env, heap, trace ++ [.error (Flat.valueToString v)], funcs, cs⟩) := by
  unfold Flat.step?; rfl

/-- step? on .throw (.var name) when lookup succeeds: resolves var, keeps throw. -/
private theorem Flat.step?_throw_var_ok (name : Flat.VarName) (v : Flat.Value)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (h : Flat.Env.lookup env name = some v) :
    Flat.step? ⟨.throw (.var name), env, heap, trace, funcs, cs⟩ =
    some (.silent, ⟨.throw (.lit v), env, heap, trace ++ [.silent], funcs, cs⟩) := by
  simp only [Flat.step?, Flat.exprValue?, h]; rfl

/-- step? on .throw .this when lookup "this" succeeds: resolves this, keeps throw. -/
private theorem Flat.step?_throw_this_ok (v : Flat.Value)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (h : Flat.Env.lookup env "this" = some v) :
    Flat.step? ⟨.throw .this, env, heap, trace, funcs, cs⟩ =
    some (.silent, ⟨.throw (.lit v), env, heap, trace ++ [.silent], funcs, cs⟩) := by
  simp only [Flat.step?, Flat.exprValue?, h]; rfl

/-- If normalizeExpr sf.expr k produces .throw arg (with trivial-preserving k),
    then there exist Flat steps from sf that produce the same error event
    as the ANF throw step. Covers both evalTrivial ok and error cases. -/
private theorem normalizeExpr_throw_step_sim
    (sf : Flat.State)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.throw arg, m))
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (hewf : ExprWellFormed sf.expr sf.env) :
    -- ok case: evalTrivial succeeds
    (∀ v, ANF.evalTrivial sf.env arg = .ok v →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.error (Flat.valueToString v)]) ∧
    -- error case: evalTrivial fails
    (∀ msg, ANF.evalTrivial sf.env arg = .error msg →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.error msg]) := by
  have hthrow := ANF.normalizeExpr_throw_implies_hasThrowInHead sf.expr k hk arg n m hnorm
  cases sf with
  | mk e env heap trace funcs cs =>
  simp only [Flat.State.expr] at hnorm hewf hthrow
  cases hthrow with
  | throw_direct =>
    rename_i flat_arg
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    -- hnorm : normalizeExpr (.throw flat_arg) k = .ok (.throw arg, m)
    -- normalizeExpr (.throw flat_arg) k ignores k and uses normalizeExpr flat_arg (fun t => pure (.throw t))
    have hnorm' : (ANF.normalizeExpr flat_arg (fun t => pure (ANF.Expr.throw t))).run n =
        .ok (.throw arg, m) := by
      simp only [ANF.normalizeExpr] at hnorm; exact hnorm
    -- Case split on flat_arg for base cases
    cases flat_arg with
    | lit v =>
      -- normalizeExpr (.lit v) k' produces k' (trivialOfFlatValue v)
      simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm'
      -- Extract arg per value constructor; evalTrivial always gives .ok for literals
      cases v <;> (
        simp only [pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
        obtain ⟨rfl, rfl⟩ := hnorm'
        refine ⟨?_, ?_⟩
        · intro val heval
          simp only [ANF.evalTrivial, ANF.trivialValue?, Except.ok.injEq] at heval
          subst heval
          exact ⟨_, _, .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _), rfl, rfl, rfl, rfl, rfl⟩
        · intro msg heval
          simp only [ANF.evalTrivial, ANF.trivialValue?] at heval
          exact absurd heval (by simp))
    | var name =>
      -- normalizeExpr (.var name) k' = k' (.var name)
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      -- By ExprWellFormed, env.lookup name must succeed
      have hwf_var : env.lookup name ≠ none := by
        apply hewf; exact VarFreeIn.throw_arg _ _ (VarFreeIn.var name)
      obtain ⟨v, hv_flat⟩ := Option.ne_none_iff_exists'.mp hwf_var
      -- Get the ANF version of the lookup
      have hv_anf : ANF.Env.lookup env name = some v := by
        simp only [ANF.Env.lookup, Flat.Env.lookup] at hv_flat ⊢; exact hv_flat
      refine ⟨?_, ?_⟩
      · -- ok case: evalTrivial env (.var name) = .ok v
        intro val heval
        simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
        subst heval
        -- Two flat steps: .throw (.var name) → .throw (.lit v) → .lit .undefined
        -- Need Flat.Env.lookup for step? helpers
        have hv_flat_env : Flat.Env.lookup env name = some v := by
          simp only [Flat.Env.lookup, ANF.Env.lookup] at hv_flat ⊢; exact hv_flat
        -- Step 1: resolve var inside throw
        have hstep1 := Flat.step?_throw_var_ok name v env heap trace funcs cs hv_flat_env
        -- Step 2: throw with literal value → error
        have hstep2 := Flat.step?_throw_lit_eq v env heap (trace ++ [.silent]) funcs cs
        refine ⟨[.silent, .error (Flat.valueToString v)], _,
          .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
          rfl, rfl, rfl, ?_, ?_⟩
        · -- trace: (trace ++ [.silent]) ++ [.error msg] = trace ++ [.silent, .error msg]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        · -- observableTrace [.silent, .error msg] = observableTrace [.error msg]
          simp only [observableTrace, List.filter]
          rfl
      · -- error case: vacuous since env.lookup name = some v
        intro msg heval
        simp only [ANF.evalTrivial, hv_anf] at heval
        exact absurd heval (by simp)
    | this =>
      -- normalizeExpr .this k' = k' (.var "this") = pure (.throw (.var "this"))
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      have hwf_this : env.lookup "this" ≠ none := by
        apply hewf; exact VarFreeIn.throw_arg _ _ VarFreeIn.this_var
      obtain ⟨v, hv_flat⟩ := Option.ne_none_iff_exists'.mp hwf_this
      have hv_anf : ANF.Env.lookup env "this" = some v := by
        simp only [ANF.Env.lookup, Flat.Env.lookup] at hv_flat ⊢; exact hv_flat
      refine ⟨?_, ?_⟩
      · -- ok case: evalTrivial env (.var "this") = .ok v
        intro val heval
        simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
        subst heval
        have hv_flat_env : Flat.Env.lookup env "this" = some v := by
          simp only [Flat.Env.lookup, ANF.Env.lookup] at hv_flat ⊢; exact hv_flat
        -- Step 1: .throw .this → .throw (.lit v) via resolving "this"
        have hstep1 := Flat.step?_throw_this_ok v env heap trace funcs cs hv_flat_env
        -- Step 2: throw with literal value → error
        have hstep2 := Flat.step?_throw_lit_eq v env heap (trace ++ [.silent]) funcs cs
        refine ⟨[.silent, .error (Flat.valueToString v)], _,
          .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
          rfl, rfl, rfl, ?_, ?_⟩
        · simp only [List.append_assoc, List.cons_append, List.nil_append]
        · simp only [observableTrace, List.filter]; rfl
      · -- error case: vacuous since env.lookup "this" = some v
        intro msg heval
        simp only [ANF.evalTrivial, hv_anf] at heval
        exact absurd heval (by simp)
    | «break» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | «continue» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | _ => sorry -- compound flat_arg: seq, let, assign, if, call, throw, etc.
  | _ =>
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    sorry

/-- If normalizeExpr sf.expr k produces .return arg (with trivial-preserving k),
    then there exist Flat steps from sf matching the ANF return step. -/
private theorem normalizeExpr_return_step_sim
    (sf : Flat.State)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : Option ANF.Trivial) (n m : Nat)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.return arg, m))
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (hewf : ExprWellFormed sf.expr sf.env) :
    -- none case: return without argument
    (arg = none →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.error "return:undefined"]) ∧
    -- some ok case: return with arg that evaluates successfully
    (∀ t v, arg = some t → ANF.evalTrivial sf.env t = .ok v →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit v ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.error ("return:" ++ Flat.valueToString v)]) ∧
    -- some error case: return with arg that fails
    (∀ t msg, arg = some t → ANF.evalTrivial sf.env t = .error msg →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.error msg]) := by
  have hret := ANF.normalizeExpr_return_implies_hasReturnInHead sf.expr k hk arg n m hnorm
  cases sf with
  | mk e env heap trace funcs cs =>
  simp only [Flat.State.expr] at hnorm hewf hret
  cases hret with
  | return_none_direct =>
    -- sf.expr = .return none, normalizeExpr produces pure (.return none), so arg = none
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
    obtain ⟨rfl, rfl⟩ := hnorm
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    refine ⟨?_, ?_, ?_⟩
    · -- none case
      intro _
      refine ⟨[.error "return:undefined"], _,
        .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _),
        rfl, rfl, rfl, rfl, rfl⟩
    · -- some ok case: vacuous (arg = none ≠ some t)
      intro t _ h; exact absurd h (by simp)
    · -- some error case: vacuous
      intro t _ h; exact absurd h (by simp)
  | return_some_direct =>
    rename_i inner_val
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    -- normalizeExpr (.return (some inner_val)) k = normalizeExpr inner_val (fun t => pure (.return (some t)))
    have hnorm' : (ANF.normalizeExpr inner_val (fun t => pure (ANF.Expr.return (some t)))).run n =
        .ok (.return arg, m) := by
      simp only [ANF.normalizeExpr] at hnorm; exact hnorm
    cases inner_val with
    | lit v =>
      simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm'
      cases v <;> (
        simp only [pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
        obtain ⟨rfl, rfl⟩ := hnorm'
        refine ⟨?_, ?_, ?_⟩
        · intro h; exact absurd h (by simp)
        · intro t val harg heval
          simp only [Option.some.injEq] at harg; subst harg
          simp only [ANF.evalTrivial, ANF.trivialValue?, Except.ok.injEq] at heval
          subst heval
          exact ⟨_, _, .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _), rfl, rfl, rfl, rfl, rfl⟩
        · intro t msg harg heval
          simp only [Option.some.injEq] at harg; subst harg
          simp only [ANF.evalTrivial, ANF.trivialValue?] at heval
          exact absurd heval (by simp))
    | var name =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      -- By ExprWellFormed, env.lookup name must succeed
      have hwf_var : env.lookup name ≠ none := by
        apply hewf; exact VarFreeIn.return_some_arg _ _ (VarFreeIn.var name)
      obtain ⟨v, hv_flat⟩ := Option.ne_none_iff_exists'.mp hwf_var
      have hv_anf : ANF.Env.lookup env name = some v := by
        simp only [ANF.Env.lookup, Flat.Env.lookup] at hv_flat ⊢; exact hv_flat
      have hv_flat_env : Flat.Env.lookup env name = some v := by
        simp only [Flat.Env.lookup, ANF.Env.lookup] at hv_flat ⊢; exact hv_flat
      refine ⟨?_, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · intro t val harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
        subst heval
        -- Step 1: .return (some (.var name)) → .return (some (.lit v))
        have hstep1 : Flat.step? ⟨.return (some (.var name)), env, heap, trace, funcs, cs⟩ =
            some (.silent, ⟨.return (some (.lit v)), env, heap, trace ++ [.silent], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?, hv_flat_env, Flat.step?]
        -- Step 2: .return (some (.lit v)) → .lit v with error
        have hstep2 : Flat.step? ⟨.return (some (.lit v)), env, heap, trace ++ [.silent], funcs, cs⟩ =
            some (.error ("return:" ++ Flat.valueToString v),
              ⟨.lit v, env, heap, (trace ++ [.silent]) ++ [.error ("return:" ++ Flat.valueToString v)], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?]
        refine ⟨[.silent, .error ("return:" ++ Flat.valueToString v)], _,
          .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
          rfl, rfl, rfl, ?_, ?_⟩
        · simp only [List.append_assoc, List.cons_append, List.nil_append]
        · simp only [observableTrace, List.filter]; rfl
      · intro t msg harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf] at heval
        exact absurd heval (by simp)
    | this =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      have hwf_this : env.lookup "this" ≠ none := by
        apply hewf; exact VarFreeIn.return_some_arg _ _ VarFreeIn.this_var
      obtain ⟨v, hv_flat⟩ := Option.ne_none_iff_exists'.mp hwf_this
      have hv_anf : ANF.Env.lookup env "this" = some v := by
        simp only [ANF.Env.lookup, Flat.Env.lookup] at hv_flat ⊢; exact hv_flat
      have hv_flat_env : Flat.Env.lookup env "this" = some v := by
        simp only [Flat.Env.lookup, ANF.Env.lookup] at hv_flat ⊢; exact hv_flat
      refine ⟨?_, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · intro t val harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
        subst heval
        -- Step 1: .return (some .this) → .return (some (.lit v))
        have hstep1 : Flat.step? ⟨.return (some .this), env, heap, trace, funcs, cs⟩ =
            some (.silent, ⟨.return (some (.lit v)), env, heap, trace ++ [.silent], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?, hv_flat_env, Flat.step?]
        -- Step 2: .return (some (.lit v)) → .lit v with error
        have hstep2 : Flat.step? ⟨.return (some (.lit v)), env, heap, trace ++ [.silent], funcs, cs⟩ =
            some (.error ("return:" ++ Flat.valueToString v),
              ⟨.lit v, env, heap, (trace ++ [.silent]) ++ [.error ("return:" ++ Flat.valueToString v)], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?]
        refine ⟨[.silent, .error ("return:" ++ Flat.valueToString v)], _,
          .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
          rfl, rfl, rfl, ?_, ?_⟩
        · simp only [List.append_assoc, List.cons_append, List.nil_append]
        · simp only [observableTrace, List.filter]; rfl
      · intro t msg harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf] at heval
        exact absurd heval (by simp)
    | «break» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | «continue» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | _ => sorry -- compound inner_val: seq, let, assign, if, call, throw, etc.
  | _ =>
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    sorry -- compound HasReturnInHead cases: seq_left, seq_right, let_init, etc.

/-- step? on .await (.lit v) resolves immediately to .lit v with silent event. -/
private theorem Flat.step?_await_lit_eq (v : Flat.Value)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env) :
    Flat.step? ⟨.await (.lit v), env, heap, trace, funcs, cs⟩ =
    some (.silent,
      ⟨.lit v, env, heap, trace ++ [.silent], funcs, cs⟩) := by
  unfold Flat.step?; rfl

/-- step? on .await (.var name) when lookup succeeds: resolves var, keeps await. -/
private theorem Flat.step?_await_var_ok (name : Flat.VarName) (v : Flat.Value)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (h : Flat.Env.lookup env name = some v) :
    Flat.step? ⟨.await (.var name), env, heap, trace, funcs, cs⟩ =
    some (.silent, ⟨.await (.lit v), env, heap, trace ++ [.silent], funcs, cs⟩) := by
  simp only [Flat.step?, Flat.exprValue?, h]; rfl

/-- step? on .await .this when lookup "this" succeeds: resolves this, keeps await. -/
private theorem Flat.step?_await_this_ok (v : Flat.Value)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (h : Flat.Env.lookup env "this" = some v) :
    Flat.step? ⟨.await .this, env, heap, trace, funcs, cs⟩ =
    some (.silent, ⟨.await (.lit v), env, heap, trace ++ [.silent], funcs, cs⟩) := by
  simp only [Flat.step?, Flat.exprValue?, h]; rfl

/-- If normalizeExpr sf.expr k produces .await arg (with trivial-preserving k),
    then there exist Flat steps from sf matching the ANF await step. -/
private theorem normalizeExpr_await_step_sim
    (sf : Flat.State)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : ANF.Trivial) (n m : Nat)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.await arg, m))
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (hewf : ExprWellFormed sf.expr sf.env) :
    -- ok case
    (∀ v, ANF.evalTrivial sf.env arg = .ok v →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit v ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.silent]) ∧
    -- error case
    (∀ msg, ANF.evalTrivial sf.env arg = .error msg →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.error msg]) := by
  have hawait := ANF.normalizeExpr_await_implies_hasAwaitInHead sf.expr k hk arg n m hnorm
  cases sf with
  | mk e env heap trace funcs cs =>
  simp only [Flat.State.expr] at hnorm hewf hawait
  cases hawait with
  | await_direct =>
    rename_i inner_arg
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    -- hnorm : normalizeExpr (.await inner_arg) k = .ok (.await arg, m)
    -- simplify to: normalizeExpr inner_arg (fun t => pure (.await t)) = .ok (.await arg, m)
    have hnorm' : (ANF.normalizeExpr inner_arg (fun t => pure (ANF.Expr.await t))).run n =
        .ok (.await arg, m) := by
      simp only [ANF.normalizeExpr] at hnorm; exact hnorm
    -- Case split on inner_arg for base cases
    cases inner_arg with
    | lit v =>
      -- normalizeExpr (.lit v) k' produces k' (trivialOfFlatValue v)
      simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm'
      -- Extract arg per value constructor; evalTrivial always gives .ok for literals
      cases v <;> (
        simp only [pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
        obtain ⟨rfl, rfl⟩ := hnorm'
        refine ⟨?_, ?_⟩
        · intro val heval
          simp only [ANF.evalTrivial, ANF.trivialValue?, Except.ok.injEq] at heval
          subst heval
          exact ⟨_, _, .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _), rfl, rfl, rfl, rfl, rfl⟩
        · intro msg heval
          simp only [ANF.evalTrivial, ANF.trivialValue?] at heval
          exact absurd heval (by simp))
    | var name =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      -- Case split on env lookup (may succeed or fail)
      cases hlookup : Flat.Env.lookup env name with
      | some v =>
        have hv_anf : ANF.Env.lookup env name = some v := by
          simp only [ANF.Env.lookup, Flat.Env.lookup] at hlookup ⊢; exact hlookup
        refine ⟨?_, ?_⟩
        · -- ok case: evalTrivial env (.var name) = .ok v
          intro val heval
          simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
          subst heval
          have hstep1 := Flat.step?_await_var_ok name v env heap trace funcs cs hlookup
          have hstep2 := Flat.step?_await_lit_eq v env heap (trace ++ [.silent]) funcs cs
          refine ⟨[.silent, .silent], _,
            .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
            rfl, rfl, rfl, ?_, ?_⟩
          · simp only [List.append_assoc, List.cons_append, List.nil_append]
          · simp only [observableTrace, List.filter]; rfl
        · -- error case: vacuous since env.lookup name = some v
          intro msg heval
          simp only [ANF.evalTrivial, hv_anf] at heval
          exact absurd heval (by simp)
      | none =>
        have hv_anf : ANF.Env.lookup env name = none := by
          simp only [ANF.Env.lookup, Flat.Env.lookup] at hlookup ⊢; exact hlookup
        refine ⟨?_, ?_⟩
        · -- ok case: vacuous since env.lookup = none
          intro val heval
          simp [ANF.evalTrivial, hv_anf] at heval
        · -- error case: evalTrivial gives ReferenceError
          intro msg heval
          simp [ANF.evalTrivial, hv_anf] at heval
          subst heval
          -- Flat steps: .await (.var name) with lookup failure
          -- Step 1: .var name produces ReferenceError → .await wraps it
          have hstep_var : Flat.step? ⟨.var name, env, heap, trace, funcs, cs⟩ =
              some (.error ("ReferenceError: " ++ name),
                ⟨.lit .undefined, env, heap, trace ++ [.error ("ReferenceError: " ++ name)], funcs, cs⟩) := by
            unfold Flat.step?; simp [hlookup]
          have hstep1 := step?_await_error ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.var name)
            (by simp [Flat.exprValue?]) ("ReferenceError: " ++ name) _ hstep_var
          obtain ⟨s1, hs1_eq, hs1_expr, hs1_env, hs1_heap, _, _, hs1_trace⟩ := hstep1
          -- Step 2: .await (.lit .undefined) → .lit .undefined with silent
          have hstep2 : Flat.step? s1 =
              some (.silent, ⟨.lit .undefined, env, heap,
                (trace ++ [.error ("ReferenceError: " ++ name)]) ++ [.silent], funcs, cs⟩) := by
            have : s1 = ⟨.await (.lit .undefined), env, heap,
                trace ++ [.error ("ReferenceError: " ++ name)], funcs, cs⟩ := by
              cases s1; simp_all
            rw [this]; unfold Flat.step?; rfl
          refine ⟨[.error ("ReferenceError: " ++ name), .silent], _,
            .tail ⟨hs1_eq⟩ (.tail ⟨hstep2⟩ (.refl _)),
            rfl, rfl, rfl, ?_, ?_⟩
          · simp only [List.append_assoc, List.cons_append, List.nil_append]
          · simp only [observableTrace, List.filter]; rfl
    | this =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      cases hlookup : Flat.Env.lookup env "this" with
      | some v =>
        have hv_anf : ANF.Env.lookup env "this" = some v := by
          simp only [ANF.Env.lookup, Flat.Env.lookup] at hlookup ⊢; exact hlookup
        refine ⟨?_, ?_⟩
        · intro val heval
          simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
          subst heval
          have hstep1 := Flat.step?_await_this_ok v env heap trace funcs cs hlookup
          have hstep2 := Flat.step?_await_lit_eq v env heap (trace ++ [.silent]) funcs cs
          refine ⟨[.silent, .silent], _,
            .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
            rfl, rfl, rfl, ?_, ?_⟩
          · simp only [List.append_assoc, List.cons_append, List.nil_append]
          · simp only [observableTrace, List.filter]; rfl
        · intro msg heval
          simp only [ANF.evalTrivial, hv_anf] at heval
          exact absurd heval (by simp)
      | none =>
        -- Semantic mismatch: Flat .this with none lookup silently resolves to .undefined,
        -- but ANF .var "this" produces ReferenceError. The error case needs ExprWellFormed
        -- with VarFreeIn.await_arg.
        exfalso; exact absurd hlookup (hewf "this" (VarFreeIn.await_arg _ _ VarFreeIn.this_var))
    | «break» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | «continue» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | _ => sorry -- compound inner_arg: seq, let, assign, if, call, throw, etc.
  | _ =>
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    sorry

/-- If normalizeExpr sf.expr k produces .yield arg delegate (with trivial-preserving k),
    then there exist Flat steps from sf matching the ANF yield step. -/
private theorem normalizeExpr_yield_step_sim
    (sf : Flat.State)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (arg : Option ANF.Trivial) (delegate : Bool) (n m : Nat)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.yield arg delegate, m))
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (hewf : ExprWellFormed sf.expr sf.env) :
    -- none case
    (arg = none →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.silent]) ∧
    -- some ok case
    (∀ t v, arg = some t → ANF.evalTrivial sf.env t = .ok v →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit v ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.silent]) ∧
    -- some error case
    (∀ t msg, arg = some t → ANF.evalTrivial sf.env t = .error msg →
      ∃ (evs : List Core.TraceEvent) (sf' : Flat.State),
        Flat.Steps sf evs sf' ∧
        sf'.expr = .lit .undefined ∧ sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
        sf'.trace = sf.trace ++ evs ∧
        observableTrace evs = observableTrace [.error msg]) := by
  have hyield := ANF.normalizeExpr_yield_implies_hasYieldInHead sf.expr k hk arg delegate n m hnorm
  cases sf with
  | mk e env heap trace funcs cs =>
  simp only [Flat.State.expr] at hnorm hewf hyield
  cases hyield with
  | yield_none_direct =>
    rename_i d_val
    -- e = .yield none d_val, normalizeExpr produces pure (.yield none d_val)
    simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm
    obtain ⟨rfl, rfl⟩ := hnorm
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    refine ⟨?_, ?_, ?_⟩
    · -- none case: yield without argument → lit undefined (silent)
      intro _
      refine ⟨[.silent], _,
        .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _),
        rfl, rfl, rfl, rfl, rfl⟩
    · -- some ok case: vacuous (arg = none ≠ some t)
      intro t _ h; exact absurd h (by simp)
    · -- some error case: vacuous
      intro t _ h; exact absurd h (by simp)
  | yield_some_direct =>
    rename_i inner_val src_delegate
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    -- normalizeExpr (.yield (some inner_val) src_delegate) k ignores k
    have hnorm' : (ANF.normalizeExpr inner_val (fun t => pure (ANF.Expr.yield (some t) src_delegate))).run n =
        .ok (.yield arg delegate, m) := by
      simp only [ANF.normalizeExpr] at hnorm; exact hnorm
    cases inner_val with
    | lit v =>
      simp only [ANF.normalizeExpr, ANF.trivialOfFlatValue] at hnorm'
      cases v <;> (
        simp only [pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
        obtain ⟨rfl, rfl⟩ := hnorm'
        refine ⟨?_, ?_, ?_⟩
        · intro h; exact absurd h (by simp)
        · intro t val harg heval
          simp only [Option.some.injEq] at harg; subst harg
          simp only [ANF.evalTrivial, ANF.trivialValue?, Except.ok.injEq] at heval
          subst heval
          exact ⟨_, _, .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _), rfl, rfl, rfl, rfl, rfl⟩
        · intro t msg harg heval
          simp only [Option.some.injEq] at harg; subst harg
          simp only [ANF.evalTrivial, ANF.trivialValue?] at heval
          exact absurd heval (by simp))
    | var name =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      -- By ExprWellFormed, env.lookup name must succeed
      have hwf_var : env.lookup name ≠ none := by
        apply hewf; exact VarFreeIn.yield_some_arg _ _ _ (VarFreeIn.var name)
      obtain ⟨v, hv_flat⟩ := Option.ne_none_iff_exists'.mp hwf_var
      have hv_anf : ANF.Env.lookup env name = some v := by
        simp only [ANF.Env.lookup, Flat.Env.lookup] at hv_flat ⊢; exact hv_flat
      have hv_flat_env : Flat.Env.lookup env name = some v := by
        simp only [Flat.Env.lookup, ANF.Env.lookup] at hv_flat ⊢; exact hv_flat
      refine ⟨?_, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · intro t val harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
        subst heval
        -- Step 1: .yield (some (.var name)) d → .yield (some (.lit v)) d
        have hstep1 : Flat.step? ⟨.yield (some (.var name)) delegate, env, heap, trace, funcs, cs⟩ =
            some (.silent, ⟨.yield (some (.lit v)) delegate, env, heap, trace ++ [.silent], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?, hv_flat_env, Flat.step?]
        -- Step 2: .yield (some (.lit v)) d → .lit v (silent)
        have hstep2 : Flat.step? ⟨.yield (some (.lit v)) delegate, env, heap, trace ++ [.silent], funcs, cs⟩ =
            some (.silent,
              ⟨.lit v, env, heap, (trace ++ [.silent]) ++ [.silent], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?]
        refine ⟨[.silent, .silent], _,
          .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
          rfl, rfl, rfl, ?_, ?_⟩
        · simp only [List.append_assoc, List.cons_append, List.nil_append]
        · simp only [observableTrace, List.filter]; rfl
      · intro t msg harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf] at heval
        exact absurd heval (by simp)
    | this =>
      simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at hnorm'
      obtain ⟨rfl, rfl⟩ := hnorm'
      have hwf_this : env.lookup "this" ≠ none := by
        apply hewf; exact VarFreeIn.yield_some_arg _ _ _ VarFreeIn.this_var
      obtain ⟨v, hv_flat⟩ := Option.ne_none_iff_exists'.mp hwf_this
      have hv_anf : ANF.Env.lookup env "this" = some v := by
        simp only [ANF.Env.lookup, Flat.Env.lookup] at hv_flat ⊢; exact hv_flat
      have hv_flat_env : Flat.Env.lookup env "this" = some v := by
        simp only [Flat.Env.lookup, ANF.Env.lookup] at hv_flat ⊢; exact hv_flat
      refine ⟨?_, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · intro t val harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf, Except.ok.injEq] at heval
        subst heval
        -- Step 1: .yield (some .this) d → .yield (some (.lit v)) d
        have hstep1 : Flat.step? ⟨.yield (some .this) delegate, env, heap, trace, funcs, cs⟩ =
            some (.silent, ⟨.yield (some (.lit v)) delegate, env, heap, trace ++ [.silent], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?, hv_flat_env, Flat.step?]
        -- Step 2: .yield (some (.lit v)) d → .lit v (silent)
        have hstep2 : Flat.step? ⟨.yield (some (.lit v)) delegate, env, heap, trace ++ [.silent], funcs, cs⟩ =
            some (.silent,
              ⟨.lit v, env, heap, (trace ++ [.silent]) ++ [.silent], funcs, cs⟩) := by
          unfold Flat.step?; simp [Flat.exprValue?]
        refine ⟨[.silent, .silent], _,
          .tail ⟨hstep1⟩ (.tail ⟨hstep2⟩ (.refl _)),
          rfl, rfl, rfl, ?_, ?_⟩
        · simp only [List.append_assoc, List.cons_append, List.nil_append]
        · simp only [observableTrace, List.filter]; rfl
      · intro t msg harg heval
        simp only [Option.some.injEq] at harg; subst harg
        simp only [ANF.evalTrivial, hv_anf] at heval
        exact absurd heval (by simp)
    | «break» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | «continue» _ =>
      exfalso; simp only [ANF.normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure] at hnorm'
      exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm')).1
    | _ => sorry -- compound inner_val: seq, let, assign, if, call, throw, etc.
  | _ =>
    simp only [Flat.State.env, Flat.State.heap, Flat.State.trace]
    sorry -- compound HasYieldInHead cases: seq_left, seq_right, let_init, etc.

/-- If normalizeExpr sf.expr k produces .let name rhs body (with trivial-preserving k),
    then one ANF step on the let can be simulated by Flat steps. -/
private theorem normalizeExpr_let_step_sim
    (sf : Flat.State) (s : Flat.Program) (t : ANF.Program)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (name : ANF.VarName) (rhs : ANF.ComplexExpr) (body : ANF.Expr)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.let name rhs body, m))
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (hewf : ExprWellFormed sf.expr sf.env)
    (sa_env : ANF.Env) (sa_heap : Core.Heap) (sa_trace : List Core.TraceEvent)
    (hheap : sa_heap = sf.heap) (henv : sa_env = sf.env)
    (htrace : observableTrace sa_trace = observableTrace sf.trace)
    (ev : Core.TraceEvent) (sa' : ANF.State)
    (hstep_eq : ANF.step? ⟨.let name rhs body, sa_env, sa_heap, sa_trace⟩ = some (ev, sa')) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      observableTrace [ev] = observableTrace evs ∧
      ANF_SimRel s t sa' sf' ∧
      ExprWellFormed sf'.expr sf'.env := by
  subst hheap henv
  -- ANF.step? on .let always succeeds: evaluates rhs via evalComplex, extends env
  simp only [ANF.step?, ANF.pushTrace] at hstep_eq
  obtain ⟨rfl, rfl⟩ := hstep_eq
  -- Now sa'.expr = body, sa'.env = (evalComplex rhs).env.extend name (evalComplex rhs).value
  -- Need: sf.expr has .let or bindComplex form at eval head, flat steps matching
  sorry -- Need characterization of what produces .let, flat simulation

/-- If normalizeExpr sf.expr k produces .seq a b (with trivial-preserving k),
    then one ANF step on the seq can be simulated by Flat steps. -/
private theorem normalizeExpr_seq_step_sim
    (sf : Flat.State) (s : Flat.Program) (t : ANF.Program)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (a b : ANF.Expr)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.seq a b, m))
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (hewf : ExprWellFormed sf.expr sf.env)
    (sa_env : ANF.Env) (sa_heap : Core.Heap) (sa_trace : List Core.TraceEvent)
    (hheap : sa_heap = sf.heap) (henv : sa_env = sf.env)
    (htrace : observableTrace sa_trace = observableTrace sf.trace)
    (ev : Core.TraceEvent) (sa' : ANF.State)
    (hstep_eq : ANF.step? ⟨.seq a b, sa_env, sa_heap, sa_trace⟩ = some (ev, sa')) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      observableTrace [ev] = observableTrace evs ∧
      ANF_SimRel s t sa' sf' ∧
      ExprWellFormed sf'.expr sf'.env := by
  subst hheap henv
  unfold ANF.step? at hstep_eq
  simp only [ANF.pushTrace] at hstep_eq
  split at hstep_eq
  · -- exprValue? a = some val: impossible since a = .while_ c d
    rename_i val hval
    obtain ⟨c, d, rfl⟩ := normalizeExpr_seq_while_first sf.expr k hk n m _ b hnorm
    simp [ANF.exprValue?] at hval
  · -- exprValue? a = none: a steps
    rename_i hnv
    split at hstep_eq
    · rename_i t_inner sa_inner hstep_inner
      obtain ⟨rfl, rfl⟩ := hstep_eq
      -- a = .while_ c d by characterization
      obtain ⟨c, d, rfl⟩ := normalizeExpr_seq_while_first sf.expr k hk n m _ b hnorm
      -- Now: sa'.expr = .seq sa_inner.expr b where sa_inner came from stepping .while_ c d.
      -- The inner while step produces (when exprValue? c = some v):
      --   sa_inner.expr = if toBool v then .seq d (.while_ c d) else .trivial .litUndefined
      -- Resulting in sa'.expr = .seq (.seq d (.while_ c d)) b  or  .seq (.trivial .litUndefined) b
      -- ISSUE: These forms have first component that is NOT .while_, so normalizeExpr with
      -- trivial-preserving k CANNOT produce them (by normalizeExpr_seq_while_first).
      -- This means ANF_SimRel cannot be established for the post-step state.
      -- FIX NEEDED: Either generalize ANF_SimRel to handle while-loop transient states,
      -- or restructure the proof to use multi-step simulation for while loops.
      -- When exprValue? c = none and step? c = some (t, sc): sa_inner.expr = .while_ sc.expr d,
      -- giving sa'.expr = .seq (.while_ sc.expr d) b — this IS handleable but requires
      -- simulation of the condition sub-expression stepping.
      sorry
    · exact absurd hstep_eq (by simp)

/-- If normalizeExpr sf.expr k produces .if cond then_ else_ (with trivial-preserving k),
    then one ANF step on the if can be simulated by Flat steps. -/
private theorem normalizeExpr_if_step_sim
    (sf : Flat.State) (s : Flat.Program) (t : ANF.Program)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (cond : ANF.Trivial) (then_ else_ : ANF.Expr)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.if cond then_ else_, m))
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (hewf : ExprWellFormed sf.expr sf.env)
    (sa_env : ANF.Env) (sa_heap : Core.Heap) (sa_trace : List Core.TraceEvent)
    (hheap : sa_heap = sf.heap) (henv : sa_env = sf.env)
    (htrace : observableTrace sa_trace = observableTrace sf.trace)
    (ev : Core.TraceEvent) (sa' : ANF.State)
    (hstep_eq : ANF.step? ⟨.if cond then_ else_, sa_env, sa_heap, sa_trace⟩ = some (ev, sa')) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      observableTrace [ev] = observableTrace evs ∧
      ANF_SimRel s t sa' sf' ∧
      ExprWellFormed sf'.expr sf'.env := by
  subst hheap henv
  unfold ANF.step? at hstep_eq
  simp only [ANF.pushTrace] at hstep_eq
  split at hstep_eq
  · -- evalTrivial env cond = .ok v
    rename_i v heval
    split at hstep_eq
    · -- toBoolean v = true: step to then_
      obtain ⟨rfl, rfl⟩ := hstep_eq
      sorry -- Need: sf.expr has .if at eval head, flat steps to then_flat, SimRel for then_
    · -- toBoolean v = false: step to else_
      obtain ⟨rfl, rfl⟩ := hstep_eq
      sorry -- Need: sf.expr has .if at eval head, flat steps to else_flat, SimRel for else_
  · -- evalTrivial env cond = .error msg
    rename_i msg herr
    obtain ⟨rfl, rfl⟩ := hstep_eq
    -- Error case: evalTrivial sf.env cond = .error msg
    -- For well-formed expressions, evalTrivial on a trivial from normalization cannot error
    -- because all variable names come from the original expression (bound by hewf)
    -- and all literal trivials evaluate successfully.
    exfalso
    cases cond with
    | var name_cond =>
      simp only [ANF.evalTrivial] at herr
      split at herr
      · simp at herr
      · rename_i hnone
        -- name_cond is not bound: show it's free in sf.expr to contradict hewf
        have hfree := normalizeExpr_if_cond_var_free sf.expr.depth sf.expr (Nat.le_refl _)
          k n m name_cond then_ else_ hk hnorm
        exact (hewf name_cond hfree) hnone
    | litNull | litUndefined | litBool _ | litNum _ | litStr _ | litObject _ | litClosure _ _ =>
      simp only [ANF.evalTrivial, ANF.trivialValue?] at herr; exact nomatch herr

/-- If normalizeExpr sf.expr k produces .tryCatch body catchParam catchBody finally_
    (with trivial-preserving k), then one ANF step can be simulated by Flat steps. -/
private theorem normalizeExpr_tryCatch_step_sim
    (sf : Flat.State) (s : Flat.Program) (t : ANF.Program)
    (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
    (body : ANF.Expr) (catchParam : ANF.VarName) (catchBody : ANF.Expr) (finally_ : Option ANF.Expr)
    (hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (.tryCatch body catchParam catchBody finally_, m))
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (hewf : ExprWellFormed sf.expr sf.env)
    (sa_env : ANF.Env) (sa_heap : Core.Heap) (sa_trace : List Core.TraceEvent)
    (hheap : sa_heap = sf.heap) (henv : sa_env = sf.env)
    (htrace : observableTrace sa_trace = observableTrace sf.trace)
    (ev : Core.TraceEvent) (sa' : ANF.State)
    (hstep_eq : ANF.step? ⟨.tryCatch body catchParam catchBody finally_, sa_env, sa_heap, sa_trace⟩ = some (ev, sa')) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      observableTrace [ev] = observableTrace evs ∧
      ANF_SimRel s t sa' sf' ∧
      ExprWellFormed sf'.expr sf'.env := by
  subst hheap henv
  -- tryCatch step involves body evaluation, error catching, and finally handling
  -- Structural decomposition deferred: needs characterization of what produces .tryCatch
  sorry

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
        exfalso
        have hnorm_simp : (ANF.normalizeExpr sf.expr k).run n = .ok (.trivial (.var name), m) := by
          simp only [ANF.State.expr] at hnorm; exact hnorm
        have hfree := normalizeExpr_var_implies_free sf.expr.depth sf.expr (Nat.le_refl _)
          k n m name hk_triv hnorm_simp
        have hbound := hewf name hfree
        simp only [ANF.State.env] at henv
        rw [← henv] at hbound
        exact hbound hlookup
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
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.State.expr] at hnorm
    simp only [ANF.State.heap] at hheap
    simp only [ANF.State.env] at henv
    simp only [ANF.State.trace] at htrace
    exact normalizeExpr_let_step_sim sf s t k n m name rhs body hnorm hk_triv hewf
      sa_env sa_heap sa_trace hheap henv htrace _ _ hstep_eq
  | seq a b =>
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.State.expr] at hnorm
    simp only [ANF.State.heap] at hheap
    simp only [ANF.State.env] at henv
    simp only [ANF.State.trace] at htrace
    exact normalizeExpr_seq_step_sim sf s t k n m a b hnorm hk_triv hewf
      sa_env sa_heap sa_trace hheap henv htrace _ _ hstep_eq
  | «if» cond then_ else_ =>
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.State.expr] at hnorm
    simp only [ANF.State.heap] at hheap
    simp only [ANF.State.env] at henv
    simp only [ANF.State.trace] at htrace
    exact normalizeExpr_if_step_sim sf s t k n m cond then_ else_ hnorm hk_triv hewf
      sa_env sa_heap sa_trace hheap henv htrace _ _ hstep_eq
  | while_ cond body =>
    exfalso
    rw [hsa] at hnorm
    exact normalizeExpr_not_while sf.expr k
      (fun x n' m' c' b' h => by
        obtain ⟨m'', hm''⟩ := hk_triv x n'
        rw [hm''] at h; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1)
      n m cond body hnorm
  | throw arg =>
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    cases heval : ANF.evalTrivial sa_env arg <;> simp [heval] at hstep_eq
    all_goals obtain ⟨rfl, rfl⟩ := hstep_eq
    -- Shared setup for both throw subcases
    all_goals simp only [ANF.State.expr] at hnorm
    all_goals simp only [ANF.State.heap] at hheap
    all_goals simp only [ANF.State.env] at henv
    all_goals simp only [ANF.State.trace] at htrace
    all_goals obtain ⟨hthrow_ok, hthrow_err⟩ :=
      normalizeExpr_throw_step_sim sf k arg n m hnorm hk_triv hewf
    · -- error case: evalTrivial produced error msg
      rename_i msg
      have heval_sf : ANF.evalTrivial sf.env arg = .error msg := by rw [← henv]; exact heval
      obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hthrow_err msg heval_sf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    · -- ok case: evalTrivial produced value
      rename_i v
      have heval_sf : ANF.evalTrivial sf.env arg = .ok v := by rw [← henv]; exact heval
      obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hthrow_ok v heval_sf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
  | tryCatch body catchParam catchBody finally_ =>
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.State.expr] at hnorm
    simp only [ANF.State.heap] at hheap
    simp only [ANF.State.env] at henv
    simp only [ANF.State.trace] at htrace
    exact normalizeExpr_tryCatch_step_sim sf s t k n m body catchParam catchBody finally_ hnorm hk_triv hewf
      sa_env sa_heap sa_trace hheap henv htrace _ _ hstep_eq
  | «return» arg =>
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.State.expr] at hnorm
    simp only [ANF.State.heap] at hheap
    simp only [ANF.State.env] at henv
    simp only [ANF.State.trace] at htrace
    obtain ⟨hret_none, hret_ok, hret_err⟩ :=
      normalizeExpr_return_step_sim sf k arg n m hnorm hk_triv hewf
    cases arg with
    | none =>
      simp only [ANF.step?, ANF.pushTrace] at hstep_eq
      obtain ⟨rfl, rfl⟩ := hstep_eq
      obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hret_none rfl
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | some t =>
      simp only [ANF.step?, ANF.pushTrace] at hstep_eq
      cases heval : ANF.evalTrivial sa_env t <;> simp [heval] at hstep_eq
      all_goals obtain ⟨rfl, rfl⟩ := hstep_eq
      · -- error case
        rename_i msg
        have heval_sf : ANF.evalTrivial sf.env t = .error msg := by rw [← henv]; exact heval
        obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hret_err t msg rfl heval_sf
        refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
        · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                  fun t' => pure (.trivial t'), n, n, ?_, ANF.trivial_k_preserving⟩
          · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
          · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
        · rw [hexpr']; intro x hfx; cases hfx
      · -- ok case
        rename_i v
        have heval_sf : ANF.evalTrivial sf.env t = .ok v := by rw [← henv]; exact heval
        obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hret_ok t v rfl heval_sf
        refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
        · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                  fun t' => pure (.trivial t'), n, n, ?_, ANF.trivial_k_preserving⟩
          · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
          · rw [hexpr']; simp [ANF.normalizeExpr, trivialOfFlatValue_eq_trivialOfValue, StateT.run, StateT.pure, pure, Pure.pure, Except.pure]
        · rw [hexpr']; intro x hfx; cases hfx
  | yield arg delegate =>
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.State.expr] at hnorm
    simp only [ANF.State.heap] at hheap
    simp only [ANF.State.env] at henv
    simp only [ANF.State.trace] at htrace
    obtain ⟨hyield_none, hyield_ok, hyield_err⟩ :=
      normalizeExpr_yield_step_sim sf k arg delegate n m hnorm hk_triv hewf
    cases arg with
    | none =>
      simp only [ANF.step?, ANF.pushTrace] at hstep_eq
      obtain ⟨rfl, rfl⟩ := hstep_eq
      obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hyield_none rfl
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | some t =>
      simp only [ANF.step?, ANF.pushTrace] at hstep_eq
      cases heval : ANF.evalTrivial sa_env t <;> simp [heval] at hstep_eq
      all_goals obtain ⟨rfl, rfl⟩ := hstep_eq
      · -- error case
        rename_i msg
        have heval_sf : ANF.evalTrivial sf.env t = .error msg := by rw [← henv]; exact heval
        obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hyield_err t msg rfl heval_sf
        refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
        · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                  fun t' => pure (.trivial t'), n, n, ?_, ANF.trivial_k_preserving⟩
          · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
          · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
        · rw [hexpr']; intro x hfx; cases hfx
      · -- ok case
        rename_i v
        have heval_sf : ANF.evalTrivial sf.env t = .ok v := by rw [← henv]; exact heval
        obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hyield_ok t v rfl heval_sf
        refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
        · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                  fun t' => pure (.trivial t'), n, n, ?_, ANF.trivial_k_preserving⟩
          · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
          · rw [hexpr']; simp [ANF.normalizeExpr, trivialOfFlatValue_eq_trivialOfValue, StateT.run, StateT.pure, pure, Pure.pure, Except.pure]
        · rw [hexpr']; intro x hfx; cases hfx
  | await arg =>
    cases sa with
    | mk sa_expr sa_env sa_heap sa_trace =>
    simp only [] at hsa; subst hsa
    simp only [ANF.State.expr] at hnorm
    simp only [ANF.State.heap] at hheap
    simp only [ANF.State.env] at henv
    simp only [ANF.State.trace] at htrace
    obtain ⟨hawait_ok, hawait_err⟩ :=
      normalizeExpr_await_step_sim sf k arg n m hnorm hk_triv hewf
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    cases heval : ANF.evalTrivial sa_env arg <;> simp [heval] at hstep_eq
    all_goals obtain ⟨rfl, rfl⟩ := hstep_eq
    · -- error case
      rename_i msg
      have heval_sf : ANF.evalTrivial sf.env arg = .error msg := by rw [← henv]; exact heval
      obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hawait_err msg heval_sf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    · -- ok case
      rename_i v
      have heval_sf : ANF.evalTrivial sf.env arg = .ok v := by rw [← henv]; exact heval
      obtain ⟨evs, sf', hsteps, hexpr', henv', hheap', htrace', hobs'⟩ := hawait_ok v heval_sf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_,
                fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · rw [observableTrace_append, htrace, htrace', observableTrace_append]; congr 1; exact hobs'.symm
        · rw [hexpr']; simp [ANF.normalizeExpr, trivialOfFlatValue_eq_trivialOfValue, StateT.run, StateT.pure, pure, Pure.pure, Except.pure]
      · rw [hexpr']; intro x hfx; cases hfx
  | labeled label body =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp [ANF.step?, ANF.pushTrace] at hstep_eq
    obtain ⟨rfl, rfl⟩ := hstep_eq
    obtain ⟨evs, sf', hsteps, ⟨k', n', m', hbody, hk'⟩, henv', hheap', htrace', hobs, hwf'⟩ :=
      normalizeExpr_labeled_step_sim sf.expr.depth sf.expr (Nat.le_refl _) k n m label body hk_triv hnorm sf rfl hewf
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
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    obtain ⟨rfl, rfl⟩ := hstep_eq
    have hnorm_simp : (ANF.normalizeExpr sf.expr k).run n = .ok (.break label, m) := by
      simp only [ANF.State.expr] at hnorm; exact hnorm
    have hk_no_break : ∀ (t : ANF.Trivial) (n' m' : Nat),
        (k t).run n' = .ok (.break label, m') → False := by
      intro t n' m' hkt
      obtain ⟨m'', htriv⟩ := hk_triv t n'
      rw [htriv] at hkt; cases hkt
    have hbreak_head := ANF.normalizeExpr_break_implies_hasBreakInHead sf.expr k hk_triv label n m hnorm_simp
    generalize hge : sf.expr = e_flat at hbreak_head hnorm_simp hewf
    cases hbreak_head with
    | break_direct =>
      have hflat_step : Flat.step? sf =
          some (.error ("break:" ++ (label.getD "")),
                ⟨.lit .undefined, sf.env, sf.heap,
                 sf.trace ++ [.error ("break:" ++ (label.getD ""))],
                 sf.funcs, sf.callStack⟩) := by
        cases sf with | mk e env heap trace funcs cs =>
        simp only [Flat.State.expr] at hge; subst hge
        unfold Flat.step?; rfl
      refine ⟨⟨.lit .undefined, sf.env, sf.heap,
               sf.trace ++ [.error ("break:" ++ (label.getD ""))],
               sf.funcs, sf.callStack⟩,
              [.error ("break:" ++ (label.getD ""))],
              Flat.Steps.tail (Flat.Step.mk hflat_step) (Flat.Steps.refl _), ?_, ?_, ?_⟩
      · simp [observableTrace_error, observableTrace_nil]
      · refine ⟨?_, ?_, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · exact hheap
        · exact henv
        · simp only [observableTrace_append, observableTrace_error, observableTrace_nil]
          congr 1
        · exact ANF.normalizeExpr_lit_undefined_trivial n
      · simp; intro x hfx; cases hfx
    | seq_left h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.seq_left h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | seq_right h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.seq_right h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | let_init h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.let_init h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getProp_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.getProp_obj h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setProp_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.setProp_obj h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setProp_val h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.setProp_val h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | binary_lhs h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.binary_lhs h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | binary_rhs h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.binary_rhs h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | unary_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.unary_arg h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | typeof_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.typeof_arg h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | deleteProp_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.deleteProp_obj h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | assign_val h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.assign_val h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | call_func h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.call_func h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | call_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.call_env h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | call_args h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.call_args h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | newObj_func h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.newObj_func h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | newObj_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.newObj_env h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | newObj_args h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.newObj_args h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | if_cond h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.if_cond h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | throw_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.throw_arg h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | return_some_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.return_some_arg h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | yield_some_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.yield_some_arg h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | await_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.await_arg h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getIndex_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.getIndex_obj h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getIndex_idx h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.getIndex_idx h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setIndex_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.setIndex_obj h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setIndex_idx h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.setIndex_idx h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setIndex_val h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.setIndex_val h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getEnv_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.getEnv_env h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | makeClosure_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.makeClosure_env h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | makeEnv_values h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.makeEnv_values h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | objectLit_props h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.objectLit_props h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | arrayLit_elems h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasBreakInHead_flat_error_steps _ label (.arrayLit_elems h) sf hge hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
  | «continue» label =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp only [ANF.step?, ANF.pushTrace] at hstep_eq
    obtain ⟨rfl, rfl⟩ := hstep_eq
    have hnorm_simp : (ANF.normalizeExpr sf.expr k).run n = .ok (.continue label, m) := by
      simp only [ANF.State.expr] at hnorm; exact hnorm
    have hk_no_cont : ∀ (t : ANF.Trivial) (n' m' : Nat),
        (k t).run n' = .ok (.continue label, m') → False := by
      intro t n' m' hkt
      obtain ⟨m'', htriv⟩ := hk_triv t n'
      rw [htriv] at hkt; cases hkt
    have hcont_head := ANF.normalizeExpr_continue_implies_hasContinueInHead sf.expr k hk_triv label n m hnorm_simp
    generalize hge' : sf.expr = e_flat' at hcont_head hnorm_simp hewf
    cases hcont_head with
    | continue_direct =>
      have hflat_step : Flat.step? sf =
          some (.error ("continue:" ++ (label.getD "")),
                ⟨.lit .undefined, sf.env, sf.heap,
                 sf.trace ++ [.error ("continue:" ++ (label.getD ""))],
                 sf.funcs, sf.callStack⟩) := by
        cases sf with | mk e env heap trace funcs cs =>
        simp only [Flat.State.expr] at hge'; subst hge'
        unfold Flat.step?; rfl
      refine ⟨⟨.lit .undefined, sf.env, sf.heap,
               sf.trace ++ [.error ("continue:" ++ (label.getD ""))],
               sf.funcs, sf.callStack⟩,
              [.error ("continue:" ++ (label.getD ""))],
              Flat.Steps.tail (Flat.Step.mk hflat_step) (Flat.Steps.refl _), ?_, ?_, ?_⟩
      · simp [observableTrace_error, observableTrace_nil]
      · refine ⟨?_, ?_, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · exact hheap
        · exact henv
        · simp only [observableTrace_append, observableTrace_error, observableTrace_nil]
          congr 1
        · exact ANF.normalizeExpr_lit_undefined_trivial n
      · simp; intro x hfx; cases hfx
    | seq_left h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.seq_left h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | seq_right h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.seq_right h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | let_init h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.let_init h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getProp_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.getProp_obj h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setProp_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.setProp_obj h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setProp_val h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.setProp_val h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | binary_lhs h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.binary_lhs h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | binary_rhs h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.binary_rhs h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | unary_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.unary_arg h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | typeof_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.typeof_arg h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | deleteProp_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.deleteProp_obj h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | assign_val h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.assign_val h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | call_func h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.call_func h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | call_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.call_env h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | call_args h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.call_args h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | newObj_func h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.newObj_func h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | newObj_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.newObj_env h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | newObj_args h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.newObj_args h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | if_cond h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.if_cond h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | throw_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.throw_arg h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | return_some_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.return_some_arg h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | yield_some_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.yield_some_arg h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | await_arg h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.await_arg h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getIndex_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.getIndex_obj h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getIndex_idx h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.getIndex_idx h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setIndex_obj h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.setIndex_obj h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setIndex_idx h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.setIndex_idx h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | setIndex_val h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.setIndex_val h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | getEnv_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.getEnv_env h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | makeClosure_env h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.makeClosure_env h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | makeEnv_values h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.makeEnv_values h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | objectLit_props h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.objectLit_props h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx
    | arrayLit_elems h =>
      obtain ⟨sf', evs, hsteps, hexpr', henv', hheap', hfuncs', hcs', htrace', hobs'⟩ :=
        hasContinueInHead_flat_error_steps _ label (.arrayLit_elems h) sf hge' hewf
      refine ⟨sf', evs, hsteps, hobs'.symm, ?_, ?_⟩
      · refine ⟨hheap.trans hheap'.symm, henv.trans henv'.symm, ?_, fun t => pure (.trivial t), n, n, ?_, ANF.trivial_k_preserving⟩
        · simp only [htrace', observableTrace_append, hobs', observableTrace_error, observableTrace_nil]; congr 1
        · rw [hexpr']; exact ANF.normalizeExpr_lit_undefined_trivial n
      · rw [hexpr']; intro x hfx; cases hfx

set_option maxHeartbeats 400000 in
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
              rw [ha]; exact match hfx with
              | .seq_l _ _ _ hfx' => .seq_l _ _ _ (.seq_r _ _ _ hfx')
              | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
            exact match hfx with
            | .seq_l _ _ _ h' =>
              have : VarFreeIn x (Flat.Expr.seq a b) := by rw [ha]; exact .seq_l _ _ _ (.seq_r _ _ _ h')
              hwf x (by rw [hsf]; exact this)
            | .seq_r _ _ _ h' =>
              hwf x (by rw [hsf]; exact .seq_r _ _ _ h')
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
            exact match hfx with
            | .seq_l _ _ _ h' =>
              have : VarFreeIn x (Flat.Expr.seq a b) := by rw [ha]; exact .seq_l _ _ _ (.seq_r _ _ _ h')
              hwf x (by rw [hsf]; exact this)
            | .seq_r _ _ _ h' =>
              hwf x (by rw [hsf]; exact .seq_r _ _ _ h')
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
                rw [ha]; exact match hfx with
                | .seq_l _ _ _ hfx' => .seq_l _ _ _ (by
                    exact match hfx' with
                    | .seq_l _ _ _ hfx'' => by rw [ha1, hc]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx'')
                    | .seq_r _ _ _ hfx'' => .seq_r _ _ _ hfx'')
                | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
              rw [ha]; exact match hfx with
              | .seq_l _ _ _ hfx' => .seq_l _ _ _ (by
                  exact match hfx' with
                  | .seq_l _ _ _ hfx'' => by rw [ha1, hc]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx'')
                  | .seq_r _ _ _ hfx'' => .seq_r _ _ _ hfx'')
              | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
              rw [ha]; exact match hfx with
              | .seq_l _ _ _ hfx' => .seq_l _ _ _ (by
                  exact match hfx' with
                  | .seq_l _ _ _ hfx'' => by rw [ha1, hc]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx'')
                  | .seq_r _ _ _ hfx'' => .seq_r _ _ _ hfx'')
              | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
                  rw [ha]; exact match hfx with
                  | .seq_l _ _ _ hfx' => .seq_l _ _ _ (by
                      exact match hfx' with
                      | .seq_l _ _ _ hfx'' =>
                        by rw [ha1]; exact .seq_l _ _ _ (by
                          exact match hfx'' with
                          | .seq_l _ _ _ hfx''' => by rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                          | .seq_r _ _ _ hfx''' => .seq_r _ _ _ hfx''')
                      | .seq_r _ _ _ hfx'' => .seq_r _ _ _ hfx'')
                  | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
                rw [ha]; exact match hfx with
                | .seq_l _ _ _ hfx' => .seq_l _ _ _ (by
                    exact match hfx' with
                    | .seq_l _ _ _ hfx'' =>
                      by rw [ha1]; exact .seq_l _ _ _ (by
                        exact match hfx'' with
                        | .seq_l _ _ _ hfx''' => by rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                        | .seq_r _ _ _ hfx''' => .seq_r _ _ _ hfx''')
                    | .seq_r _ _ _ hfx'' => .seq_r _ _ _ hfx'')
                | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
                rw [ha]; exact match hfx with
                | .seq_l _ _ _ hfx' => .seq_l _ _ _ (by
                    exact match hfx' with
                    | .seq_l _ _ _ hfx'' =>
                      by rw [ha1]; exact .seq_l _ _ _ (by
                        exact match hfx'' with
                        | .seq_l _ _ _ hfx''' => by rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                        | .seq_r _ _ _ hfx''' => .seq_r _ _ _ hfx''')
                    | .seq_r _ _ _ hfx'' => .seq_r _ _ _ hfx'')
                | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
                rw [ha]; exact match hfx with
                | .seq_l _ _ _ hfx' => .seq_l _ _ _ (by
                    exact match hfx' with
                    | .seq_l _ _ _ hfx'' =>
                      by rw [ha1]; exact .seq_l _ _ _ (by
                        exact match hfx'' with
                        | .seq_l _ _ _ hfx''' => by rw [hc, hc1]; exact .seq_l _ _ _ (.seq_r _ _ _ hfx''')
                        | .seq_r _ _ _ hfx''' => .seq_r _ _ _ hfx''')
                    | .seq_r _ _ _ hfx'' => .seq_r _ _ _ hfx'')
                | .seq_r _ _ _ hfx' => .seq_r _ _ _ hfx'
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
