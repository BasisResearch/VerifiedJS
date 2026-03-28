/-
  VerifiedJS — ANF Conversion: JS.Flat → JS.ANF
  Converts to A-normal form: names all subexpressions.
-/

import VerifiedJS.Flat.Syntax
import VerifiedJS.ANF.Syntax
import VerifiedJS.Core.Syntax

namespace VerifiedJS.ANF

/-- Converter monad carrying a fresh-name counter and conversion errors. -/
abbrev ConvM := StateT Nat (Except String)

def freshName : ConvM String := do
  let n ← get
  set (n + 1)
  pure s!"_anf{n}"

def bindComplex (rhs : ComplexExpr) (k : Trivial → ConvM Expr) : ConvM Expr := do
  let tmp ← freshName
  let body ← k (.var tmp)
  pure (.let tmp rhs body)

def trivialOfFlatValue : Flat.Value → Except String Trivial
  | .null => .ok .litNull
  | .undefined => .ok .litUndefined
  | .bool b => .ok (.litBool b)
  | .number n => .ok (.litNum n)
  | .string s => .ok (.litStr s)
  | .object addr => .ok (.litObject addr)
  | .closure funcIdx envPtr => .ok (.litClosure funcIdx envPtr)

mutual

def normalizeExpr (e : Flat.Expr) (k : Trivial → ConvM Expr) : ConvM Expr := do
  match e with
  | .lit v =>
    match trivialOfFlatValue v with
    | .ok t => k t
    | .error err => throw err
  | .var name => k (.var name)
  | .«let» name init body =>
    normalizeExpr init (fun initTriv => do
      let bodyExpr ← normalizeExpr body k
      pure (.let name (.trivial initTriv) bodyExpr))
  | .assign name value =>
    normalizeExpr value (fun valueTriv => bindComplex (.assign name valueTriv) k)
  | .«if» cond then_ else_ =>
    normalizeExpr cond (fun condTriv => do
      let thenExpr ← normalizeExpr then_ k
      let elseExpr ← normalizeExpr else_ k
      pure (.«if» condTriv thenExpr elseExpr))
  | .seq a b =>
    normalizeExpr a (fun _ => normalizeExpr b k)
  | .call funcIdx envPtr args =>
    normalizeExpr funcIdx (fun calleeTriv =>
      normalizeExpr envPtr (fun envTriv =>
        normalizeExprList args (fun argTrivs =>
          bindComplex (.call calleeTriv envTriv argTrivs) k)))
  | .newObj funcIdx envPtr args =>
    normalizeExpr funcIdx (fun calleeTriv =>
      normalizeExpr envPtr (fun envTriv =>
        normalizeExprList args (fun argTrivs =>
          bindComplex (.newObj calleeTriv envTriv argTrivs) k)))
  | .getProp obj prop =>
    normalizeExpr obj (fun objTriv => bindComplex (.getProp objTriv prop) k)
  | .setProp obj prop value =>
    normalizeExpr obj (fun objTriv =>
      normalizeExpr value (fun valueTriv =>
        bindComplex (.setProp objTriv prop valueTriv) k))
  | .getIndex obj idx =>
    normalizeExpr obj (fun objTriv =>
      normalizeExpr idx (fun idxTriv =>
        bindComplex (.getIndex objTriv idxTriv) k))
  | .setIndex obj idx value =>
    normalizeExpr obj (fun objTriv =>
      normalizeExpr idx (fun idxTriv =>
        normalizeExpr value (fun valueTriv =>
          bindComplex (.setIndex objTriv idxTriv valueTriv) k)))
  | .deleteProp obj prop =>
    normalizeExpr obj (fun objTriv => bindComplex (.deleteProp objTriv prop) k)
  | .typeof arg =>
    normalizeExpr arg (fun argTriv => bindComplex (.typeof argTriv) k)
  | .getEnv envPtr idx =>
    normalizeExpr envPtr (fun envTriv => bindComplex (.getEnv envTriv idx) k)
  | .makeEnv values =>
    normalizeExprList values (fun valueTrivs => bindComplex (.makeEnv valueTrivs) k)
  | .makeClosure funcIdx env =>
    normalizeExpr env (fun envTriv => bindComplex (.makeClosure funcIdx envTriv) k)
  | .objectLit props =>
    normalizeProps props (fun anfProps => bindComplex (.objectLit anfProps) k)
  | .arrayLit elems =>
    normalizeExprList elems (fun elemTrivs => bindComplex (.arrayLit elemTrivs) k)
  | .throw arg =>
    normalizeExpr arg (fun argTriv => pure (.throw argTriv))
  | .tryCatch body catchParam catchBody finally_ => do
    let bodyExpr ← normalizeExpr body k
    let catchExpr ← normalizeExpr catchBody k
    let finallyExpr ←
      match finally_ with
      | some fin => some <$> normalizeExpr fin (fun _ => pure (.trivial .litUndefined))
      | none => pure none
    pure (.tryCatch bodyExpr catchParam catchExpr finallyExpr)
  | .while_ cond body => do
    let condExpr ← normalizeExpr cond (fun condTriv => pure (.trivial condTriv))
    let bodyExpr ← normalizeExpr body (fun _ => pure (.trivial .litUndefined))
    let rest ← k .litUndefined
    pure (.seq (.while_ condExpr bodyExpr) rest)
  | .«break» label =>
    pure (.«break» label)
  | .«continue» label =>
    pure (.«continue» label)
  | .labeled label body => do
    let bodyExpr ← normalizeExpr body k
    pure (.labeled label bodyExpr)
  | .«return» arg =>
    match arg with
    | some value => normalizeExpr value (fun t => pure (.«return» (some t)))
    | none => pure (.«return» none)
  | .yield arg delegate =>
    match arg with
    | some value => normalizeExpr value (fun t => pure (.yield (some t) delegate))
    | none => pure (.yield none delegate)
  | .await arg =>
    normalizeExpr arg (fun argTriv => pure (.await argTriv))
  | .this =>
    k (.var "this")
  | .unary op arg =>
    normalizeExpr arg (fun argTriv => bindComplex (.unary op argTriv) k)
  | .binary op lhs rhs =>
    normalizeExpr lhs (fun lhsTriv =>
      normalizeExpr rhs (fun rhsTriv =>
        bindComplex (.binary op lhsTriv rhsTriv) k))
  termination_by e.depth
  decreasing_by all_goals (try cases ‹Option Flat.Expr›) <;> simp_all [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth] <;> omega

def normalizeExprList (es : List Flat.Expr)
    (k : List Trivial → ConvM Expr) : ConvM Expr := do
  match es with
  | [] => k []
  | e :: rest =>
    normalizeExpr e (fun t =>
      normalizeExprList rest (fun ts => k (t :: ts)))
  termination_by Flat.Expr.listDepth es
  decreasing_by all_goals simp_all [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth] <;> omega

def normalizeProps (props : List (Flat.PropName × Flat.Expr))
    (k : List (PropName × Trivial) → ConvM Expr) : ConvM Expr := do
  match props with
  | [] => k []
  | (name, value) :: rest =>
    normalizeExpr value (fun valueTriv =>
      normalizeProps rest (fun tail => k ((name, valueTriv) :: tail)))
  termination_by Flat.Expr.propListDepth props
  decreasing_by all_goals simp_all [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth] <;> omega

end

private def convertFuncDef (f : Flat.FuncDef) : Except String FuncDef := do
  let body ← (normalizeExpr f.body (fun t => pure (.trivial t))).run' 0
  pure
    { name := f.name
      params := f.params
      envParam := f.envParam
      body := body }

/-- Convert a Flat program to ANF -/
def convert (prog : Flat.Program) : Except String Program := do
  let functions ← prog.functions.toList.mapM convertFuncDef
  let main ← (normalizeExpr prog.main (fun t => pure (.trivial t))).run' 0
  pure
    { functions := functions.toArray
      main := main }

/-- When convert succeeds, the main expression comes from normalizeExpr. -/
theorem convert_main_from_normalizeExpr (prog : Flat.Program) (t : Program)
    (h : convert prog = .ok t) :
    ∃ m, (normalizeExpr prog.main (fun t => pure (.trivial t))).run 0 = .ok (t.main, m) := by
  -- StateT.run is definitionally equal to function application for StateT
  show ∃ m, normalizeExpr prog.main (fun t => pure (.trivial t)) 0 = .ok (t.main, m)
  -- Extract from convert that t.main = fst of normalizeExpr result
  unfold convert at h
  simp only [Bind.bind, Except.bind] at h
  -- Split on mapM result
  match hfns : prog.functions.toList.mapM convertFuncDef with
  | .error _ => simp [hfns] at h
  | .ok fns =>
    simp only [hfns, Except.ok.injEq] at h
    -- h is now about StateT.run'
    -- run' calls normalizeExpr ... 0 and maps Prod.fst
    match hnorm : normalizeExpr prog.main (fun t => pure (Expr.trivial t)) 0 with
    | .ok (expr, counter) =>
      -- run' with .ok result maps to .ok expr
      have : (StateT.run' (normalizeExpr prog.main (fun t => pure (Expr.trivial t))) 0) = .ok expr := by
        show (Prod.fst <$> (normalizeExpr prog.main (fun t => pure (Expr.trivial t)) 0 : Except String _)) = .ok expr
        rw [hnorm]; rfl
      rw [this] at h
      -- h : pure { functions := fns.toArray, main := expr } = Except.ok t
      -- pure = Except.ok for Except
      change Except.ok { functions := fns.toArray, main := expr } = Except.ok t at h
      simp only [Except.ok.injEq] at h
      -- h : { functions := fns.toArray, main := expr } = t
      have hmain : expr = t.main := congrArg Program.main h
      subst hmain; exact ⟨counter, rfl⟩
    | .error e =>
      have : (StateT.run' (normalizeExpr prog.main (fun t => pure (Expr.trivial t))) 0) = .error e := by
        show (Prod.fst <$> (normalizeExpr prog.main (fun t => pure (Expr.trivial t)) 0 : Except String _)) = .error e
        rw [hnorm]; rfl
      rw [this] at h
      simp at h

@[simp] theorem normalizeExpr_break (label : Option Flat.LabelName) (k : Trivial → ConvM Expr) :
    normalizeExpr (.«break» label) k = pure (.«break» label) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_continue (label : Option Flat.LabelName) (k : Trivial → ConvM Expr) :
    normalizeExpr (.«continue» label) k = pure (.«continue» label) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_labeled (label : Flat.LabelName) (body : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.labeled label body) k = (do
      let bodyExpr ← normalizeExpr body k
      pure (.labeled label bodyExpr)) := by
  simp [normalizeExpr]

/-! ## No-confusion lemmas for normalizeExpr producing .labeled -/

/-- bindComplex always produces .let, never .labeled -/
theorem bindComplex_not_labeled (rhs : ComplexExpr) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr) :
    (bindComplex rhs k).run n ≠ .ok (.labeled label body, m) := by
  unfold bindComplex freshName
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure, StateT.pure, Except.pure]
  intro h; split at h
  · simp at h
  · exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- normalizeExpr (.return none) always produces .return none, never .labeled -/
theorem normalizeExpr_return_none_not_labeled (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.«return» none) k).run n ≠ .ok (.labeled label body, m) := by
  simp only [normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run]
  intro h; exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- normalizeExpr (.yield none d) always produces .yield none d, never .labeled -/
theorem normalizeExpr_yield_none_not_labeled (d : Bool) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.yield none d) k).run n ≠ .ok (.labeled label body, m) := by
  simp only [normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run]
  intro h; exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- normalizeExpr (.break l) never produces .labeled -/
theorem normalizeExpr_break_not_labeled' (l : Option Flat.LabelName) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.«break» l) k).run n ≠ .ok (.labeled label body, m) := by
  simp only [normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run]
  intro h; exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- normalizeExpr (.continue l) never produces .labeled -/
theorem normalizeExpr_continue_not_labeled' (l : Option Flat.LabelName) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.«continue» l) k).run n ≠ .ok (.labeled label body, m) := by
  simp only [normalizeExpr, pure, Pure.pure, StateT.pure, Except.pure, StateT.run]
  intro h; exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- When k always produces .trivial, normalizeExpr (.var name) k never produces .labeled -/
theorem normalizeExpr_var_not_labeled (name : Flat.VarName) (k : Trivial → ConvM Expr)
    (hk : ∀ (arg : Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (n m : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.var name) k).run n ≠ .ok (.labeled label body, m) := by
  simp only [normalizeExpr]
  obtain ⟨m', hm'⟩ := hk (.var name) n
  rw [hm']; intro h; exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- When k always produces .trivial, normalizeExpr (.this) k never produces .labeled -/
theorem normalizeExpr_this_not_labeled (k : Trivial → ConvM Expr)
    (hk : ∀ (arg : Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (n m : Nat) (label : String) (body : Expr) :
    (normalizeExpr .this k).run n ≠ .ok (.labeled label body, m) := by
  simp only [normalizeExpr]
  obtain ⟨m', hm'⟩ := hk (.var "this") n
  rw [hm']; intro h; exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- When k always produces .trivial, normalizeExpr (.lit v) k never produces .labeled -/
theorem normalizeExpr_lit_not_labeled (v : Flat.Value) (k : Trivial → ConvM Expr)
    (hk : ∀ (arg : Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (n m : Nat) (label : String) (body : Expr) :
    (normalizeExpr (.lit v) k).run n ≠ .ok (.labeled label body, m) := by
  simp only [normalizeExpr]
  cases htv : trivialOfFlatValue v with
  | error msg =>
    change ¬StateT.lift (Except.error msg) n = _
    simp [StateT.lift, Functor.map, Except.map]
  | ok triv =>
    obtain ⟨m', hm'⟩ := hk triv n
    rw [hm']; intro h; exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-! ## Continuation no-confusion: specific continuations never produce .labeled -/

/-- The continuation (fun t => pure (.return (some t))) never produces .labeled -/
theorem return_some_k_not_labeled (t : Trivial) (n m : Nat) (label : String) (body : Expr) :
    ((fun (t : Trivial) => (pure (.«return» (some t)) : ConvM Expr)) t).run n ≠
    .ok (.labeled label body, m) := by
  simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]

/-- The continuation (fun t => pure (.throw t)) never produces .labeled -/
theorem throw_k_not_labeled (t : Trivial) (n m : Nat) (label : String) (body : Expr) :
    ((fun (t : Trivial) => (pure (.throw t) : ConvM Expr)) t).run n ≠
    .ok (.labeled label body, m) := by
  simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]

/-- The continuation (fun t => pure (.await t)) never produces .labeled -/
theorem await_k_not_labeled (t : Trivial) (n m : Nat) (label : String) (body : Expr) :
    ((fun (t : Trivial) => (pure (.await t) : ConvM Expr)) t).run n ≠
    .ok (.labeled label body, m) := by
  simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]

/-- The continuation (fun t => pure (.yield (some t) d)) never produces .labeled -/
theorem yield_some_k_not_labeled (t : Trivial) (d : Bool) (n m : Nat) (label : String) (body : Expr) :
    ((fun (t : Trivial) => (pure (.yield (some t) d) : ConvM Expr)) t).run n ≠
    .ok (.labeled label body, m) := by
  simp [pure, Pure.pure, StateT.pure, Except.pure, StateT.run]

/-- bindComplex always produces .let constructor -/
theorem bindComplex_produces_let (rhs : ComplexExpr) (k : Trivial → ConvM Expr)
    (n : Nat) (result : Expr) (m : Nat)
    (h : (bindComplex rhs k).run n = .ok (result, m)) :
    ∃ name body, result = .let name rhs body := by
  unfold bindComplex freshName at h
  simp only [bind, Bind.bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, set, MonadStateOf.set, StateT.set, pure, Pure.pure, StateT.pure, Except.pure] at h
  split at h
  · simp at h
  · exact ⟨_, _, ((Prod.mk.inj (Except.ok.inj h)).1).symm⟩

/-! ## Unfolding/rewrite lemmas for compound normalizeExpr cases -/

@[simp] theorem normalizeExpr_let' (name : String) (init body : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.«let» name init body) k = normalizeExpr init (fun initTriv => do
      let bodyExpr ← normalizeExpr body k
      pure (.let name (.trivial initTriv) bodyExpr)) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_if' (cond then_ else_ : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.«if» cond then_ else_) k = normalizeExpr cond (fun condTriv => do
      let thenExpr ← normalizeExpr then_ k
      let elseExpr ← normalizeExpr else_ k
      pure (.«if» condTriv thenExpr elseExpr)) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_assign' (name : String) (value : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.assign name value) k = normalizeExpr value (fun valueTriv => bindComplex (.assign name valueTriv) k) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_seq' (a b : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.seq a b) k = normalizeExpr a (fun _ => normalizeExpr b k) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_return_none' (k : Trivial → ConvM Expr) :
    normalizeExpr (.«return» none) k = pure (.«return» none) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_return_some' (v : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.«return» (some v)) k = normalizeExpr v (fun t => pure (.«return» (some t))) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_yield_none' (d : Bool) (k : Trivial → ConvM Expr) :
    normalizeExpr (.yield none d) k = pure (.yield none d) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_yield_some' (v : Flat.Expr) (d : Bool) (k : Trivial → ConvM Expr) :
    normalizeExpr (.yield (some v) d) k = normalizeExpr v (fun t => pure (.yield (some t) d)) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_throw' (arg : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.throw arg) k = normalizeExpr arg (fun argTriv => pure (.throw argTriv)) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_await' (arg : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.await arg) k = normalizeExpr arg (fun argTriv => pure (.await argTriv)) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_var' (name : Flat.VarName) (k : Trivial → ConvM Expr) :
    normalizeExpr (.var name) k = k (.var name) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_this' (k : Trivial → ConvM Expr) :
    normalizeExpr .this k = k (.var "this") := by
  simp [normalizeExpr]

/-! ## Continuation no-confusion for compound normalizeExpr cases -/

/-- The let-continuation never produces .labeled because it always wraps in .let. -/
theorem let_k_not_labeled (name : String) (body : Flat.Expr) (k : Trivial → ConvM Expr)
    (initTriv : Trivial) (n m : Nat) (label : String) (b : Expr) :
    ((fun (initTriv : Trivial) => (do
      let bodyExpr ← normalizeExpr body k
      pure (.let name (ComplexExpr.trivial initTriv) bodyExpr) : ConvM Expr)) initTriv).run n
    ≠ .ok (.labeled label b, m) := by
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; split at h
  · simp at h
  · exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1

/-- The if-continuation never produces .labeled because it wraps in .if. -/
theorem if_k_not_labeled (then_ else_ : Flat.Expr) (k : Trivial → ConvM Expr)
    (condTriv : Trivial) (n m : Nat) (label : String) (b : Expr) :
    ((fun (condTriv : Trivial) => (do
      let thenExpr ← normalizeExpr then_ k
      let elseExpr ← normalizeExpr else_ k
      pure (.«if» condTriv thenExpr elseExpr) : ConvM Expr)) condTriv).run n
    ≠ .ok (.labeled label b, m) := by
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h; repeat (first | split at h | simp at h | (simp [pure, Pure.pure, StateT.pure, Except.pure] at h; try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

/-- Any bindComplex-based continuation never produces .labeled. -/
theorem bindComplex_k_not_labeled (mkComplex : Trivial → ComplexExpr) (k : Trivial → ConvM Expr)
    (t : Trivial) (n m : Nat) (label : String) (body : Expr) :
    ((fun (t : Trivial) => bindComplex (mkComplex t) k) t).run n
    ≠ .ok (.labeled label body, m) :=
  bindComplex_not_labeled (mkComplex t) k n m label body

/-! ## Universal not-labeled lemmas (any k) -/

/-- normalizeExpr (.while_ cond body) k never produces .labeled for ANY k. -/
theorem normalizeExpr_while_not_labeled_any_k (cond body_w : Flat.Expr) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (b : Expr) :
    (normalizeExpr (.while_ cond body_w) k).run n ≠ .ok (.labeled label b, m) := by
  simp only [normalizeExpr]
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h
  repeat (first | split at h | simp at h |
    (simp [pure, Pure.pure, StateT.pure, Except.pure] at h;
     try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

/-- normalizeExpr (.tryCatch body cp cb none) k never produces .labeled. -/
theorem normalizeExpr_tryCatch_none_not_labeled_any_k
    (body_tc : Flat.Expr) (cp : String) (cb : Flat.Expr) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (b : Expr) :
    (normalizeExpr (.tryCatch body_tc cp cb none) k).run n ≠ .ok (.labeled label b, m) := by
  simp only [normalizeExpr]
  simp only [bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h
  repeat (first | split at h | simp at h |
    (simp [pure, Pure.pure, StateT.pure, Except.pure] at h;
     try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

/-- normalizeExpr (.tryCatch body cp cb (some fin)) k never produces .labeled. -/
theorem normalizeExpr_tryCatch_some_not_labeled_any_k
    (body_tc : Flat.Expr) (cp : String) (cb fin : Flat.Expr) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (b : Expr) :
    (normalizeExpr (.tryCatch body_tc cp cb (some fin)) k).run n ≠ .ok (.labeled label b, m) := by
  simp only [normalizeExpr]
  simp only [Functor.map, StateT.map, bind, Bind.bind, StateT.bind, StateT.run, Except.bind]
  intro h
  repeat (first | split at h | simp at h |
    (simp [pure, Pure.pure, StateT.pure, Except.pure] at h;
     try exact Expr.noConfusion (Prod.mk.inj (Except.ok.inj h)).1))

/-! ## Decomposition lemmas: when normalizeExpr of compound expr produces .labeled -/

/-- For .seq a b: labeled result comes from normalizeExpr a with seq-continuation. -/
theorem normalizeExpr_seq_labeled_source (a b : Flat.Expr) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.seq a b) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr a (fun _ => normalizeExpr b k)).run n = .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .throw arg: labeled result comes from normalizeExpr arg with throw-k. -/
theorem normalizeExpr_throw_labeled_source (arg : Flat.Expr) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.throw arg) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr arg (fun argTriv => pure (.throw argTriv))).run n = .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .await arg: labeled result comes from normalizeExpr arg with await-k. -/
theorem normalizeExpr_await_labeled_source (arg : Flat.Expr) (k : Trivial → ConvM Expr)
    (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.await arg) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr arg (fun argTriv => pure (.await argTriv))).run n = .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .assign name value: labeled result comes from normalizeExpr value with assign-k. -/
theorem normalizeExpr_assign_labeled_source (name : String) (value : Flat.Expr)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.assign name value) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr value (fun vt => bindComplex (.assign name vt) k)).run n =
    .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .let name init body: labeled result comes from normalizeExpr init with let-k. -/
theorem normalizeExpr_let_labeled_source (name : String) (init body : Flat.Expr)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (b : Expr)
    (h : (normalizeExpr (.let name init body) k).run n = .ok (.labeled label b, m)) :
    (normalizeExpr init (fun initTriv => do
      let bodyExpr ← normalizeExpr body k
      pure (.let name (.trivial initTriv) bodyExpr))).run n = .ok (.labeled label b, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .if cond then_ else_: labeled result comes from normalizeExpr cond with if-k. -/
theorem normalizeExpr_if_labeled_source (cond then_ else_ : Flat.Expr)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (b : Expr)
    (h : (normalizeExpr (.if cond then_ else_) k).run n = .ok (.labeled label b, m)) :
    (normalizeExpr cond (fun condTriv => do
      let thenExpr ← normalizeExpr then_ k
      let elseExpr ← normalizeExpr else_ k
      pure (.if condTriv thenExpr elseExpr))).run n = .ok (.labeled label b, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .unary op arg: decomposition. -/
theorem normalizeExpr_unary_labeled_source (op : Core.UnaryOp) (arg : Flat.Expr)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.unary op arg) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr arg (fun argTriv => bindComplex (.unary op argTriv) k)).run n =
    .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .typeof arg: decomposition. -/
theorem normalizeExpr_typeof_labeled_source (arg : Flat.Expr)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.typeof arg) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr arg (fun argTriv => bindComplex (.typeof argTriv) k)).run n =
    .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .deleteProp obj prop: decomposition. -/
theorem normalizeExpr_deleteProp_labeled_source (obj : Flat.Expr) (prop : Flat.PropName)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.deleteProp obj prop) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr obj (fun objTriv => bindComplex (.deleteProp objTriv prop) k)).run n =
    .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .getEnv envPtr idx: decomposition. -/
theorem normalizeExpr_getEnv_labeled_source (envPtr : Flat.Expr) (idx : Nat)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.getEnv envPtr idx) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr envPtr (fun envTriv => bindComplex (.getEnv envTriv idx) k)).run n =
    .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .makeClosure funcIdx env: decomposition. -/
theorem normalizeExpr_makeClosure_labeled_source (funcIdx : Flat.FuncIdx) (env : Flat.Expr)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.makeClosure funcIdx env) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr env (fun envTriv => bindComplex (.makeClosure funcIdx envTriv) k)).run n =
    .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

/-- For .getProp obj prop: decomposition. -/
theorem normalizeExpr_getProp_labeled_source (obj : Flat.Expr) (prop : Flat.PropName)
    (k : Trivial → ConvM Expr) (n m : Nat) (label : String) (body : Expr)
    (h : (normalizeExpr (.getProp obj prop) k).run n = .ok (.labeled label body, m)) :
    (normalizeExpr obj (fun objTriv => bindComplex (.getProp objTriv prop) k)).run n =
    .ok (.labeled label body, m) := by
  simp only [normalizeExpr] at h; exact h

end VerifiedJS.ANF
