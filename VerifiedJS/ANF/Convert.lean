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

end VerifiedJS.ANF
