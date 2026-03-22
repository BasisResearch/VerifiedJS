/-
  VerifiedJS — ANF IL Semantics
  Small-step LTS as an inductive relation.
  SPEC: ECMA-262 §8 (Execution Contexts), §13 (Runtime Semantics: Evaluation)
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Flat.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.ANF

/-- ECMA-262 §8.1 Environment Records (flattened lexical environment for ANF). -/
abbrev Env := List (VarName × Flat.Value)

/-- ECMA-262 §8.3 Execution Contexts (ANF machine state). -/
structure State where
  expr : Expr
  env : Env
  heap : Core.Heap
  trace : List Core.TraceEvent
  deriving Repr

/-- Empty ANF lexical environment. -/
def Env.empty : Env := []

/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lexical lookup). -/
def Env.lookup (env : Env) (name : VarName) : Option Flat.Value :=
  match env.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

private def updateBindingList (xs : Env) (name : VarName) (v : Flat.Value) : Env :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Flat.Value) : Env :=
  if env.any (fun kv => kv.fst == name) then
    updateBindingList env name v
  else
    (name, v) :: env

/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Flat.Value) : Env :=
  (name, v) :: env

private def pushTrace (s : State) (t : Core.TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

/-- Convert an ANF literal-like trivial to a Flat value when possible. -/
@[simp]
def trivialValue? : Trivial → Option Flat.Value
  | .var _ => none
  | .litNull => some .null
  | .litUndefined => some .undefined
  | .litBool b => some (.bool b)
  | .litNum n => some (.number n)
  | .litStr s => some (.string s)
  | .litObject addr => some (.object addr)
  | .litClosure funcIdx envPtr => some (.closure funcIdx envPtr)

private def trivialOfValue : Flat.Value → Trivial
  | .null => .litNull
  | .undefined => .litUndefined
  | .bool b => .litBool b
  | .number n => .litNum n
  | .string s => .litStr s
  | .object addr => .litObject addr
  | .closure funcIdx envPtr => .litClosure funcIdx envPtr

/-- Evaluate a trivial in the current environment (variables may fail with ReferenceError). -/
def evalTrivial (env : Env) : Trivial → Except String Flat.Value
  | .var name =>
      match env.lookup name with
      | some v => .ok v
      | none => .error s!"ReferenceError: {name}"
  | t =>
      match trivialValue? t with
      | some v => .ok v
      | none => .error "TypeError: invalid trivial"

private def evalTrivialList (env : Env) (ts : List Trivial) : Except String (List Flat.Value) :=
  ts.mapM (evalTrivial env)

private def toBoolean : Flat.Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .closure _ _ => true

private def toNumber : Flat.Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | _ => 0.0

private def evalUnary : Core.UnaryOp → Flat.Value → Flat.Value
  | .neg, v => .number (-toNumber v)
  | .pos, v => .number (toNumber v)
  | .logNot, v => .bool (!toBoolean v)
  | .void, _ => .undefined
  | .bitNot, _ => .undefined

private def evalBinary : Core.BinOp → Flat.Value → Flat.Value → Flat.Value
  | .add, .string a, .string b => .string (a ++ b)
  | .add, a, b => .number (toNumber a + toNumber b)
  | .sub, a, b => .number (toNumber a - toNumber b)
  | .mul, a, b => .number (toNumber a * toNumber b)
  | .div, a, b => .number (toNumber a / toNumber b)
  | .eq, a, b => .bool (a == b)
  | .neq, a, b => .bool (a != b)
  | .strictEq, a, b => .bool (a == b)
  | .strictNeq, a, b => .bool (a != b)
  | .lt, a, b => .bool (toNumber a < toNumber b)
  | .gt, a, b => .bool (toNumber a > toNumber b)
  | .le, a, b => .bool (toNumber a <= toNumber b)
  | .ge, a, b => .bool (toNumber a >= toNumber b)
  | .logAnd, a, b => if toBoolean a then b else a
  | .logOr, a, b => if toBoolean a then a else b
  | _, _, _ => .undefined

private def flatToCoreValue : Flat.Value → Core.Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  | .closure funcIdx _ => .function funcIdx

private def coreToFlatValue : Core.Value → Flat.Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  | .function idx => .closure idx 0

private def envSlotKey (idx : Nat) : PropName :=
  "__env" ++ toString idx

private def encodeEnvPropsAux (idx : Nat) (values : List Flat.Value) : List (PropName × Core.Value) :=
  match values with
  | [] => []
  | v :: rest => (envSlotKey idx, flatToCoreValue v) :: encodeEnvPropsAux (idx + 1) rest

private def encodeEnvProps (values : List Flat.Value) : List (PropName × Core.Value) :=
  encodeEnvPropsAux 0 values

private def allocFreshObject (h : Core.Heap) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap := { objects := h.objects.push [], nextAddr := addr + 1 }
  (addr, h')

private def allocEnvObject (h : Core.Heap) (values : List Flat.Value) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap := { objects := h.objects.push (encodeEnvProps values), nextAddr := addr + 1 }
  (addr, h')

private def heapObjectAt? (h : Core.Heap) (addr : Nat) : Option (List (Core.PropName × Core.Value)) :=
  if hAddr : addr < h.objects.size then
    let _ := hAddr
    some (h.objects[addr]!)
  else
    none

private def typeofValue : Flat.Value → Flat.Value
  | .undefined => .string "undefined"
  | .null => .string "object"
  | .bool _ => .string "boolean"
  | .number _ => .string "number"
  | .string _ => .string "string"
  | .object _ => .string "object"
  | .closure _ _ => .string "function"

private structure ComplexResult where
  event : Core.TraceEvent
  env : Env
  heap : Core.Heap
  value : Flat.Value

private def mkError (msg : String) (s : State) : ComplexResult :=
  { event := .error msg, env := s.env, heap := s.heap, value := .undefined }

/-- Evaluate one ANF complex expression atomically. -/
def evalComplex (s : State) (rhs : ComplexExpr) : ComplexResult :=
  match rhs with
  | .trivial t =>
      match evalTrivial s.env t with
      | .ok v => { event := .silent, env := s.env, heap := s.heap, value := v }
      | .error msg => mkError msg s
  | .assign name value =>
      match evalTrivial s.env value with
      | .ok v => { event := .silent, env := s.env.assign name v, heap := s.heap, value := v }
      | .error msg => mkError msg s
  | .call callee env args =>
      match evalTrivial s.env callee, evalTrivial s.env env, evalTrivialList s.env args with
      | .ok _, .ok _, .ok _ => { event := .silent, env := s.env, heap := s.heap, value := .undefined }
      | .error msg, _, _ => mkError msg s
      | _, .error msg, _ => mkError msg s
      | _, _, .error msg => mkError msg s
  | .newObj callee env args =>
      match evalTrivial s.env callee, evalTrivial s.env env, evalTrivialList s.env args with
      | .ok _, .ok _, .ok _ =>
          let (addr, heap') := allocFreshObject s.heap
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg, _, _ => mkError msg s
      | _, .error msg, _ => mkError msg s
      | _, _, .error msg => mkError msg s
  | .getProp obj _prop =>
      match evalTrivial s.env obj with
      | .ok (.object _) => { event := .silent, env := s.env, heap := s.heap, value := .undefined }
      | .ok _ => mkError "TypeError: getProp on non-object" s
      | .error msg => mkError msg s
  | .setProp obj _prop value =>
      match evalTrivial s.env obj, evalTrivial s.env value with
      | .ok (.object _), .ok v => { event := .silent, env := s.env, heap := s.heap, value := v }
      | .ok (.object _), .error msg => mkError msg s
      | .ok _, _ => mkError "TypeError: setProp on non-object" s
      | .error msg, _ => mkError msg s
  | .getIndex obj idx =>
      match evalTrivial s.env obj, evalTrivial s.env idx with
      | .ok (.object _), .ok _ => { event := .silent, env := s.env, heap := s.heap, value := .undefined }
      | .ok (.object _), .error msg => mkError msg s
      | .ok _, _ => mkError "TypeError: getIndex on non-object" s
      | .error msg, _ => mkError msg s
  | .setIndex obj idx value =>
      match evalTrivial s.env obj, evalTrivial s.env idx, evalTrivial s.env value with
      | .ok (.object _), .ok _, .ok v => { event := .silent, env := s.env, heap := s.heap, value := v }
      | .ok (.object _), .error msg, _ => mkError msg s
      | .ok (.object _), _, .error msg => mkError msg s
      | .ok _, _, _ => mkError "TypeError: setIndex on non-object" s
      | .error msg, _, _ => mkError msg s
  | .deleteProp obj _prop =>
      match evalTrivial s.env obj with
      | .ok _ => { event := .silent, env := s.env, heap := s.heap, value := .bool true }
      | .error msg => mkError msg s
  | .typeof arg =>
      match evalTrivial s.env arg with
      | .ok v => { event := .silent, env := s.env, heap := s.heap, value := typeofValue v }
      | .error _ =>
          -- typeof undeclared identifiers does not throw in JavaScript.
          { event := .silent, env := s.env, heap := s.heap, value := .string "undefined" }
  | .getEnv envTriv idx =>
      match evalTrivial s.env envTriv with
      | .ok (.object envPtr) =>
          match heapObjectAt? s.heap envPtr with
          | some props =>
              let key := envSlotKey idx
              match props.find? (fun kv => kv.fst == key) with
              | some kv =>
                  { event := .silent, env := s.env, heap := s.heap, value := coreToFlatValue kv.snd }
              | none => mkError s!"ReferenceError: missing env slot {key}" s
          | none => mkError s!"TypeError: dangling env pointer {envPtr}" s
      | .ok _ => mkError "TypeError: invalid env pointer" s
      | .error msg => mkError msg s
  | .makeEnv values =>
      match evalTrivialList s.env values with
      | .ok captured =>
          let (addr, heap') := allocEnvObject s.heap captured
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg => mkError msg s
  | .makeClosure funcIdx env =>
      match evalTrivial s.env env with
      | .ok (.object envPtr) => { event := .silent, env := s.env, heap := s.heap, value := .closure funcIdx envPtr }
      | .ok _ => mkError "TypeError: invalid closure environment" s
      | .error msg => mkError msg s
  | .objectLit props =>
      match props.mapM (fun (_, t) => evalTrivial s.env t) with
      | .ok _ =>
          let (addr, heap') := allocFreshObject s.heap
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg => mkError msg s
  | .arrayLit elems =>
      match evalTrivialList s.env elems with
      | .ok _ =>
          let (addr, heap') := allocFreshObject s.heap
          { event := .silent, env := s.env, heap := heap', value := .object addr }
      | .error msg => mkError msg s
  | .unary op arg =>
      match evalTrivial s.env arg with
      | .ok v => { event := .silent, env := s.env, heap := s.heap, value := evalUnary op v }
      | .error msg => mkError msg s
  | .binary op lhs rhs =>
      match evalTrivial s.env lhs, evalTrivial s.env rhs with
      | .ok lv, .ok rv => { event := .silent, env := s.env, heap := s.heap, value := evalBinary op lv rv }
      | .error msg, _ => mkError msg s
      | _, .error msg => mkError msg s

/-- Check whether an ANF expression is already a value expression. -/
@[simp]
def exprValue? : Expr → Option Flat.Value
  | .trivial t => trivialValue? t
  | _ => none

/-- One deterministic ANF small-step transition with emitted trace event. -/
def step? (s : State) : Option (Core.TraceEvent × State) :=
  match h : s.expr with
  | .trivial t =>
      match t with
      | .var name =>
          match s.env.lookup name with
          | some v =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
          | none =>
              let msg := s!"ReferenceError: {name}"
              let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
              some (.error msg, s')
      | _ =>
          -- Literal trivials are final values in ANF and do not step further.
          none
  | .«let» name rhs body =>
      let r := evalComplex s rhs
      let s' := pushTrace { s with expr := body, env := r.env.extend name r.value, heap := r.heap } r.event
      some (r.event, s')
  | .seq a b =>
      match exprValue? a with
      | some _ =>
          let s' := pushTrace { s with expr := b } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := a } with
          | some (t, sa) =>
              let s' := pushTrace { s with expr := .seq sa.expr b, env := sa.env, heap := sa.heap } t
              some (t, s')
          | none => none
  | .«if» cond then_ else_ =>
      match evalTrivial s.env cond with
      | .ok v =>
          let next := if toBoolean v then then_ else else_
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | .error msg =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
          some (.error msg, s')
  | .while_ cond body =>
      match exprValue? cond with
      | some v =>
          let next := if toBoolean v then .seq body (.while_ cond body) else .trivial .litUndefined
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := cond } with
          | some (t, sc) =>
              let s' := pushTrace { s with expr := .while_ sc.expr body, env := sc.env, heap := sc.heap } t
              some (t, s')
          | none => none
  | .throw arg =>
      match evalTrivial s.env arg with
      | .ok _ =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error "throw")
          some (.error "throw", s')
      | .error msg =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
          some (.error msg, s')
  | .tryCatch body catchParam catchBody finally_ =>
      match exprValue? body with
      | some v =>
          match finally_ with
          | some fin =>
              let s' := pushTrace { s with expr := .seq fin (.trivial (trivialOfValue v)) } .silent
              some (.silent, s')
          | none =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
      | none =>
          match step? { s with expr := body } with
          | some (.error msg, sb) =>
              let handler :=
                match finally_ with
                | some fin => .seq catchBody fin
                | none => catchBody
              let s' := pushTrace
                { s with expr := handler, env := sb.env.extend catchParam (.string msg), heap := sb.heap } (.error msg)
              some (.error msg, s')
          | some (t, sb) =>
              let s' := pushTrace
                { s with expr := .tryCatch sb.expr catchParam catchBody finally_, env := sb.env, heap := sb.heap } t
              some (t, s')
          | none => none
  | .«return» arg =>
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } .silent
          some (.silent, s')
      | some t =>
          match evalTrivial s.env t with
          | .ok v =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
          | .error msg =>
              let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
              some (.error msg, s')
  | .yield arg delegate =>
      let _ := delegate
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } .silent
          some (.silent, s')
      | some t =>
          match evalTrivial s.env t with
          | .ok v =>
              let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
              some (.silent, s')
          | .error msg =>
              let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
              some (.error msg, s')
  | .await arg =>
      match evalTrivial s.env arg with
      | .ok v =>
          let s' := pushTrace { s with expr := .trivial (trivialOfValue v) } .silent
          some (.silent, s')
      | .error msg =>
          let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
          some (.error msg, s')
  | .labeled _ body =>
      let s' := pushTrace { s with expr := body } .silent
      some (.silent, s')
  | .«break» label =>
      let l := label.getD ""
      let msg := "break:" ++ l
      let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
      some (.error msg, s')
  | .«continue» label =>
      let l := label.getD ""
      let msg := "continue:" ++ l
      let s' := pushTrace { s with expr := .trivial .litUndefined } (.error msg)
      some (.error msg, s')
  termination_by s.expr.depth
  decreasing_by all_goals (try cases ‹Option Expr›) <;> simp_all [Expr.depth] <;> omega

/-- Small-step relation induced by `step?`. -/
inductive Step : State → Core.TraceEvent → State → Prop where
  | mk {s : State} {t : Core.TraceEvent} {s' : State} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of ANF steps with trace accumulation. -/
inductive Steps : State → List Core.TraceEvent → State → Prop where
  | refl (s : State) : Steps s [] s
  | tail {s1 s2 s3 : State} {t : Core.TraceEvent} {ts : List Core.TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Initial ANF machine state for a program entry expression. -/
def initialState (p : Program) : State :=
  { expr := p.main, env := Env.empty, heap := Core.Heap.empty, trace := [] }

/-- Program behavior as finite terminating trace sequence. -/
def Behaves (p : Program) (b : List Core.TraceEvent) : Prop :=
  ∃ sFinal,
    Steps (initialState p) b sFinal ∧
    step? sFinal = none

/-- ANF literal trivials are final values and do not step. -/
@[simp]
theorem step?_litNull (s : State) :
    step? { s with expr := .trivial .litNull } = none := by
  simp [step?]

@[simp]
theorem step?_litUndefined (s : State) :
    step? { s with expr := .trivial .litUndefined } = none := by
  simp [step?]

@[simp]
theorem step?_litBool (s : State) (b : Bool) :
    step? { s with expr := .trivial (.litBool b) } = none := by
  simp [step?]

@[simp]
theorem step?_litNum (s : State) (n : Float) :
    step? { s with expr := .trivial (.litNum n) } = none := by
  simp [step?]

@[simp]
theorem step?_litStr (s : State) (str : String) :
    step? { s with expr := .trivial (.litStr str) } = none := by
  simp [step?]

@[simp]
theorem step?_litObject (s : State) (addr : Nat) :
    step? { s with expr := .trivial (.litObject addr) } = none := by
  simp [step?]

@[simp]
theorem step?_litClosure (s : State) (f e : Nat) :
    step? { s with expr := .trivial (.litClosure f e) } = none := by
  simp [step?]

/-- Variable lookup that succeeds produces the looked-up value. -/
@[simp]
theorem step?_var_found (s : State) (name : VarName) (v : Flat.Value)
    (h : s.env.lookup name = some v) :
    step? { s with expr := .trivial (.var name) } =
      some (.silent, pushTrace { s with expr := .trivial (trivialOfValue v) } .silent) := by
  simp [step?, h]

/-- Variable lookup that fails produces a ReferenceError. -/
@[simp]
theorem step?_var_not_found (s : State) (name : VarName)
    (h : s.env.lookup name = none) :
    step? { s with expr := .trivial (.var name) } =
      some (.error s!"ReferenceError: {name}",
            pushTrace { s with expr := .trivial .litUndefined } (.error s!"ReferenceError: {name}")) := by
  simp [step?, h]

/-- Let-binding always steps by evaluating the complex RHS immediately. -/
theorem step?_let (s : State) (name : VarName) (rhs : ComplexExpr) (body : Expr) :
    let r := evalComplex { s with expr := .let name rhs body } rhs
    step? { s with expr := .let name rhs body } =
      some (r.event, pushTrace { s with expr := body, env := r.env.extend name r.value, heap := r.heap } r.event) := by
  simp [step?]

/-- If-then-else with successful condition eval always steps. -/
@[simp]
theorem step?_if_ok (s : State) (cond : Trivial) (then_ else_ : Expr) (v : Flat.Value)
    (h : evalTrivial s.env cond = .ok v) :
    step? { s with expr := .if cond then_ else_ } =
      some (.silent, pushTrace { s with expr := if toBoolean v then then_ else else_ } .silent) := by
  simp [step?, h]

/-- If-then-else with failed condition eval produces an error. -/
@[simp]
theorem step?_if_error (s : State) (cond : Trivial) (then_ else_ : Expr) (msg : String)
    (h : evalTrivial s.env cond = .error msg) :
    step? { s with expr := .if cond then_ else_ } =
      some (.error msg, pushTrace { s with expr := .trivial .litUndefined } (.error msg)) := by
  simp [step?, h]

/-- Labeled expression always steps by unwrapping to body. -/
@[simp]
theorem step?_labeled (s : State) (label : String) (body : Expr) :
    step? { s with expr := .labeled label body } =
      some (.silent, pushTrace { s with expr := body } .silent) := by
  simp [step?]

/-- Break always steps with an error event. -/
@[simp]
theorem step?_break (s : State) (label : Option String) :
    step? { s with expr := .break label } =
      some (.error ("break:" ++ label.getD ""),
            pushTrace { s with expr := .trivial .litUndefined } (.error ("break:" ++ label.getD ""))) := by
  simp [step?]

/-- Continue always steps with an error event. -/
@[simp]
theorem step?_continue (s : State) (label : Option String) :
    step? { s with expr := .continue label } =
      some (.error ("continue:" ++ label.getD ""),
            pushTrace { s with expr := .trivial .litUndefined } (.error ("continue:" ++ label.getD ""))) := by
  simp [step?]

/-- Throw with successful eval always steps with an error event. -/
@[simp]
theorem step?_throw_ok (s : State) (arg : Trivial) (v : Flat.Value)
    (h : evalTrivial s.env arg = .ok v) :
    step? { s with expr := .throw arg } =
      some (.error "throw",
            pushTrace { s with expr := .trivial .litUndefined } (.error "throw")) := by
  simp [step?, h]

/-- Throw with failed eval always steps with an error event. -/
@[simp]
theorem step?_throw_error (s : State) (arg : Trivial) (msg : String)
    (h : evalTrivial s.env arg = .error msg) :
    step? { s with expr := .throw arg } =
      some (.error msg,
            pushTrace { s with expr := .trivial .litUndefined } (.error msg)) := by
  simp [step?, h]

/-- Return with no argument always steps. -/
@[simp]
theorem step?_return_none (s : State) :
    step? { s with expr := .return none } =
      some (.silent, pushTrace { s with expr := .trivial .litUndefined } .silent) := by
  simp [step?]

/-- Return with successful arg eval always steps. -/
@[simp]
theorem step?_return_some_ok (s : State) (t : Trivial) (v : Flat.Value)
    (h : evalTrivial s.env t = .ok v) :
    step? { s with expr := .return (some t) } =
      some (.silent, pushTrace { s with expr := .trivial (trivialOfValue v) } .silent) := by
  simp [step?, h]

/-- Return with failed arg eval produces an error. -/
@[simp]
theorem step?_return_some_error (s : State) (t : Trivial) (msg : String)
    (h : evalTrivial s.env t = .error msg) :
    step? { s with expr := .return (some t) } =
      some (.error msg,
            pushTrace { s with expr := .trivial .litUndefined } (.error msg)) := by
  simp [step?, h]

/-- Await with successful eval always steps. -/
@[simp]
theorem step?_await_ok (s : State) (arg : Trivial) (v : Flat.Value)
    (h : evalTrivial s.env arg = .ok v) :
    step? { s with expr := .await arg } =
      some (.silent, pushTrace { s with expr := .trivial (trivialOfValue v) } .silent) := by
  simp [step?, h]

/-- Await with failed eval produces an error. -/
@[simp]
theorem step?_await_error (s : State) (arg : Trivial) (msg : String)
    (h : evalTrivial s.env arg = .error msg) :
    step? { s with expr := .await arg } =
      some (.error msg,
            pushTrace { s with expr := .trivial .litUndefined } (.error msg)) := by
  simp [step?, h]

/-! ### Non-trivial expressions always step -/

/-- Let-binding expressions always step (step? ≠ none).
    Useful for proving halt contradictions: if an ANF state has a let-binding,
    it cannot be halted. -/
theorem step?_let_ne_none (s : State) (name : VarName) (rhs : ComplexExpr) (body : Expr) :
    step? { s with expr := .let name rhs body } ≠ none := by
  simp [step?]

/-- Labeled expressions always step. -/
theorem step?_labeled_ne_none (s : State) (label : String) (body : Expr) :
    step? { s with expr := .labeled label body } ≠ none := by
  simp [step?]

/-- Break always steps. -/
theorem step?_break_ne_none (s : State) (label : Option String) :
    step? { s with expr := .break label } ≠ none := by
  simp [step?]

/-- Continue always steps. -/
theorem step?_continue_ne_none (s : State) (label : Option String) :
    step? { s with expr := .continue label } ≠ none := by
  simp [step?]

/-- If-then-else always steps. -/
theorem step?_if_ne_none (s : State) (cond : Trivial) (then_ else_ : Expr) :
    step? { s with expr := .if cond then_ else_ } ≠ none := by
  simp [step?]
  cases evalTrivial s.env cond <;> simp

/-- Throw always steps. -/
theorem step?_throw_ne_none (s : State) (arg : Trivial) :
    step? { s with expr := .throw arg } ≠ none := by
  simp [step?]
  cases evalTrivial s.env arg <;> simp

/-- Return always steps. -/
theorem step?_return_ne_none (s : State) (arg : Option Trivial) :
    step? { s with expr := .return arg } ≠ none := by
  simp [step?]
  cases arg with
  | none => simp
  | some t =>
    intro h; cases h1 : evalTrivial s.env t <;> simp_all

/-- Await always steps. -/
theorem step?_await_ne_none (s : State) (arg : Trivial) :
    step? { s with expr := .await arg } ≠ none := by
  simp [step?]
  cases evalTrivial s.env arg <;> simp

/-- Yield always steps. -/
theorem step?_yield_ne_none (s : State) (arg : Option Trivial) (delegate : Bool) :
    step? { s with expr := .yield arg delegate } ≠ none := by
  simp [step?]
  cases arg with
  | none => simp
  | some t =>
    intro h; cases h1 : evalTrivial s.env t <;> simp_all

/-- While with a value condition always steps.
    Note: while_ with a non-value cond that can't step might NOT step. -/
theorem step?_while_value_ne_none (s : State) (cond : Expr) (body : Expr) (v : Flat.Value)
    (h : exprValue? cond = some v) :
    step? { s with expr := .while_ cond body } ≠ none := by
  unfold step?; simp only [h]; exact fun h => by simp at h

/-- Seq with a value first expression always steps. -/
theorem step?_seq_value_ne_none (s : State) (a b : Expr) (v : Flat.Value)
    (h : exprValue? a = some v) :
    step? { s with expr := .seq a b } ≠ none := by
  unfold step?; simp only [h]; exact fun h => by simp at h

/-- TryCatch with a value body always steps. -/
theorem step?_tryCatch_value_ne_none (s : State) (body : Expr) (catchParam : VarName)
    (catchBody : Expr) (finally_ : Option Expr) (v : Flat.Value)
    (h : exprValue? body = some v) :
    step? { s with expr := .tryCatch body catchParam catchBody finally_ } ≠ none := by
  unfold step?; simp only [h]; cases finally_ <;> exact fun h => by simp at h

/-- A trivial is a literal value (not a variable reference). -/
def Trivial.isLit : Trivial → Bool
  | .var _ => false
  | _ => true

/-- Literal trivials always have a value. -/
@[simp] theorem trivialValue?_isLit (t : Trivial) (h : t.isLit = true) :
    ∃ v, trivialValue? t = some v := by
  cases t <;> simp [Trivial.isLit, trivialValue?] at *

/-- Literal trivial expressions have values. -/
theorem exprValue?_trivial_lit (t : Trivial) (h : t.isLit = true) :
    ∃ v, exprValue? (.trivial t) = some v := by
  simp [exprValue?]; exact trivialValue?_isLit t h

/-- If step? returns none, the expression must be a literal trivial.
    This is the fundamental halting characterization for ANF:
    the only ANF states that cannot step are those with literal trivial expressions.
    Key lemma for anfConvert_halt_star non-lit cases.

    PROOF SKETCH (strong induction on expression depth):
    - Base cases: for `.trivial (.var name)`, step? always returns some
      (either looks up the variable or produces a ReferenceError). For all other
      `.trivial` constructors (litNull, litUndefined, etc.), step? returns none
      and these are the literal trivials we want.
    - Non-trivial, non-recursive: `.let`, `.if`, `.throw`, `.return`, `.yield`,
      `.await`, `.labeled`, `.break`, `.continue` always return some from step?.
    - Recursive cases (`.seq a b`, `.while_ cond body`, `.tryCatch`):
      step? returns none iff `exprValue? sub = none` AND `step? sub = none`.
      By IH (sub has smaller depth), sub is a literal trivial, so
      `exprValue? sub = trivialValue? t = some v`, contradiction. -/
theorem step?_none_implies_trivial_lit (s : State) (h : step? s = none) :
    ∃ t, s.expr = .trivial t ∧ t.isLit = true := by
  sorry

/-- Comprehensive: if an ANF expression is not a literal trivial (not .litNull,
    .litUndefined, .litBool, .litNum, .litStr, .litObject, .litClosure) but IS
    a variable, let, if, throw, return, await, yield, labeled, break, or continue,
    then step? ≠ none. For seq/while_/tryCatch, step? may return none if a
    sub-expression is stuck — those cases need separate handling.
    Key lemma for anfConvert_halt_star: halted ANF states must be literal trivials. -/
theorem step?_ne_none_of_var (s : State) (name : VarName) :
    step? { s with expr := .trivial (.var name) } ≠ none := by
  simp [step?]
  cases s.env.lookup name <;> simp

/-- Step relation is equivalent to step? returning some. -/
theorem Step_iff (s : State) (t : Core.TraceEvent) (s' : State) :
    Step s t s' ↔ step? s = some (t, s') :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- Steps.refl is the only way to produce an empty trace. -/
theorem Steps_nil_iff (s s' : State) :
    Steps s [] s' ↔ s = s' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ Steps.refl s⟩

/-! ## Structural theorems for ANF Step/Steps -/

/-- ANF.Step is deterministic. -/
theorem Step_deterministic {s : State} {t1 t2 : Core.TraceEvent} {s1 s2 : State} :
    Step s t1 s1 → Step s t2 s2 → t1 = t2 ∧ s1 = s2 := by
  intro ⟨h1⟩ ⟨h2⟩; rw [h1] at h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2; exact h2

/-- ANF.Steps is transitive. -/
theorem Steps_trans {s1 s2 s3 : State} {t1 t2 : List Core.TraceEvent} :
    Steps s1 t1 s2 → Steps s2 t2 s3 → Steps s1 (t1 ++ t2) s3 := by
  intro h1 h2
  induction h1 with
  | refl _ => exact h2
  | tail hstep _ ih => exact Steps.tail hstep (ih h2)

/-- If step? returns none, no Step can be taken. -/
theorem step?_none_no_step {s : State} (h : step? s = none) :
    ∀ t s', ¬ Step s t s' := by
  intro t s' ⟨hs⟩; rw [hs] at h; exact absurd h (by simp)

end VerifiedJS.ANF
