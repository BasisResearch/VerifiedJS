/-
  VerifiedJS — Flat IL Semantics
-/

import VerifiedJS.Flat.Syntax
import VerifiedJS.Core.Semantics

namespace VerifiedJS.Flat

/-- ECMA-262 §8.1 Environment Records (flattened lexical environment). -/
abbrev Env := List (VarName × Value)

/-- ECMA-262 §8.3 Execution Contexts (Flat machine state). -/
structure State where
  expr : Expr
  env : Env
  heap : Core.Heap
  trace : List Core.TraceEvent
  funcs : Array FuncDef := #[]
  /-- Call stack: saved caller environments for function call return. -/
  callStack : List Env := []
  deriving Repr

/-- Empty Flat lexical environment. -/
def Env.empty : Env := []

/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lexical lookup). -/
def Env.lookup (env : Env) (name : VarName) : Option Value :=
  match env.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

def updateBindingList (xs : Env) (name : VarName) (v : Value) : Env :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Value) : Env :=
  if env.any (fun kv => kv.fst == name) then
    updateBindingList env name v
  else
    (name, v) :: env

/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Value) : Env :=
  (name, v) :: env

/-- Check whether an expression is already a Flat value expression. -/
@[simp]
def exprValue? : Expr → Option Value
  | .lit v => some v
  | _ => none

/-- ECMA-262 §7.2.14 ToBoolean (Flat subset). -/
def toBoolean : Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .closure _ _ => true

/-- ECMA-262 §7.1.3 ToNumber (Flat subset — must match Core). -/
def toNumber : Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | .undefined => 0.0 / 0.0  -- NaN, matching Core
  | .string s =>
      let trimmed := s.trimAscii.toString
      if trimmed.isEmpty then 0.0
      else match trimmed.toNat? with
        | some n => Float.ofNat n
        | none =>
            if trimmed.startsWith "-" then
              match (trimmed.drop 1).toNat? with
              | some n => -(Float.ofNat n)
              | none => 0.0 / 0.0
            else 0.0 / 0.0
  | .object _ => 0.0 / 0.0
  | .closure _ _ => 0.0 / 0.0

/-- ECMA-262 §13.5 Runtime Semantics: Evaluation (Flat unary subset). -/
def evalUnary : Core.UnaryOp → Value → Value
  | .neg, v => .number (-toNumber v)
  | .pos, v => .number (toNumber v)
  | .logNot, v => .bool (!toBoolean v)
  | .void, _ => .undefined
  | .bitNot, v => .number (~~~(toNumber v |>.toUInt32)).toFloat

/-- ECMA-262 §7.1.12 ToString (Flat — must match Core.valueToString on convertValue). -/
def valueToString : Value → String
  | .string s => s
  | .number n =>
      if n.isNaN then "NaN"
      else if n == 1.0/0.0 then "Infinity"
      else if n == -1.0/0.0 then "-Infinity"
      else
        let i := n.toUInt64
        if i.toFloat == n && n >= 0.0 then toString i.toNat
        else
          let neg := -n
          let j := neg.toUInt64
          if j.toFloat == neg && neg > 0.0 then "-" ++ toString j.toNat
          else toString n
  | .bool true => "true"
  | .bool false => "false"
  | .null => "null"
  | .undefined => "undefined"
  | .object _ => "[object Object]"
  | .closure _ _ => "function"

/-- ECMA-262 §7.2.14 Abstract Equality Comparison (Flat — must match Core.abstractEq on convertValue). -/
def abstractEq : Value → Value → Bool
  | .null, .null => true
  | .undefined, .undefined => true
  | .null, .undefined => true
  | .undefined, .null => true
  | .bool a, .bool b => a == b
  | .number a, .number b => a == b
  | .string a, .string b => a == b
  | .object a, .object b => a == b
  | .closure a _, .closure b _ => a == b
  | .number a, .string b => a == toNumber (.string b)
  | .string a, .number b => toNumber (.string a) == b
  | .bool a, .number b => (toNumber (.bool a)) == b
  | .bool a, .string b => (toNumber (.bool a)) == (toNumber (.string b))
  | .number a, .bool b => a == (toNumber (.bool b))
  | .string a, .bool b => (toNumber (.string a)) == (toNumber (.bool b))
  | _, _ => false

/-- ECMA-262 §7.2.13 Abstract Relational Comparison (Flat — must match Core.abstractLt on convertValue). -/
def abstractLt : Value → Value → Bool
  | .string a, .string b => a < b
  | a, b => toNumber a < toNumber b

/-- ECMA-262 §13.15 Runtime Semantics: Evaluation (Flat binary subset — aligned with Core.evalBinary). -/
def evalBinary : Core.BinOp → Value → Value → Value
  | .add, .string a, .string b => .string (a ++ b)
  | .add, .string a, b => .string (a ++ valueToString b)
  | .add, a, .string b => .string (valueToString a ++ b)
  | .add, a, b => .number (toNumber a + toNumber b)
  | .sub, a, b => .number (toNumber a - toNumber b)
  | .mul, a, b => .number (toNumber a * toNumber b)
  | .div, a, b => .number (toNumber a / toNumber b)
  | .eq, a, b => .bool (abstractEq a b)
  | .neq, a, b => .bool (!abstractEq a b)
  | .strictEq, a, b => .bool (a == b)
  | .strictNeq, a, b => .bool (a != b)
  | .lt, a, b => .bool (abstractLt a b)
  | .gt, a, b => .bool (abstractLt b a)
  | .le, a, b => .bool (!abstractLt b a)
  | .ge, a, b => .bool (!abstractLt a b)
  | .logAnd, a, b => if toBoolean a then b else a
  | .logOr, a, b => if toBoolean a then a else b
  | .instanceof, .object _, .closure _ _ => .bool true
  | .instanceof, _, .closure _ _ => .bool false
  | .instanceof, _, _ => .bool false
  | .«in», .string _, .object _ => .bool true
  | .«in», _, _ => .bool false
  | .mod, a, b =>
      let na := toNumber a; let nb := toNumber b
      if nb == 0.0 then .number (0.0 / 0.0) else .number (na - nb * (na / nb).floor)
  | .exp, a, b => .number (Float.pow (toNumber a) (toNumber b))
  | .bitAnd, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia &&& ib).toFloat)
  | .bitOr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia ||| ib).toFloat)
  | .bitXor, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia ^^^ ib).toFloat)
  | .shl, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia <<< ib).toFloat)
  | .shr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia >>> ib).toFloat)
  | .ushr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia >>> ib).toFloat)

def pushTrace (s : State) (t : Core.TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

private def allocFreshObject (h : Core.Heap) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push [], nextAddr := addr + 1 }
  (addr, h')

@[simp] theorem allocFreshObject_fst (h : Core.Heap) :
    (allocFreshObject h).1 = h.nextAddr := rfl

@[simp] theorem allocFreshObject_objects_size (h : Core.Heap) :
    (allocFreshObject h).2.objects.size = h.objects.size + 1 := by
  simp [allocFreshObject, Array.size_push]

@[simp] theorem allocFreshObject_nextAddr (h : Core.Heap) :
    (allocFreshObject h).2.nextAddr = h.nextAddr + 1 := rfl

@[simp] theorem allocFreshObject_get_old (h : Core.Heap) (a : Nat) (ha : a < h.objects.size) :
    (allocFreshObject h).2.objects[a]? = h.objects[a]? := by
  simp only [allocFreshObject]
  rw [Array.getElem?_push]
  split
  · omega
  · rfl

@[simp] theorem allocFreshObject_get_new (h : Core.Heap) :
    (allocFreshObject h).2.objects[h.objects.size]? = some [] := by
  simp [allocFreshObject, Array.getElem?_push]

private def allocObjectWithProps (h : Core.Heap) (props : List (Core.PropName × Core.Value)) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push props, nextAddr := addr + 1 }
  (addr, h')

def flatToCoreValue : Value → Core.Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  -- Core heap payloads cannot encode Flat env pointers; keep callable identity only.
  | .closure funcIdx _ => .function funcIdx

def coreToFlatValue : Core.Value → Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  | .function idx => .closure idx 0

private def envSlotKey (idx : Nat) : PropName :=
  "__env" ++ toString idx

private def encodeEnvPropsAux (idx : Nat) (values : List Value) : List (PropName × Core.Value) :=
  match values with
  | [] => []
  | v :: rest => (envSlotKey idx, flatToCoreValue v) :: encodeEnvPropsAux (idx + 1) rest

private def encodeEnvProps (values : List Value) : List (PropName × Core.Value) :=
  encodeEnvPropsAux 0 values

private def allocEnvObject (h : Core.Heap) (values : List Value) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push (encodeEnvProps values), nextAddr := addr + 1 }
  (addr, h')

@[simp] theorem allocEnvObject_fst (h : Core.Heap) (vs : List Value) :
    (allocEnvObject h vs).1 = h.nextAddr := rfl

@[simp] theorem allocEnvObject_objects_size (h : Core.Heap) (vs : List Value) :
    (allocEnvObject h vs).2.objects.size = h.objects.size + 1 := by
  simp [allocEnvObject, Array.size_push]

@[simp] theorem allocEnvObject_nextAddr (h : Core.Heap) (vs : List Value) :
    (allocEnvObject h vs).2.nextAddr = h.nextAddr + 1 := rfl

@[simp] theorem allocEnvObject_get_old (h : Core.Heap) (vs : List Value) (a : Nat) (ha : a < h.objects.size) :
    (allocEnvObject h vs).2.objects[a]? = h.objects[a]? := by
  simp only [allocEnvObject]
  rw [Array.getElem?_push]
  split
  · omega
  · rfl

@[simp] theorem allocEnvObject_get_new (h : Core.Heap) (vs : List Value) :
    (allocEnvObject h vs).2.objects[h.objects.size]? = some (encodeEnvProps vs) := by
  simp [allocEnvObject, Array.getElem?_push]

def heapObjectAt? (h : Core.Heap) (addr : Nat) : Option (List (Core.PropName × Core.Value)) :=
  if hAddr : addr < h.objects.size then
    let _ := hAddr
    some (h.objects[addr]!)
  else
    none

-- Equation lemmas for coreToFlatValue
@[simp] theorem coreToFlatValue_null : coreToFlatValue .null = .null := rfl
@[simp] theorem coreToFlatValue_undefined : coreToFlatValue .undefined = .undefined := rfl
@[simp] theorem coreToFlatValue_bool (b : Bool) : coreToFlatValue (.bool b) = .bool b := rfl
@[simp] theorem coreToFlatValue_number (n : Float) : coreToFlatValue (.number n) = .number n := rfl
@[simp] theorem coreToFlatValue_string (s : String) : coreToFlatValue (.string s) = .string s := rfl
@[simp] theorem coreToFlatValue_object (addr : Nat) : coreToFlatValue (.object addr) = .object addr := rfl
@[simp] theorem coreToFlatValue_function (idx : Nat) : coreToFlatValue (.function idx) = .closure idx 0 := rfl

-- Equation lemmas for flatToCoreValue
@[simp] theorem flatToCoreValue_null : flatToCoreValue .null = .null := rfl
@[simp] theorem flatToCoreValue_undefined : flatToCoreValue .undefined = .undefined := rfl
@[simp] theorem flatToCoreValue_bool (b : Bool) : flatToCoreValue (.bool b) = .bool b := rfl
@[simp] theorem flatToCoreValue_number (n : Float) : flatToCoreValue (.number n) = .number n := rfl
@[simp] theorem flatToCoreValue_string (s : String) : flatToCoreValue (.string s) = .string s := rfl
@[simp] theorem flatToCoreValue_object (addr : Nat) : flatToCoreValue (.object addr) = .object addr := rfl
@[simp] theorem flatToCoreValue_closure (idx envPtr : Nat) : flatToCoreValue (.closure idx envPtr) = .function idx := rfl

/-- flatToCoreValue is a left inverse of coreToFlatValue on non-function values -/
theorem flatToCoreValue_coreToFlatValue_null : flatToCoreValue (coreToFlatValue .null) = .null := rfl
theorem flatToCoreValue_coreToFlatValue_undefined : flatToCoreValue (coreToFlatValue .undefined) = .undefined := rfl
theorem flatToCoreValue_coreToFlatValue_bool (b : Bool) : flatToCoreValue (coreToFlatValue (.bool b)) = .bool b := rfl
theorem flatToCoreValue_coreToFlatValue_number (n : Float) : flatToCoreValue (coreToFlatValue (.number n)) = .number n := rfl
theorem flatToCoreValue_coreToFlatValue_string (s : String) : flatToCoreValue (coreToFlatValue (.string s)) = .string s := rfl
theorem flatToCoreValue_coreToFlatValue_object (addr : Nat) : flatToCoreValue (coreToFlatValue (.object addr)) = .object addr := rfl

private def typeofValue : Value → Value
  | .undefined => .string "undefined"
  | .null => .string "object"
  | .bool _ => .string "boolean"
  | .number _ => .string "number"
  | .string _ => .string "string"
  | .object _ => .string "object"
  | .closure _ _ => .string "function"

def valuesFromExprList? : List Expr → Option (List Value)
  | [] => some []
  | e :: rest =>
      match exprValue? e, valuesFromExprList? rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-- One deterministic Flat small-step transition with emitted trace event. -/
def step? (s : State) : Option (Core.TraceEvent × State) :=
  match h : s.expr with
  | .lit _ => none
  | .var name =>
      match s.env.lookup name with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          let msg := "ReferenceError: " ++ name
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
  | .«let» name init body =>
      match exprValue? init with
      | some v =>
          let s' := pushTrace { s with expr := body, env := s.env.extend name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := init } with
          | some (t, si) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .«let» name si.expr body, env := si.env, heap := si.heap } t
                  some (t, s')
          | none => none
  | .assign name rhs =>
      match exprValue? rhs with
      | some v =>
          let s' := pushTrace { s with expr := .lit v, env := s.env.assign name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := rhs } with
          | some (t, sr) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sr.expr, env := sr.env, heap := sr.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .assign name sr.expr, env := sr.env, heap := sr.heap } t
                  some (t, s')
          | none => none
  | .«if» cond then_ else_ =>
      match exprValue? cond with
      | some v =>
          let next := if toBoolean v then then_ else else_
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := cond } with
          | some (t, sc) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sc.expr, env := sc.env, heap := sc.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .«if» sc.expr then_ else_, env := sc.env, heap := sc.heap } t
                  some (t, s')
          | none => none
  | .seq a b =>
      match exprValue? a with
      | some _ =>
          let s' := pushTrace { s with expr := b } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := a } with
          | some (t, sa) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .seq sa.expr b, env := sa.env, heap := sa.heap } t
                  some (t, s')
          | none => none
  | .unary op arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit (evalUnary op v) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .unary op sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
          | none => none
  | .binary op lhs rhs =>
      match exprValue? lhs with
      | none =>
          match step? { s with expr := lhs } with
          | some (t, sl) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sl.expr, env := sl.env, heap := sl.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .binary op sl.expr rhs, env := sl.env, heap := sl.heap } t
                  some (t, s')
          | none => none
      | some lv =>
          match exprValue? rhs with
          | none =>
              match step? { s with expr := rhs } with
              | some (t, sr) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := sr.expr, env := sr.env, heap := sr.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .binary op (.lit lv) sr.expr, env := sr.env, heap := sr.heap } t
                      some (t, s')
              | none => none
          | some rv =>
              let s' := pushTrace { s with expr := .lit (evalBinary op lv rv) } .silent
              some (.silent, s')
  | .while_ cond body =>
      let lowered := .«if» cond (.seq body (.while_ cond body)) (.lit .undefined)
      let s' := pushTrace { s with expr := lowered } .silent
      some (.silent, s')
  | .call funcExpr envExpr args =>
      match exprValue? funcExpr with
      | none =>
          match step? { s with expr := funcExpr } with
          | some (t, sf) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sf.expr, env := sf.env, heap := sf.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace
                    { s with expr := .call sf.expr envExpr args, env := sf.env, heap := sf.heap } t
                  some (t, s')
          | none => none
      | some _ =>
          match exprValue? envExpr with
          | none =>
              match step? { s with expr := envExpr } with
              | some (t, se) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .call funcExpr se.expr args, env := se.env, heap := se.heap } t
                      some (t, s')
              | none => none
          | some envVal =>
              match valuesFromExprList? args with
              | some argVals =>
                  -- WASMCERT: theories/opsem.v — function call with all values
                  -- All arguments evaluated; perform the actual call.
                  match exprValue? funcExpr with
                  | some (.closure funcIdx _envPtr) =>
                      -- §18.2 Built-in: console.log (reserved at function index 0).
                      if funcIdx == Core.consoleLogIdx then
                          let msg := match argVals with
                            | [v] => valueToString v
                            | vs => String.intercalate " " (vs.map valueToString)
                          let s' := pushTrace { s with expr := .lit .undefined } (.log msg)
                          some (.log msg, s')
                      else
                      match s.funcs[funcIdx]? with
                      | some funcDef =>
                          -- §10.2.1 [[Call]]: bind params to args, bind envParam.
                          let pairs := funcDef.params.zip argVals
                          let bodyEnv : Env :=
                            pairs.foldr (fun pv bs => (pv.1, pv.2) :: bs) []
                          -- Bind the environment pointer for captured variable access.
                          let bodyEnv' : Env := (funcDef.envParam, envVal) :: bodyEnv
                          -- Bind function name for recursion.
                          let bodyEnv'' : Env := (funcDef.name, .closure funcIdx (match envVal with | .object p => p | _ => 0)) :: bodyEnv'
                          -- Wrap body in tryCatch to intercept returns.
                          let wrapped := .tryCatch funcDef.body "__call_frame_return__"
                            (.var "__call_frame_return__") none
                          -- Push caller env onto call stack for restoration on return.
                          let s' := pushTrace { s with
                            expr := wrapped
                            env := bodyEnv''
                            callStack := s.env :: s.callStack } .silent
                          some (.silent, s')
                      | none =>
                          let s' := pushTrace { s with expr := .lit .undefined } .silent
                          some (.silent, s')
                  | _ =>
                      -- Non-closure callee: return undefined.
                      let s' := pushTrace { s with expr := .lit .undefined } .silent
                      some (.silent, s')
              | none =>
                  match hf : firstNonValueExpr args with
                  | some (done, target, remaining) =>
                      have : Expr.depth target < Expr.depth s.expr := by
                        rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
                      match step? { s with expr := target } with
                      | some (t, sa) =>
                          match t with
                          | .error _ =>
                              let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                              some (t, s')
                          | _ =>
                              let s' := pushTrace
                                { s with expr := .call funcExpr envExpr (done ++ [sa.expr] ++ remaining), env := sa.env, heap := sa.heap } t
                              some (t, s')
                      | none => none
                  | none => none
  | .newObj funcExpr envExpr args =>
      match exprValue? funcExpr with
      | none =>
          match step? { s with expr := funcExpr } with
          | some (t, sf) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sf.expr, env := sf.env, heap := sf.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace
                    { s with expr := .newObj sf.expr envExpr args, env := sf.env, heap := sf.heap } t
                  some (t, s')
          | none => none
      | some _ =>
          match exprValue? envExpr with
          | none =>
              match step? { s with expr := envExpr } with
              | some (t, se) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .newObj funcExpr se.expr args, env := se.env, heap := se.heap } t
                      some (t, s')
              | none => none
          | some _ =>
              match valuesFromExprList? args with
              | some _ =>
                  let (addr, heap') := allocFreshObject s.heap
                  let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
                  some (.silent, s')
              | none =>
                  match hf : firstNonValueExpr args with
                  | some (done, target, remaining) =>
                      have : Expr.depth target < Expr.depth s.expr := by
                        rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
                      match step? { s with expr := target } with
                      | some (t, sa) =>
                          match t with
                          | .error _ =>
                              let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                              some (t, s')
                          | _ =>
                              let s' := pushTrace
                                { s with expr := .newObj funcExpr envExpr (done ++ [sa.expr] ++ remaining), env := sa.env, heap := sa.heap } t
                              some (t, s')
                      | none => none
                  | none => none
  | .getProp obj prop =>
      match exprValue? obj with
      | some (.object addr) =>
          -- ECMA-262 §9.1.8 [[Get]]: look up property on heap object.
          let v := match heapObjectAt? s.heap addr with
            | some props =>
                match props.find? (fun kv => kv.fst == prop) with
                | some (_, cv) => coreToFlatValue cv
                | none =>
                    if prop == "length" then .number (Float.ofNat props.length)
                    else .undefined
            | none => .undefined
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | some (.string str) =>
          -- ECMA-262 §21.1.3.3 String.prototype.length.
          let v := if prop == "length" then .number (Float.ofNat str.length)
                   else .undefined
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .getProp so.expr prop, env := so.env, heap := so.heap } t
                  some (t, s')
          | none => none
  | .setProp obj prop value =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .setProp so.expr prop value, env := so.env, heap := so.heap } t
                  some (t, s')
          | none => none
      | some (.object addr) =>
          match exprValue? value with
          | some v =>
              -- ECMA-262 §9.1.9 [[Set]]: update or add property on heap object.
              let cv := flatToCoreValue v
              let heap' := match heapObjectAt? s.heap addr with
                | some props =>
                    let updated := if props.any (fun kv => kv.fst == prop)
                      then props.map (fun kv => if kv.fst == prop then (prop, cv) else kv)
                      else props ++ [(prop, cv)]
                    { s.heap with objects := s.heap.objects.set! addr updated }
                | none => s.heap
              let s' := pushTrace { s with expr := .lit v, heap := heap' } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := value } with
              | some (t, sv) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := sv.expr, env := sv.env, heap := sv.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .setProp obj prop sv.expr, env := sv.env, heap := sv.heap } t
                      some (t, s')
              | none => none
      | some _ =>
          -- Property set on non-object: silently return value.
          match exprValue? value with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := value } with
              | some (t, sv) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := sv.expr, env := sv.env, heap := sv.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .setProp obj prop sv.expr, env := sv.env, heap := sv.heap } t
                      some (t, s')
              | none => none
  | .getIndex obj idx =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .getIndex so.expr idx, env := so.env, heap := so.heap } t
                  some (t, s')
          | none => none
      | some (.object addr) =>
          match exprValue? idx with
          | some idxVal =>
              -- ECMA-262 §9.1.8 [[Get]] with computed key.
              let propName := valueToString idxVal
              let v := match heapObjectAt? s.heap addr with
                | some props =>
                    match props.find? (fun kv => kv.fst == propName) with
                    | some (_, cv) => coreToFlatValue cv
                    | none =>
                        if propName == "length" then .number (Float.ofNat props.length)
                        else .undefined
                | none => .undefined
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := idx } with
              | some (t, si) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace { s with expr := .getIndex obj si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
              | none => none
      | some (.string str) =>
          match exprValue? idx with
          | some idxVal =>
              let propName := valueToString idxVal
              let v := match idxVal with
                | .number n =>
                    let idx := n.toUInt64.toNat
                    if n >= 0.0 && n.toUInt64.toFloat == n && idx < str.length
                    then .string (String.Pos.Raw.get str ⟨idx⟩ |>.toString)
                    else if propName == "length" then .number (Float.ofNat str.length)
                    else .undefined
                | _ =>
                    if propName == "length" then .number (Float.ofNat str.length)
                    else .undefined
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := idx } with
              | some (t, si) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace { s with expr := .getIndex obj si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
              | none => none
      | some _ =>
          match exprValue? idx with
          | some _ =>
              let s' := pushTrace { s with expr := .lit .undefined } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := idx } with
              | some (t, si) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace { s with expr := .getIndex obj si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
              | none => none
  | .setIndex obj idx value =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .setIndex so.expr idx value, env := so.env, heap := so.heap } t
                  some (t, s')
          | none => none
      | some (.object addr) =>
          match exprValue? idx with
          | none =>
              match step? { s with expr := idx } with
              | some (t, si) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .setIndex obj si.expr value, env := si.env, heap := si.heap } t
                      some (t, s')
              | none => none
          | some idxVal =>
              match exprValue? value with
              | some v =>
                  -- ECMA-262 §9.1.9 [[Set]] with computed key.
                  let propName := valueToString idxVal
                  let cv := flatToCoreValue v
                  let heap' := match heapObjectAt? s.heap addr with
                    | some props =>
                        let updated := if props.any (fun kv => kv.fst == propName)
                          then props.map (fun kv => if kv.fst == propName then (propName, cv) else kv)
                          else props ++ [(propName, cv)]
                        { s.heap with objects := s.heap.objects.set! addr updated }
                    | none => s.heap
                  let s' := pushTrace { s with expr := .lit v, heap := heap' } .silent
                  some (.silent, s')
              | none =>
                  match step? { s with expr := value } with
                  | some (t, sv) =>
                      match t with
                      | .error _ =>
                          let s' := pushTrace { s with expr := sv.expr, env := sv.env, heap := sv.heap } t
                          some (t, s')
                      | _ =>
                          let s' := pushTrace
                            { s with expr := .setIndex obj idx sv.expr, env := sv.env, heap := sv.heap } t
                          some (t, s')
                  | none => none
      | some _ =>
          -- setIndex on non-object: silently return value.
          match exprValue? idx with
          | none =>
              match step? { s with expr := idx } with
              | some (t, si) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := si.expr, env := si.env, heap := si.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .setIndex obj si.expr value, env := si.env, heap := si.heap } t
                      some (t, s')
              | none => none
          | some _ =>
              match exprValue? value with
              | some v =>
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
              | none =>
                  match step? { s with expr := value } with
                  | some (t, sv) =>
                      match t with
                      | .error _ =>
                          let s' := pushTrace { s with expr := sv.expr, env := sv.env, heap := sv.heap } t
                          some (t, s')
                      | _ =>
                          let s' := pushTrace
                            { s with expr := .setIndex obj idx sv.expr, env := sv.env, heap := sv.heap } t
                          some (t, s')
                  | none => none
  | .deleteProp obj prop =>
      match exprValue? obj with
      | some (.object addr) =>
          -- ECMA-262 §12.4.3 delete: remove property from heap object.
          let heap' := match heapObjectAt? s.heap addr with
            | some props =>
                let filtered := props.filter (fun kv => kv.fst != prop)
                { s.heap with objects := s.heap.objects.set! addr filtered }
            | none => s.heap
          let s' := pushTrace { s with expr := .lit (.bool true), heap := heap' } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit (.bool true) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .deleteProp so.expr prop, env := so.env, heap := so.heap } t
                  some (t, s')
          | none => none
  | .typeof arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit (typeofValue v) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .typeof sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
          | none => none
  | .labeled _ body =>
      let s' := pushTrace { s with expr := body } .silent
      some (.silent, s')
  | .throw arg =>
      match exprValue? arg with
      | some v =>
          let msg := valueToString v
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .throw sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
          | none => none
  | .this =>
      match s.env.lookup "this" with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  | .makeClosure idx envExpr =>
      match exprValue? envExpr with
      | some (.object envPtr) =>
          let s' := pushTrace { s with expr := .lit (.closure idx envPtr) } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: invalid closure environment")
          some (.error "TypeError: invalid closure environment", s')
      | none =>
          match step? { s with expr := envExpr } with
          | some (t, se) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .makeClosure idx se.expr, env := se.env, heap := se.heap } t
                  some (t, s')
          | none => none
  | .getEnv envExpr idx =>
      match exprValue? envExpr with
      | some (.object envPtr) =>
          match heapObjectAt? s.heap envPtr with
          | some props =>
              let key := envSlotKey idx
              match props.find? (fun kv => kv.fst == key) with
              | some kv =>
                  let s' := pushTrace { s with expr := .lit (coreToFlatValue kv.snd) } .silent
                  some (.silent, s')
              | none =>
                  let msg := "ReferenceError: missing env slot " ++ key
                  let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
                  some (.error msg, s')
          | none =>
              let msg := "TypeError: dangling env pointer " ++ toString envPtr
              let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
              some (.error msg, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "TypeError: invalid env pointer")
          some (.error "TypeError: invalid env pointer", s')
      | none =>
          match step? { s with expr := envExpr } with
          | some (t, se) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .getEnv se.expr idx, env := se.env, heap := se.heap } t
                  some (t, s')
          | none => none
  | .makeEnv values =>
      match valuesFromExprList? values with
      | some captured =>
          let (addr, heap') := allocEnvObject s.heap captured
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
      | none =>
          match hf : firstNonValueExpr values with
          | some (done, target, remaining) =>
              have : Expr.depth target < Expr.depth s.expr := by
                rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
              match step? { s with expr := target } with
              | some (t, se) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace { s with expr := .makeEnv (done ++ [se.expr] ++ remaining), env := se.env, heap := se.heap } t
                      some (t, s')
              | none => none
          | none => none
  | .objectLit props =>
      let vals := props.map Prod.snd
      match valuesFromExprList? vals with
      | some _ =>
          let heapProps := props.filterMap fun (k, e) =>
            match exprValue? e with | some v => some (k, flatToCoreValue v) | none => none
          let (addr, heap') := allocObjectWithProps s.heap heapProps
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
      | none =>
          match hf : firstNonValueProp props with
          | some (done, propName, target, remaining) =>
              have : Expr.depth target < Expr.depth s.expr := by
                rw [h]; simp [Expr.depth]; have := firstNonValueProp_depth hf; omega
              match step? { s with expr := target } with
              | some (t, se) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace { s with expr := .objectLit (done ++ [(propName, se.expr)] ++ remaining), env := se.env, heap := se.heap } t
                      some (t, s')
              | none => none
          | none => none
  | .arrayLit elems =>
      match valuesFromExprList? elems with
      | some _ =>
          let heapProps : List (Core.PropName × Core.Value) := elems.zipIdx.filterMap fun (e, i) =>
            match exprValue? e with | some v => some (toString i, flatToCoreValue v) | none => none
          let (addr, heap') := allocObjectWithProps s.heap heapProps
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
      | none =>
          match hf : firstNonValueExpr elems with
          | some (done, target, remaining) =>
              have : Expr.depth target < Expr.depth s.expr := by
                rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
              match step? { s with expr := target } with
              | some (t, se) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace { s with expr := .arrayLit (done ++ [se.expr] ++ remaining), env := se.env, heap := se.heap } t
                      some (t, s')
              | none => none
          | none => none
  | .tryCatch body catchParam catchBody finally_ =>
      let isCallFrame := catchParam == "__call_frame_return__"
      match exprValue? body with
      | some v =>
          if isCallFrame then
              -- Function normal completion: restore caller env from callStack.
              let restoredEnv : Env := match s.callStack with
                | saved :: _ => saved
                | [] => s.env
              let newStack := match s.callStack with
                | _ :: rest => rest
                | [] => []
              let s' := pushTrace { s with expr := .lit v, env := restoredEnv, callStack := newStack } .silent
              some (.silent, s')
          else
          match finally_ with
          | some fin =>
              let s' := pushTrace { s with expr := .seq fin (.lit v) } .silent
              some (.silent, s')
          | none =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
      | none =>
          match step? { s with expr := body } with
          | some (.error msg, sb) =>
              if isCallFrame && msg.startsWith "return:" then
                  -- Function return: extract value from sb.expr, restore caller env.
                  let retVal := match exprValue? sb.expr with
                    | some v => v
                    | none => .undefined
                  let restoredEnv : Env := match s.callStack with
                    | saved :: _ => saved
                    | [] => sb.env
                  let newStack := match s.callStack with
                    | _ :: rest => rest
                    | [] => []
                  let s' := pushTrace
                    { s with expr := .lit retVal, env := restoredEnv
                           , heap := sb.heap
                           , callStack := newStack } .silent
                  some (.silent, s')
              else if isCallFrame then
                  -- Function threw: propagate error, restore caller env.
                  let restoredEnv : Env := match s.callStack with
                    | saved :: _ => saved
                    | [] => sb.env
                  let newStack := match s.callStack with
                    | _ :: rest => rest
                    | [] => []
                  let s' := pushTrace
                    { s with expr := .lit .undefined, env := restoredEnv
                           , heap := sb.heap
                           , callStack := newStack } (.error msg)
                  some (.error msg, s')
              else
              let handler :=
                match finally_ with
                | some fin => .seq catchBody fin
                | none => catchBody
              let s' := pushTrace
                { s with expr := handler, env := sb.env.extend catchParam (.string msg), heap := sb.heap } (.error msg)
              some (.error msg, s')
          | some (t, sb) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sb.expr, env := sb.env, heap := sb.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace
                    { s with expr := .tryCatch sb.expr catchParam catchBody finally_, env := sb.env, heap := sb.heap } t
                  some (t, s')
          | none => none
  | .«break» label =>
      let l := label.getD ""
      let msg := "break:" ++ l
      let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
      some (.error msg, s')
  | .«continue» label =>
      let l := label.getD ""
      let msg := "continue:" ++ l
      let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
      some (.error msg, s')
  | .«return» arg =>
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "return:undefined")
          some (.error "return:undefined", s')
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } (.error ("return:" ++ valueToString v))
              some (.error ("return:" ++ valueToString v), s')
          | none =>
              match step? { s with expr := e } with
              | some (t, se) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace { s with expr := .«return» (some se.expr), env := se.env, heap := se.heap } t
                      some (t, s')
              | none => none
  | .yield arg delegate =>
      match arg with
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := e } with
              | some (t, se) =>
                  match t with
                  | .error _ =>
                      let s' := pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t
                      some (t, s')
                  | _ =>
                      let s' := pushTrace
                        { s with expr := .yield (some se.expr) delegate, env := se.env, heap := se.heap } t
                      some (t, s')
              | none => none
  | .await arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              match t with
              | .error _ =>
                  let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
              | _ =>
                  let s' := pushTrace { s with expr := .await sa.expr, env := sa.env, heap := sa.heap } t
                  some (t, s')
          | none => none
  termination_by s.expr.depth
  decreasing_by all_goals (try cases ‹Option Expr›) <;> simp_all [Expr.depth] <;> omega

/-- Small-step relation induced by `step?`.
    ECMA-262 §8.3 execution context stepping. -/
inductive Step : State → Core.TraceEvent → State → Prop where
  | mk {s : State} {t : Core.TraceEvent} {s' : State} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of Flat steps with trace accumulation. -/
inductive Steps : State → List Core.TraceEvent → State → Prop where
  | refl (s : State) : Steps s [] s
  | tail {s1 s2 s3 : State} {t : Core.TraceEvent} {ts : List Core.TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Initial Flat machine state for a program entry expression. -/
def initialState (p : Program) : State :=
  let consoleProps : List (Core.PropName × Core.Value) := [("log", .function Core.consoleLogIdx)]
  let heap : Core.Heap := { objects := #[consoleProps], nextAddr := 1 }
  { expr := p.main, env := Env.empty.extend "console" (.object 0), heap := heap, trace := []
  , funcs := p.functions, callStack := [] }

/-- Behavioral semantics -/
def Behaves (p : Program) (b : List Core.TraceEvent) : Prop :=
  ∃ s', Steps (initialState p) b s' ∧ step? s' = none

/-- Flat literal expressions are final values and do not step. -/
@[simp]
theorem step?_lit_none (s : State) (v : Value) :
    step? { s with expr := .lit v } = none := by
  simp [step?]

/-- Variable lookup that succeeds. -/
@[simp]
theorem step?_var_found (s : State) (name : VarName) (v : Value)
    (h : s.env.lookup name = some v) :
    step? { s with expr := .var name } =
      some (.silent, pushTrace { s with expr := .lit v } .silent) := by
  simp [step?, h]

/-- Variable lookup that fails. -/
@[simp]
theorem step?_var_not_found (s : State) (name : VarName)
    (h : s.env.lookup name = none) :
    step? { s with expr := .var name } =
      some (.error ("ReferenceError: " ++ name),
            pushTrace { s with expr := .lit .undefined } (.error ("ReferenceError: " ++ name))) := by
  simp [step?, h]

/-- Let-binding where init is already a value. -/
@[simp]
theorem step?_let_value (s : State) (name : VarName) (v : Value) (body : Expr) :
    step? { s with expr := .«let» name (.lit v) body } =
      some (.silent, pushTrace { s with expr := body, env := s.env.extend name v } .silent) := by
  simp [step?, exprValue?]

/-- Seq where first expression is already a value: skip to the second. -/
@[simp]
theorem step?_seq_value (s : State) (v : Value) (b : Expr) :
    step? { s with expr := .seq (.lit v) b } =
      some (.silent, pushTrace { s with expr := b } .silent) := by
  simp [step?, exprValue?]

/-- If with a true-ish condition value: takes the then branch. -/
@[simp]
theorem step?_if_true (s : State) (v : Value) (then_ else_ : Expr)
    (h : toBoolean v = true) :
    step? { s with expr := .«if» (.lit v) then_ else_ } =
      some (.silent, pushTrace { s with expr := then_ } .silent) := by
  simp [step?, exprValue?, h]

/-- If with a false-ish condition value: takes the else branch. -/
@[simp]
theorem step?_if_false (s : State) (v : Value) (then_ else_ : Expr)
    (h : toBoolean v = false) :
    step? { s with expr := .«if» (.lit v) then_ else_ } =
      some (.silent, pushTrace { s with expr := else_ } .silent) := by
  simp [step?, exprValue?, h]

/-- Unary op on a value. -/
@[simp]
theorem step?_unary_value (s : State) (op : Core.UnaryOp) (v : Value) :
    step? { s with expr := .unary op (.lit v) } =
      some (.silent, pushTrace { s with expr := .lit (evalUnary op v) } .silent) := by
  simp [step?, exprValue?]

/-- Binary op on two values. -/
@[simp]
theorem step?_binary_values (s : State) (op : Core.BinOp) (lv rv : Value) :
    step? { s with expr := .binary op (.lit lv) (.lit rv) } =
      some (.silent, pushTrace { s with expr := .lit (evalBinary op lv rv) } .silent) := by
  simp [step?, exprValue?]

/-- valuesFromExprList? on a list of literals returns the values. -/
@[simp] theorem valuesFromExprList?_map_lit (vs : List Value) :
    valuesFromExprList? (vs.map (fun v => Expr.lit v)) = some vs := by
  induction vs with
  | nil => simp [valuesFromExprList?]
  | cons v rest ih => simp [valuesFromExprList?, exprValue?, ih]

/-- Call with closure value, env value, all arg values, valid funcIdx, non-consoleLog.
    This is the main call step: lookup function, bind params, enter body. -/
theorem step?_call_closure (s : State)
    (funcIdx : Nat) (envPtr : Nat) (envVal : Value) (argVals : List Value)
    (funcDef : FuncDef)
    (hfuncIdx : funcIdx ≠ Core.consoleLogIdx)
    (hfunc : s.funcs[funcIdx]? = some funcDef) :
    step? { s with expr := .call (.lit (.closure funcIdx envPtr)) (.lit envVal)
                     (argVals.map (fun v => Expr.lit v)) } =
      let pairs := funcDef.params.zip argVals
      let bodyEnv := pairs.foldr (fun pv bs => (pv.1, pv.2) :: bs) []
      let bodyEnv' := (funcDef.envParam, envVal) :: bodyEnv
      let bodyEnv'' := (funcDef.name, .closure funcIdx (match envVal with | .object p => p | _ => 0)) :: bodyEnv'
      let wrapped := .tryCatch funcDef.body "__call_frame_return__"
        (.var "__call_frame_return__") none
      some (.silent, pushTrace { s with
        expr := wrapped
        env := bodyEnv''
        callStack := s.env :: s.callStack } .silent) := by
  simp [step?, exprValue?, hfuncIdx, hfunc, valuesFromExprList?_map_lit]

/-- Call with closure value, env value, all arg values, consoleLog. -/
theorem step?_call_consoleLog (s : State)
    (envPtr : Nat) (envVal : Value) (argVals : List Value) :
    step? { s with expr := .call (.lit (.closure Core.consoleLogIdx envPtr)) (.lit envVal)
                     (argVals.map (fun v => Expr.lit v)) } =
      let msg := match argVals with
        | [v] => valueToString v
        | vs => String.intercalate " " (vs.map valueToString)
      some (.log msg, pushTrace { s with expr := .lit .undefined } (.log msg)) := by
  simp [step?, exprValue?, Core.consoleLogIdx, valuesFromExprList?_map_lit]

/-- Stepping a call when funcExpr is not a value: recurse into funcExpr. -/
@[simp] theorem step?_call_step_func (s : State) (f envE : Expr) (args : List Expr)
    (hf : exprValue? f = none) :
    step? { s with expr := .call f envE args } =
      (step? { s with expr := f }).bind fun (t, sf) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := sf.expr, env := sf.env, heap := sf.heap } t)
        | _ => some (t, pushTrace { s with expr := .call sf.expr envE args, env := sf.env, heap := sf.heap } t) := by
  rw [step?.eq_1]; simp only [hf]; cases step? { s with expr := f } <;> rfl

/-- Stepping a call when funcExpr is a value but envExpr is not: recurse into envExpr. -/
@[simp] theorem step?_call_step_env (s : State) (f envE : Expr) (args : List Expr)
    (fv : Value) (hf : exprValue? f = some fv) (he : exprValue? envE = none) :
    step? { s with expr := .call f envE args } =
      (step? { s with expr := envE }).bind fun (t, se) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t)
        | _ => some (t, pushTrace { s with expr := .call f se.expr args, env := se.env, heap := se.heap } t) := by
  rw [step?.eq_1]; simp only [hf, he]; cases step? { s with expr := envE } <;> rfl

/-- Stepping a newObj when funcExpr is not a value: recurse into funcExpr. -/
@[simp] theorem step?_newObj_step_func (s : State) (f envE : Expr) (args : List Expr)
    (hf : exprValue? f = none) :
    step? { s with expr := .newObj f envE args } =
      (step? { s with expr := f }).bind fun (t, sf) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := sf.expr, env := sf.env, heap := sf.heap } t)
        | _ => some (t, pushTrace { s with expr := .newObj sf.expr envE args, env := sf.env, heap := sf.heap } t) := by
  rw [step?.eq_1]; simp only [hf]; cases step? { s with expr := f } <;> rfl

/-- Stepping a newObj when funcExpr is a value but envExpr is not: recurse into envExpr. -/
theorem step?_newObj_step_env (s : State) (f envE : Expr) (args : List Expr)
    (fv : Value) (hf : exprValue? f = some fv) (he : exprValue? envE = none) :
    step? { s with expr := .newObj f envE args } =
      (step? { s with expr := envE }).bind fun (t, se) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t)
        | _ => some (t, pushTrace { s with expr := .newObj f se.expr args, env := se.env, heap := se.heap } t) := by
  rw [step?.eq_1]; simp only [hf, he]; cases step? { s with expr := envE } <;> rfl

/-- Stepping a getEnv when envExpr is not a value: recurse into envExpr. -/
@[simp] theorem step?_getEnv_step_env (s : State) (envE : Expr) (idx : Nat)
    (he : exprValue? envE = none) :
    step? { s with expr := .getEnv envE idx } =
      (step? { s with expr := envE }).bind fun (t, se) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := se.expr, env := se.env, heap := se.heap } t)
        | _ => some (t, pushTrace { s with expr := .getEnv se.expr idx, env := se.env, heap := se.heap } t) := by
  rw [step?.eq_1]; simp only [he]; cases step? { s with expr := envE } <;> rfl

/-- Stepping getProp when obj is not a value: recurse into obj. -/
@[simp] theorem step?_getProp_step_obj (s : State) (obj : Expr) (prop : PropName)
    (ho : exprValue? obj = none) :
    step? { s with expr := .getProp obj prop } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t)
        | _ => some (t, pushTrace { s with expr := .getProp so.expr prop, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping setProp when obj is not a value: recurse into obj. -/
@[simp] theorem step?_setProp_step_obj (s : State) (obj : Expr) (prop : PropName) (val : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .setProp obj prop val } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t)
        | _ => some (t, pushTrace { s with expr := .setProp so.expr prop val, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping getIndex when obj is not a value: recurse into obj. -/
@[simp] theorem step?_getIndex_step_obj (s : State) (obj idx : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .getIndex obj idx } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t)
        | _ => some (t, pushTrace { s with expr := .getIndex so.expr idx, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping setIndex when obj is not a value: recurse into obj. -/
@[simp] theorem step?_setIndex_step_obj (s : State) (obj idx val : Expr)
    (ho : exprValue? obj = none) :
    step? { s with expr := .setIndex obj idx val } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t)
        | _ => some (t, pushTrace { s with expr := .setIndex so.expr idx val, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl

/-- Stepping deleteProp when obj is not a value: recurse into obj. -/
@[simp] theorem step?_deleteProp_step_obj (s : State) (obj : Expr) (prop : PropName)
    (ho : exprValue? obj = none) :
    step? { s with expr := .deleteProp obj prop } =
      (step? { s with expr := obj }).bind fun (t, so) =>
        match t with
        | .error _ => some (t, pushTrace { s with expr := so.expr, env := so.env, heap := so.heap } t)
        | _ => some (t, pushTrace { s with expr := .deleteProp so.expr prop, env := so.env, heap := so.heap } t) := by
  rw [step?.eq_1]; simp only [ho]; cases step? { s with expr := obj } <;> rfl


/-- Step relation is equivalent to step? returning some. -/
theorem Step_iff (s : State) (t : Core.TraceEvent) (s' : State) :
    Step s t s' ↔ step? s = some (t, s') :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- Steps.refl is the only way to produce an empty trace. -/
theorem Steps_nil_iff (s s' : State) :
    Steps s [] s' ↔ s = s' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ Steps.refl s⟩

/-! ## Structural theorems for Flat Step/Steps -/

/-- Flat.Step is deterministic. -/
theorem Step_deterministic {s : State} {t1 t2 : Core.TraceEvent} {s1 s2 : State} :
    Step s t1 s1 → Step s t2 s2 → t1 = t2 ∧ s1 = s2 := by
  intro ⟨h1⟩ ⟨h2⟩; rw [h1] at h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2; exact h2

/-- Flat.Steps is transitive. -/
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

/-- A literal value halts (step? returns none). -/
theorem step?_value_halts (s : State) (v : Value) :
    step? { s with expr := .lit v } = none := by
  simp

/-- `.var name` always steps (either found or not found). -/
theorem step?_var_isSome (s : State) (name : VarName) :
    (step? { s with expr := .var name }).isSome = true := by
  cases h : s.env.lookup name <;> simp [step?, h]

/-- `.this` always steps (resolves `this` binding or defaults to undefined). -/
theorem step?_this_isSome (s : State) :
    (step? { s with expr := .this }).isSome = true := by
  cases h : s.env.lookup "this" <;> simp [step?, h]

/-- `.this` result when binding exists. -/
theorem step?_this_found (s : State) (v : Value)
    (h : s.env.lookup "this" = some v) :
    step? { s with expr := .this } =
      some (.silent, pushTrace { s with expr := .lit v } .silent) := by
  simp [step?, h]

/-- `.this` result when no binding. -/
theorem step?_this_not_found (s : State)
    (h : s.env.lookup "this" = none) :
    step? { s with expr := .this } =
      some (.silent, pushTrace { s with expr := .lit .undefined } .silent) := by
  simp [step?, h]

/-- `.seq a b` steps when `a` is not a value but steps.
    REF: WasmCert-Coq reduction under evaluation context. -/
theorem step?_seq_sub_step (s : State) (a b : Expr)
    (hnotval : exprValue? a = none)
    (hstep : ∃ t sa, step? { s with expr := a } = some (t, sa)) :
    ∃ t s', step? { s with expr := .seq a b } = some (t, s') := by
  obtain ⟨t, sa, ha⟩ := hstep
  simp only [step?, hnotval, ha]
  cases t with
  | error msg => exact ⟨_, _, rfl⟩
  | _ => exact ⟨_, _, rfl⟩

/-- `.seq (.var name) b` always steps (var always steps, seq delegates). -/
theorem step?_seq_var_isSome (s : State) (name : VarName) (b : Expr) :
    (step? { s with expr := .seq (.var name) b }).isSome = true := by
  simp [step?, exprValue?]; cases s.env.lookup name <;> simp [pushTrace]

/-- `.seq .this b` always steps (.this always steps, seq delegates). -/
theorem step?_seq_this_isSome (s : State) (b : Expr) :
    (step? { s with expr := .seq .this b }).isSome = true := by
  cases h : s.env.lookup "this" <;> simp [step?, h]

/-- `.seq (.var name) b` when var is found: steps silently to `.seq (.lit v) b`.
    Result uses explicit struct — proof agent can destructure directly. -/
theorem step?_seq_var_found_explicit (s : State) (name : VarName) (v : Value) (b : Expr)
    (henv : s.env.lookup name = some v) :
    step? { s with expr := .seq (.var name) b } =
      some (.silent, { expr := .seq (.lit v) b, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [step?, exprValue?, henv, pushTrace]

/-- `.seq (.var name) b` when var not found: steps with ReferenceError, error propagates (no seq wrap). -/
theorem step?_seq_var_not_found_explicit (s : State) (name : VarName) (b : Expr)
    (henv : s.env.lookup name = none) :
    step? { s with expr := .seq (.var name) b } =
      some (.error ("ReferenceError: " ++ name),
            { expr := .lit .undefined, env := s.env, heap := s.heap,
              trace := s.trace ++ [.error ("ReferenceError: " ++ name)],
              funcs := s.funcs, callStack := s.callStack }) := by
  simp [step?, exprValue?, henv, pushTrace]

/-- `.seq (.var name) b` when var found: steps to `.seq (.lit v) b`. -/
theorem step?_seq_var_steps_to_lit (s : State) (name : VarName) (v : Value) (b : Expr)
    (henv : s.env.lookup name = some v) :
    step? { s with expr := .seq (.var name) b } =
      some (.silent,
        { expr := .seq (.lit v) b, env := s.env, heap := s.heap,
          trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  simp [step?, exprValue?, henv, pushTrace]

/-- `.seq (.var name) b` when var not found: error propagates (no seq wrap). -/
theorem step?_seq_var_not_found_propagates (s : State) (name : VarName) (b : Expr)
    (henv : s.env.lookup name = none) :
    step? { s with expr := .seq (.var name) b } =
      some (.error ("ReferenceError: " ++ name),
        { expr := .lit .undefined, env := s.env, heap := s.heap,
          trace := s.trace ++ [.error ("ReferenceError: " ++ name)],
          funcs := s.funcs, callStack := s.callStack }) := by
  simp [step?, exprValue?, henv, pushTrace]

/-- `.seq .this b` always steps to a state with `.seq (.lit val) b` for some val.
    This is the key existential the proof agent needs for anfConvert_halt_star. -/
theorem step?_seq_this_steps_to_lit (s : State) (b : Expr) :
    ∃ val, step? { s with expr := .seq .this b } =
      some (.silent, { expr := .seq (.lit val) b, env := s.env, heap := s.heap,
                       trace := s.trace ++ [.silent], funcs := s.funcs, callStack := s.callStack }) := by
  cases henv : s.env.lookup "this" with
  | some v => exact ⟨v, by simp [step?, exprValue?, henv, pushTrace]⟩
  | none => exact ⟨.undefined, by simp [step?, exprValue?, henv, pushTrace]⟩

/-- `.var` always produces some result (existential form for case splitting). -/
theorem step?_var_some (s : State) (name : VarName) :
    ∃ t s', step? { s with expr := .var name } = some (t, s') := by
  cases h : s.env.lookup name with
  | some v => exact ⟨_, _, step?_var_found _ _ _ h⟩
  | none => exact ⟨_, _, step?_var_not_found _ _ h⟩

/-- `.this` always produces some result (existential form for case splitting). -/
theorem step?_this_some (s : State) :
    ∃ t s', step? { s with expr := .this } = some (t, s') := by
  cases h : s.env.lookup "this" with
  | some v => exact ⟨_, _, step?_this_found _ _ h⟩
  | none => exact ⟨_, _, step?_this_not_found _ h⟩

/-- `.var` result is always a literal expression (for proving halt characterization). -/
theorem step?_var_result_is_lit (s : State) (name : VarName) (t : Core.TraceEvent) (s' : State)
    (h : step? { s with expr := .var name } = some (t, s')) :
    ∃ v, s'.expr = .lit v := by
  cases henv : s.env.lookup name with
  | some v => rw [step?_var_found _ _ _ henv] at h; simp at h; rw [← h.2]; exact ⟨v, by simp [pushTrace]⟩
  | none => rw [step?_var_not_found _ _ henv] at h; simp at h; rw [← h.2]; exact ⟨.undefined, by simp [pushTrace]⟩

/-- If firstNonValueExpr returns none (all elements are literals),
    then valuesFromExprList? returns some list of values.
    This bridges the two representations for the proof agent. -/
theorem firstNonValueExpr_none_implies_values (l : List Expr)
    (h : firstNonValueExpr l = none) :
    ∃ vs, valuesFromExprList? l = some vs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons e rest ih =>
    unfold firstNonValueExpr at h
    match e, h with
    | .lit v, h =>
      simp at h
      split at h
      · contradiction
      · next hrest =>
        have ⟨vs, hvs⟩ := ih hrest
        exact ⟨v :: vs, by simp [valuesFromExprList?, exprValue?, hvs]⟩

/-- valuesFromExprList? on an empty list returns some []. -/
@[simp] theorem valuesFromExprList?_nil :
    valuesFromExprList? [] = some [] := rfl

/-- valuesFromExprList? on a lit cons propagates. -/
@[simp] theorem valuesFromExprList?_cons_lit (v : Value) (rest : List Expr) :
    valuesFromExprList? (.lit v :: rest) =
      (valuesFromExprList? rest).map (v :: ·) := by
  simp [valuesFromExprList?, exprValue?]
  cases valuesFromExprList? rest <;> simp [Option.map]

/-- If firstNonValueProp returns none, then valuesFromExprList? on the mapped values succeeds. -/
theorem firstNonValueProp_none_implies_map_values (props : List (PropName × Expr))
    (h : firstNonValueProp props = none) :
    ∃ vs, valuesFromExprList? (props.map Prod.snd) = some vs := by
  induction props with
  | nil => exact ⟨[], rfl⟩
  | cons p rest ih =>
    obtain ⟨name, e⟩ := p
    unfold firstNonValueProp at h
    match e with
    | .lit v =>
      simp at h
      split at h
      · contradiction
      · next hrest =>
        have ⟨vs, hvs⟩ := ih hrest
        exact ⟨v :: vs, by simp [valuesFromExprList?, exprValue?, hvs]⟩
    | .var _ | .«let» _ _ _ | .assign _ _ | .«if» _ _ _ | .seq _ _ | .call _ _ _
    | .newObj _ _ _ | .getProp _ _ | .setProp _ _ _ | .getIndex _ _ | .setIndex _ _ _
    | .deleteProp _ _ | .typeof _ | .getEnv _ _ | .makeEnv _ | .makeClosure _ _
    | .objectLit _ | .arrayLit _ | .throw _ | .tryCatch _ _ _ _ | .while_ _ _
    | .«break» _ | .«continue» _ | .labeled _ _ | .«return» _ | .yield _ _
    | .await _ | .this | .unary _ _ | .binary _ _ _ => simp at h

/-! ## Halting characterization -/

/-- The only Flat expression where step? returns none is a literal value.
    This is the Flat analogue of ANF.step?_none_implies_trivial_lit.
    REF: WasmCert-Coq progress lemma. -/
theorem step?_none_implies_lit (s : State) (h : step? s = none) :
    ∃ v, s.expr = .lit v := by
  -- Strong induction on expression depth
  suffices ∀ (n : Nat) (expr : Expr) (env : Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
      (funcs : Array FuncDef) (callStack : List Env),
      expr.depth ≤ n → step? ⟨expr, env, heap, trace, funcs, callStack⟩ = none →
      ∃ v, expr = .lit v by
    exact this s.expr.depth s.expr s.env s.heap s.trace s.funcs s.callStack (Nat.le_refl _)
      (by cases s; exact h)
  intro n
  induction n with
  | zero =>
    intro e env heap trace funcs callStack hd h
    cases e with
    | lit v => exact ⟨v, rfl⟩
    | var => unfold step? at h; split at h <;> simp at h
    | this => unfold step? at h; split at h <;> simp at h
    | «break» => unfold step? at h; simp [-step?] at h
    | «continue» => unfold step? at h; simp [-step?] at h
    | «return» arg =>
      cases arg with
      | none => unfold step? at h; simp [-step?] at h
      | some => simp [Expr.depth] at hd
    | yield arg =>
      cases arg with
      | none => unfold step? at h; simp [-step?] at h
      | some => simp [Expr.depth] at hd
    | «let» => simp [Expr.depth] at hd
    | assign => simp [Expr.depth] at hd
    | «if» => simp [Expr.depth] at hd
    | seq => simp [Expr.depth] at hd
    | call => simp [Expr.depth] at hd
    | newObj => simp [Expr.depth] at hd
    | getProp => simp [Expr.depth] at hd
    | setProp => simp [Expr.depth] at hd
    | getIndex => simp [Expr.depth] at hd
    | setIndex => simp [Expr.depth] at hd
    | deleteProp => simp [Expr.depth] at hd
    | typeof => simp [Expr.depth] at hd
    | getEnv => simp [Expr.depth] at hd
    | makeEnv => simp [Expr.depth] at hd
    | makeClosure => simp [Expr.depth] at hd
    | objectLit => simp [Expr.depth] at hd
    | arrayLit => simp [Expr.depth] at hd
    | throw => simp [Expr.depth] at hd
    | tryCatch _ _ _ f => cases f <;> simp [Expr.depth] at hd
    | while_ => simp [Expr.depth] at hd
    | labeled => simp [Expr.depth] at hd
    | unary => simp [Expr.depth] at hd
    | binary => simp [Expr.depth] at hd
    | await => simp [Expr.depth] at hd
  | succ k ih =>
    intro e env heap trace funcs callStack hd h
    -- Helper: if a sub-expression is stuck, IH gives it's a literal
    have litOfStuck : ∀ (sub : Expr), sub.depth ≤ k →
        step? ⟨sub, env, heap, trace, funcs, callStack⟩ = none → ∃ v, sub = .lit v :=
      fun sub hds hs => ih sub env heap trace funcs callStack hds hs
    cases e with
    | lit v => exact ⟨v, rfl⟩
    -- Always-step constructors
    | var => unfold step? at h; split at h <;> simp at h
    | this => unfold step? at h; split at h <;> simp at h
    | while_ => unfold step? at h; simp [-step?] at h
    | labeled => unfold step? at h; simp [-step?] at h
    | «break» => unfold step? at h; simp [-step?] at h
    | «continue» => unfold step? at h; simp [-step?] at h
    | «return» arg =>
      cases arg with
      | none => unfold step? at h; simp [-step?] at h
      | some e =>
        unfold step? at h; simp only [-step?] at h
        split at h; · simp at h
        · split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck e (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
    | yield arg _ =>
      cases arg with
      | none => unfold step? at h; simp [-step?] at h
      | some e =>
        unfold step? at h; simp only [-step?] at h
        split at h; · simp at h
        · split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck e (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
    -- Single sub-expression patterns: unfold, split on exprValue?, split on step?,
    -- use IH to get literal, contradiction with exprValue? = none
    | «let» _ init _ =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · split at h <;> simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck init (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | assign _ rhs =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · split at h <;> simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck rhs (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | «if» cond _ _ =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck cond (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | seq a _ =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · split at h <;> simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck a (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | unary _ arg =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck arg (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | typeof arg =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck arg (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | throw arg =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck arg (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | await arg =>
      unfold step? at h; simp only [-step?] at h
      split at h; · simp at h
      · split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck arg (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    -- Multi sub-expression cases: unfold step?, split on exprValue?/step? of sub-exprs,
    -- use IH (litOfStuck) to derive literal, contradict exprValue? = none.
    | binary _ lhs rhs =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · -- exprValue? lhs = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck lhs (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
      · -- exprValue? lhs = some _
        split at h
        · -- exprValue? rhs = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck rhs (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
        · -- exprValue? rhs = some _ → step? returns some
          simp at h
    | deleteProp obj _ =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · simp at h  -- some (.object _) → returns some
      · simp at h  -- some _ → returns some
      · -- exprValue? obj = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck obj (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | getProp obj _ =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · simp at h  -- some (.object addr) → returns some
      · simp at h  -- some (.string str) → returns some
      · simp at h  -- some _ → returns some
      · -- exprValue? obj = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck obj (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | makeClosure _ envExpr =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · simp at h  -- some (.object _) → returns some
      · simp at h  -- some _ → returns some
      · -- exprValue? envExpr = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck envExpr (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | getEnv envExpr _ =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · -- some (.object _) → nested matches, all return some
        split at h
        · split at h <;> simp at h
        · simp at h
      · simp at h  -- some _ → returns some
      · -- exprValue? envExpr = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck envExpr (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
    | setProp obj _ value =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · -- exprValue? obj = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck obj (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
      · -- exprValue? obj = some (.object addr)
        split at h
        · simp at h  -- exprValue? value = some → returns some
        · -- exprValue? value = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck value (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
      · -- some _ (non-object) → nested match on value
        split at h
        · simp at h  -- exprValue? value = some → returns some
        · -- exprValue? value = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck value (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
    | getIndex obj idx =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · -- exprValue? obj = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck obj (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
      · -- exprValue? obj = some (.object addr)
        split at h
        · simp at h  -- exprValue? idx = some → returns some
        · -- exprValue? idx = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck idx (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
      · -- exprValue? obj = some (.string str)
        split at h
        · simp at h  -- exprValue? idx = some → returns some
        · -- exprValue? idx = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck idx (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
      · -- some _ (non-object, non-string)
        split at h
        · simp at h  -- exprValue? idx = some → returns some
        · -- exprValue? idx = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck idx (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
    | setIndex obj idx value =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · -- exprValue? obj = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck obj (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
      · -- exprValue? obj = some (.object addr)
        split at h
        · -- exprValue? idx = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck idx (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
        · -- exprValue? idx = some _
          split at h
          · simp at h  -- exprValue? value = some → returns some
          · -- exprValue? value = none
            split at h
            · simp at h
            · next hval hstep =>
              have ⟨v, hv⟩ := litOfStuck value (by simp [Expr.depth] at hd; omega) hstep
              subst hv; simp_all [exprValue?]
      · -- some _ (non-object): nested matches on idx and value
        split at h
        · -- exprValue? idx = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck idx (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
        · -- exprValue? idx = some _
          split at h
          · simp at h  -- exprValue? value = some → returns some
          · -- exprValue? value = none
            split at h
            · simp at h
            · next hval hstep =>
              have ⟨v, hv⟩ := litOfStuck value (by simp [Expr.depth] at hd; omega) hstep
              subst hv; simp_all [exprValue?]
    -- List-pattern cases: firstNonValueExpr / firstNonValueProp with IH contradiction.
    | tryCatch body _ _ fin =>
      unfold step? at h; simp only [-step?] at h
      -- First split on exprValue? body
      split at h
      · -- exprValue? body = some → if isCallFrame then some; else match finally_ ...
        split at h
        · simp at h  -- isCallFrame = true → returns some
        · cases fin <;> simp at h  -- isCallFrame = false → both finally branches return some
      · -- exprValue? body = none
        split at h
        · -- step? body = some (.error ..) → isCallFrame checks, all return some
          split at h
          · simp at h  -- isCallFrame && startsWith → returns some
          · split at h <;> simp at h  -- isCallFrame else → returns some
        · simp at h  -- step? body = some (t, _) → returns some
        · -- step? body = none
          rename_i _ hstep
          have ⟨v, hv⟩ := litOfStuck body (by cases fin <;> simp [Expr.depth] at hd <;> omega) hstep
          subst hv; simp_all [exprValue?]
    | call funcExpr envExpr args =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · -- exprValue? funcExpr = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck funcExpr (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
      · -- exprValue? funcExpr = some _
        split at h
        · -- exprValue? envExpr = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck envExpr (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
        · -- exprValue? envExpr = some _
          split at h
          · -- valuesFromExprList? = some → match on closure, all branches return some
            split at h
            · -- exprValue? funcExpr = some (.closure ..) → consoleLog / funcs lookup
              split at h
              · simp at h  -- consoleLogIdx → returns some
              · split at h <;> simp at h  -- funcs[idx]? some/none → returns some
            · simp at h  -- non-closure callee → returns some
          · -- valuesFromExprList? = none
            split at h
            · -- firstNonValueExpr = some (done, target, remaining)
              split at h
              · simp at h
              · -- step? target = none → target must be lit → contradiction
                rename_i done' target' remaining' hfnve _ hstep
                have htgt := firstNonValueExpr_target_not_lit hfnve
                have ⟨v, hv⟩ := litOfStuck target'
                  (by simp [Expr.depth] at hd; have := firstNonValueExpr_depth hfnve; omega) hstep
                exact absurd hv (htgt v)
            · -- firstNonValueExpr = none → contradiction with valuesFromExprList? = none
              rename_i _ hvfnone hfnone
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values args hfnone
              simp_all
    | newObj funcExpr envExpr args =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · -- exprValue? funcExpr = none
        split at h
        · simp at h
        · next hval hstep =>
          have ⟨v, hv⟩ := litOfStuck funcExpr (by simp [Expr.depth] at hd; omega) hstep
          subst hv; simp_all [exprValue?]
      · -- exprValue? funcExpr = some _
        split at h
        · -- exprValue? envExpr = none
          split at h
          · simp at h
          · next hval hstep =>
            have ⟨v, hv⟩ := litOfStuck envExpr (by simp [Expr.depth] at hd; omega) hstep
            subst hv; simp_all [exprValue?]
        · -- exprValue? envExpr = some _
          split at h
          · simp at h  -- valuesFromExprList? = some → returns some
          · -- valuesFromExprList? = none
            split at h
            · -- firstNonValueExpr = some
              split at h
              · simp at h
              · rename_i done' target' remaining' hfnve _ hstep
                have htgt := firstNonValueExpr_target_not_lit hfnve
                have ⟨v, hv⟩ := litOfStuck target'
                  (by simp [Expr.depth] at hd; have := firstNonValueExpr_depth hfnve; omega) hstep
                exact absurd hv (htgt v)
            · rename_i _ hvfnone hfnone
              have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values args hfnone
              simp_all
    | makeEnv values =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · simp at h  -- valuesFromExprList? = some → returns some
      · -- valuesFromExprList? = none
        split at h
        · -- firstNonValueExpr = some
          split at h
          · simp at h
          · rename_i done' target' remaining' hfnve _ hstep
            have htgt := firstNonValueExpr_target_not_lit hfnve
            have ⟨v, hv⟩ := litOfStuck target'
              (by simp [Expr.depth] at hd; have := firstNonValueExpr_depth hfnve; omega) hstep
            exact absurd hv (htgt v)
        · rename_i hvfnone hfnone
          have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values values hfnone
          simp_all
    | arrayLit elems =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · simp at h  -- valuesFromExprList? = some → returns some
      · -- valuesFromExprList? = none
        split at h
        · -- firstNonValueExpr = some
          split at h
          · simp at h
          · rename_i done' target' remaining' hfnve _ hstep
            have htgt := firstNonValueExpr_target_not_lit hfnve
            have ⟨v, hv⟩ := litOfStuck target'
              (by simp [Expr.depth] at hd; have := firstNonValueExpr_depth hfnve; omega) hstep
            exact absurd hv (htgt v)
        · rename_i hvfnone hfnone
          have ⟨vs, hvs⟩ := firstNonValueExpr_none_implies_values elems hfnone
          simp_all
    | objectLit props =>
      unfold step? at h; simp only [-step?] at h
      split at h
      · simp at h  -- valuesFromExprList? (props.map Prod.snd) = some → returns some
      · -- valuesFromExprList? = none
        split at h
        · -- firstNonValueProp = some
          split at h
          · simp at h
          · rename_i done' propName' target' remaining' hfnvp _ hstep
            have htgt := firstNonValueProp_target_not_lit hfnvp
            have ⟨v, hv⟩ := litOfStuck target'
              (by simp [Expr.depth] at hd; have := firstNonValueProp_depth hfnvp; omega) hstep
            exact absurd hv (htgt v)
        · -- firstNonValueProp = none → contradiction with valuesFromExprList? = none
          rename_i hvfnone hfnone
          have ⟨vs, hvs⟩ := firstNonValueProp_none_implies_map_values props hfnone
          simp_all

/-! ## Equation lemmas for toNumber, valueToString, updateBindingList -/

@[simp] theorem toNumber_number (n : Float) : toNumber (.number n) = n := rfl
@[simp] theorem toNumber_bool_true : toNumber (.bool true) = 1.0 := rfl
@[simp] theorem toNumber_bool_false : toNumber (.bool false) = 0.0 := rfl
@[simp] theorem toNumber_null : toNumber .null = 0.0 := rfl
@[simp] theorem toNumber_undefined : toNumber .undefined = 0.0 / 0.0 := rfl
@[simp] theorem toNumber_object (a : Nat) : toNumber (.object a) = 0.0 / 0.0 := rfl
@[simp] theorem toNumber_closure (i e : Nat) : toNumber (.closure i e) = 0.0 / 0.0 := rfl

@[simp] theorem valueToString_string (s : String) : valueToString (.string s) = s := rfl
@[simp] theorem valueToString_bool_true : valueToString (.bool true) = "true" := rfl
@[simp] theorem valueToString_bool_false : valueToString (.bool false) = "false" := rfl
@[simp] theorem valueToString_null : valueToString .null = "null" := rfl
@[simp] theorem valueToString_undefined : valueToString .undefined = "undefined" := rfl
@[simp] theorem valueToString_object (a : Nat) : valueToString (.object a) = "[object Object]" := rfl
@[simp] theorem valueToString_closure (i e : Nat) : valueToString (.closure i e) = "function" := rfl

@[simp] theorem updateBindingList_nil (name : VarName) (v : Value) :
    updateBindingList [] name v = [] := rfl
@[simp] theorem updateBindingList_cons_eq (n : VarName) (old : Value) (rest : Env) (v : Value) :
    updateBindingList ((n, old) :: rest) n v = (n, v) :: rest := by
  simp [updateBindingList]
@[simp] theorem updateBindingList_cons_ne (n m : VarName) (old : Value) (rest : Env) (v : Value)
    (h : ¬(n == m)) :
    updateBindingList ((n, old) :: rest) m v = (n, old) :: updateBindingList rest m v := by
  simp [updateBindingList, h]

/-- Lookup after updateBindingList for the same name. -/
@[simp] theorem lookup_updateBindingList_eq (xs : Env) (name : VarName) (v : Value)
    (h : xs.any (fun kv => kv.fst == name) = true) :
    Env.lookup (updateBindingList xs name v) name = some v := by
  induction xs with
  | nil => simp [List.any] at h
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    unfold updateBindingList
    split
    next heq => unfold Env.lookup; simp [List.find?, heq]
    next hne =>
      unfold Env.lookup; simp only [List.find?, hne]
      apply ih
      simp only [List.any, Bool.or_eq_true] at h
      rcases h with h | h
      · exact absurd h (by simpa using hne)
      · exact h

/-- Lookup after updateBindingList for a different name. -/
@[simp] theorem lookup_updateBindingList_ne (xs : Env) (name other : VarName) (v : Value)
    (hne : (other == name) = false) :
    Env.lookup (updateBindingList xs name v) other = Env.lookup xs other := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    unfold updateBindingList
    split
    next heq =>
      unfold Env.lookup
      have hnn : n = name := beq_iff_eq.mp heq
      subst hnn
      have hno : (n == other) = false := by
        rw [show (n == other) = (other == n) from by simp [BEq.comm]]; exact hne
      simp [List.find?, hno]
    next hneq =>
      unfold Env.lookup
      simp only [List.find?]
      cases hno : (n == other)
      · exact ih
      · rfl

/-- Lookup after assign for the same name (existing binding). -/
@[simp] theorem Env.lookup_assign_eq (env : Env) (name : VarName) (v : Value)
    (h : env.any (fun kv => kv.fst == name) = true) :
    (env.assign name v).lookup name = some v := by
  simp [Env.assign, h, lookup_updateBindingList_eq]

/-- Lookup after assign for a different name. -/
@[simp] theorem Env.lookup_assign_ne (env : Env) (name other : VarName) (v : Value)
    (hne : (other == name) = false) :
    (env.assign name v).lookup other = env.lookup other := by
  simp only [Env.assign]
  split
  · exact lookup_updateBindingList_ne env name other v hne
  · have hno : (name == other) = false := by
      rw [show (name == other) = (other == name) from by simp [BEq.comm]]; exact hne
    simp [Env.lookup, List.find?, hno]

/-- Lookup after assign for the same name (new binding). -/
@[simp] theorem Env.lookup_assign_new (env : Env) (name : VarName) (v : Value)
    (h : env.any (fun kv => kv.fst == name) = false) :
    (env.assign name v).lookup name = some v := by
  simp [Env.assign, h, Env.lookup]

/-- pushTrace only modifies the trace field; heap is unchanged. -/
@[simp] theorem step?_pushTrace_expand (s : State) (t : Core.TraceEvent) :
    pushTrace s t = { s with trace := s.trace ++ [t] } := rfl

/-- When all objectLit props are values, Flat.step? allocates on heap. -/
theorem step?_objectLit_allValues (s : State)
    (props : List (PropName × Expr))
    (vs : List Value)
    (hvs : valuesFromExprList? (props.map Prod.snd) = some vs) :
    step? { s with expr := .objectLit props } =
      some (.silent,
        ⟨.lit (.object s.heap.nextAddr), s.env,
         ⟨s.heap.objects.push (props.filterMap fun (k, e) =>
            match exprValue? e with | some v => some (k, flatToCoreValue v) | none => none),
          s.heap.nextAddr + 1⟩,
         s.trace ++ [.silent], s.funcs, s.callStack⟩) := by
  unfold step?; simp only [hvs, allocObjectWithProps, pushTrace]

/-- When all arrayLit elems are values, Flat.step? allocates on heap. -/
theorem step?_arrayLit_allValues (s : State)
    (elems : List Expr)
    (vs : List Value)
    (hvs : valuesFromExprList? elems = some vs) :
    step? { s with expr := .arrayLit elems } =
      some (.silent,
        ⟨.lit (.object s.heap.nextAddr), s.env,
         ⟨s.heap.objects.push (elems.zipIdx.filterMap fun (e, i) =>
            match exprValue? e with | some v => some (toString i, flatToCoreValue v) | none => none),
          s.heap.nextAddr + 1⟩,
         s.trace ++ [.silent], s.funcs, s.callStack⟩) := by
  unfold step?; simp only [hvs, allocObjectWithProps, pushTrace]

theorem step?_newObj_allValues (s : State)
    (funcExpr envExpr : Expr) (args : List Expr)
    (fv ev : Value) (vs : List Value)
    (hf : exprValue? funcExpr = some fv)
    (he : exprValue? envExpr = some ev)
    (hvs : valuesFromExprList? args = some vs) :
    step? { s with expr := .newObj funcExpr envExpr args } =
      some (.silent, ⟨.lit (.object s.heap.nextAddr), s.env,
        ⟨s.heap.objects.push [], s.heap.nextAddr + 1⟩,
        s.trace ++ [.silent], s.funcs, s.callStack⟩) := by
  unfold step?; simp only [hf, he, hvs, allocFreshObject, pushTrace]

set_option maxHeartbeats 8000000 in
/-- step? never modifies the funcs field. -/
theorem step?_preserves_funcs (sf : Flat.State) (ev : Core.TraceEvent) (sf' : Flat.State)
    (h : step? sf = some (ev, sf')) : sf'.funcs = sf.funcs := by
  unfold step? at h
  split at h
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try contradiction)
  all_goals (try { obtain ⟨-, rfl⟩ := h; rfl })
  all_goals (try { simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl })
  all_goals (try { simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨-, rfl⟩ := h; simp [pushTrace] })

/-- Multi-step execution preserves the funcs field. -/
theorem Steps_preserves_funcs {sf sf' : Flat.State} {evs : List Core.TraceEvent}
    (h : Flat.Steps sf evs sf') : sf'.funcs = sf.funcs := by
  induction h with
  | refl => rfl
  | tail hstep _ ih => obtain ⟨h⟩ := hstep; exact (step?_preserves_funcs _ _ _ h) ▸ ih

set_option maxHeartbeats 8000000 in
/-- step? always sets trace to s.trace ++ [t]. -/
theorem step?_trace_append (sf : Flat.State) (ev : Core.TraceEvent) (sf' : Flat.State)
    (h : step? sf = some (ev, sf')) : sf'.trace = sf.trace ++ [ev] := by
  unfold step? at h
  split at h
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try (dsimp only [] at h)); all_goals (try (split at h))
  all_goals (try contradiction)
  all_goals (try { obtain ⟨-, rfl⟩ := h; simp [pushTrace] })
  all_goals (try { simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp [pushTrace] })

/-- Multi-step execution accumulates trace: sf'.trace = sf.trace ++ evs. -/
theorem Steps_trace_append {sf sf' : Flat.State} {evs : List Core.TraceEvent}
    (h : Flat.Steps sf evs sf') : sf'.trace = sf.trace ++ evs := by
  induction h with
  | refl => simp
  | tail hstep _ ih =>
    obtain ⟨h⟩ := hstep
    rw [ih, step?_trace_append _ _ _ h]; simp [List.append_assoc]

end VerifiedJS.Flat
