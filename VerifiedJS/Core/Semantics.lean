/-
  VerifiedJS — Core IL Semantics
  Small-step LTS as an inductive relation.
  SPEC: §8 (Executable Code and Execution Contexts), §9 (Ordinary Object Internal Methods)
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.Core

/-- Observable trace events emitted by Core execution. -/
inductive TraceEvent where
  | log (s : String)
  | error (s : String)
  | silent
  deriving Repr, BEq

/-- ECMA-262 §8.1 Environment Records (simplified lexical bindings for Core). -/
structure Env where
  bindings : List (VarName × Value)
  deriving Repr

/-- ECMA-262 §9.1 Ordinary object storage (heap abstract state). -/
structure Heap where
  objects : Array (List (PropName × Value))
  nextAddr : Nat
  deriving Repr

/-- ECMA-262 §8.3 Execution Contexts (Core machine state). -/
structure State where
  expr : Expr
  env : Env
  heap : Heap
  trace : List TraceEvent
  funcs : Array FuncClosure
  /-- Call stack: saved caller environments for function call return. -/
  callStack : List (List (VarName × Value))
  deriving Repr

/-- Empty lexical environment. -/
def Env.empty : Env :=
  { bindings := [] }

/-- Empty heap. -/
def Heap.empty : Heap :=
  { objects := #[], nextAddr := 0 }

/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lookup in lexical bindings). -/
def Env.lookup (env : Env) (name : VarName) : Option Value :=
  match env.bindings.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

private def updateBindingList (xs : List (VarName × Value)) (name : VarName) (v : Value) : List (VarName × Value) :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Value) : Env :=
  if env.bindings.any (fun kv => kv.fst == name) then
    { bindings := updateBindingList env.bindings name v }
  else
    { bindings := (name, v) :: env.bindings }

/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Value) : Env :=
  { bindings := (name, v) :: env.bindings }

/-- Check whether an expression is a value expression. -/
def exprValue? : Expr → Option Value
  | .lit v => some v
  | _ => none

/-- ECMA-262 §7.2.14 ToBoolean (core subset). -/
def toBoolean : Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .function _ => true

/-- ECMA-262 §7.1.3 ToNumber (core subset). -/
def toNumber : Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | .undefined => 0.0 / 0.0  -- ECMA-262 §7.1.3: undefined → NaN
  | .string s =>
      -- ECMA-262 §7.1.3.1: StringNumericValue.
      let trimmed := s.trim
      if trimmed.isEmpty then 0.0
      else
        -- Try to parse as integer literal, fallback to NaN.
        match trimmed.toNat? with
        | some n => Float.ofNat n
        | none =>
            -- Check for negative integers.
            if trimmed.startsWith "-" then
              match (trimmed.drop 1).toNat? with
              | some n => -(Float.ofNat n)
              | none => 0.0 / 0.0  -- NaN
            else 0.0 / 0.0  -- NaN for non-numeric strings
  | _ => 0.0 / 0.0  -- NaN for objects/functions

/-- ECMA-262 §13.5 Runtime Semantics: Evaluation (core unary subset). -/
def evalUnary : UnaryOp → Value → Value
  | .neg, v => .number (-toNumber v)
  | .pos, v => .number (toNumber v)
  | .logNot, v => .bool (!toBoolean v)
  | .void, _ => .undefined
  -- ECMA-262 §12.5.8 Bitwise NOT: ~ToInt32(x).
  | .bitNot, v => .number (~~~(toNumber v |>.toUInt32)).toFloat

/-- ECMA-262 §7.1.12 ToString (core subset). -/
def valueToString : Value → String
  | .string s => s
  | .number n =>
      -- §7.1.12.1: if n is an integer, omit decimal point.
      if n.isNaN then "NaN"
      else if n == 1.0/0.0 then "Infinity"
      else if n == -1.0/0.0 then "-Infinity"
      else
        let i := n.toUInt64
        if i.toFloat == n && n >= 0.0 then toString i.toNat
        else toString n
  | .bool true => "true"
  | .bool false => "false"
  | .null => "null"
  | .undefined => "undefined"
  | .object _ => "[object Object]"
  | .function _ => "function"

/-- ECMA-262 §7.2.14 Abstract Equality Comparison (simplified core subset).
    Handles null/undefined equivalence and type coercion. -/
private def abstractEq : Value → Value → Bool
  -- §7.2.14 step 1: same type → strict equality
  | .null, .null => true
  | .undefined, .undefined => true
  -- §7.2.14 step 2: null == undefined → true
  | .null, .undefined => true
  | .undefined, .null => true
  -- Same-type comparisons
  | .bool a, .bool b => a == b
  | .number a, .number b => a == b
  | .string a, .string b => a == b
  | .object a, .object b => a == b
  | .function a, .function b => a == b
  -- §7.2.14 step 5: number == string → number == ToNumber(string)
  | .number a, .string b => a == toNumber (.string b)
  | .string a, .number b => toNumber (.string a) == b
  -- §7.2.14 step 7-8: boolean == x → ToNumber(boolean) == x
  | .bool a, .number b => (toNumber (.bool a)) == b
  | .bool a, .string b => (toNumber (.bool a)) == (toNumber (.string b))
  | .number a, .bool b => a == (toNumber (.bool b))
  | .string a, .bool b => (toNumber (.string a)) == (toNumber (.bool b))
  -- All other cross-type comparisons: false
  | _, _ => false

/-- ECMA-262 §7.2.13 Abstract Relational Comparison (string-aware). -/
private def abstractLt : Value → Value → Bool
  | .string a, .string b => a < b  -- lexicographic comparison
  | a, b => toNumber a < toNumber b

/-- ECMA-262 §13.15 Runtime Semantics: Evaluation (core binary subset). -/
def evalBinary : BinOp → Value → Value → Value
  -- ECMA-262 §12.8.3: if either operand is a string, concatenate after ToString.
  | .add, .string a, .string b => .string (a ++ b)
  | .add, .string a, b => .string (a ++ valueToString b)
  | .add, a, .string b => .string (valueToString a ++ b)
  | .add, a, b => .number (toNumber a + toNumber b)
  | .sub, a, b => .number (toNumber a - toNumber b)
  | .mul, a, b => .number (toNumber a * toNumber b)
  | .div, a, b => .number (toNumber a / toNumber b)
  -- §7.2.14 Abstract Equality (with type coercion).
  | .eq, a, b => .bool (abstractEq a b)
  | .neq, a, b => .bool (!abstractEq a b)
  -- §7.2.15 Strict Equality (no type coercion).
  | .strictEq, a, b => .bool (a == b)
  | .strictNeq, a, b => .bool (a != b)
  -- §7.2.13 Abstract Relational Comparison (string-aware).
  | .lt, a, b => .bool (abstractLt a b)
  | .gt, a, b => .bool (abstractLt b a)
  | .le, a, b => .bool (!abstractLt b a)
  | .ge, a, b => .bool (!abstractLt a b)
  | .logAnd, a, b => if toBoolean a then b else a
  | .logOr, a, b => if toBoolean a then a else b
  -- ECMA-262 §12.10.4 instanceof: simplified — checks if rhs is a function.
  | .instanceof, .object _, .function _ => .bool true
  | .instanceof, _, .function _ => .bool false
  | .instanceof, _, _ => .bool false
  -- ECMA-262 §12.10.2 in operator: simplified — checks property existence.
  | .«in», .string _, .object _ => .bool true  -- simplified: always true for string key on object
  | .«in», _, _ => .bool false
  -- ECMA-262 §12.9 modulus and exponentiation.
  | .mod, a, b =>
      let na := toNumber a; let nb := toNumber b
      if nb == 0.0 then .number (0.0 / 0.0) else .number (na - nb * (na / nb).floor)
  | .exp, a, b => .number (Float.pow (toNumber a) (toNumber b))
  -- ECMA-262 §12.12 Bitwise operators.
  -- §7.1.6 ToInt32: truncate float to signed 32-bit integer for bitwise operations.
  | .bitAnd, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia &&& ib).toFloat)
  | .bitOr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia ||| ib).toFloat)
  | .bitXor, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := toNumber b |>.toUInt32
      .number ((ia ^^^ ib).toFloat)
  -- ECMA-262 §12.9.3 ShiftExpression: left shift.
  | .shl, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia <<< ib).toFloat)
  -- ECMA-262 §12.9.3 ShiftExpression: signed right shift.
  | .shr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia >>> ib).toFloat)
  -- ECMA-262 §12.9.3 ShiftExpression: unsigned right shift.
  | .ushr, a, b =>
      let ia := toNumber a |>.toUInt32; let ib := (toNumber b |>.toUInt32) % 32
      .number ((ia >>> ib).toFloat)

/-- Built-in function index for console.log (reserved at index 0). -/
private def consoleLogIdx : FuncIdx := 0

private def pushTrace (s : State) (t : TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

/-- One deterministic Core small-step transition with emitted trace event. -/
def step? (s : State) : Option (TraceEvent × State) :=
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
  | .let name init body =>
      match exprValue? init with
      | some v =>
          let s' := pushTrace { s with expr := body, env := s.env.extend name v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := init } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .let name si.expr body, trace := s.trace } t
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
              let s' := pushTrace { sr with expr := .assign name sr.expr, trace := s.trace } t
              some (t, s')
          | none => none
  | .if cond then_ else_ =>
      match exprValue? cond with
      | some v =>
          let next := if toBoolean v then then_ else else_
          let s' := pushTrace { s with expr := next } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := cond } with
          | some (t, sc) =>
              let s' := pushTrace { sc with expr := .if sc.expr then_ else_, trace := s.trace } t
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
              let s' := pushTrace { sa with expr := .seq sa.expr b, trace := s.trace } t
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
              let s' := pushTrace { sa with expr := .unary op sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  | .binary op lhs rhs =>
      match exprValue? lhs with
      | none =>
          match step? { s with expr := lhs } with
          | some (t, sl) =>
              let s' := pushTrace { sl with expr := .binary op sl.expr rhs, trace := s.trace } t
              some (t, s')
          | none => none
      | some lv =>
          match exprValue? rhs with
          | none =>
              match step? { s with expr := rhs } with
              | some (t, sr) =>
                  let s' := pushTrace { sr with expr := .binary op (.lit lv) sr.expr, trace := s.trace } t
                  some (t, s')
              | none => none
          | some rv =>
              let s' := pushTrace { s with expr := .lit (evalBinary op lv rv) } .silent
              some (.silent, s')
  -- ECMA-262 §13.3.1 function call with closure invocation.
  | .call callee args =>
      -- Step 1: Step callee to a value.
      match exprValue? callee with
      | none =>
          match step? { s with expr := callee } with
          | some (t, sc) =>
              let s' := pushTrace { sc with expr := .call sc.expr args, trace := s.trace } t
              some (t, s')
          | none => none
      | some cv =>
          -- Step 2: Step all arguments to values (left-to-right).
          match allValues args with
          | some argVals =>
              -- Step 3: All args are values — perform the call.
              match cv with
              | .function idx =>
                  -- §18.2 Built-in: console.log (reserved at function index 0).
                  if idx == consoleLogIdx then
                      let msg := match argVals with
                        | [v] => valueToString v
                        | vs => String.intercalate " " (vs.map valueToString)
                      let s' := pushTrace { s with expr := .lit .undefined } (.log msg)
                      some (.log msg, s')
                  else
                  match s.funcs[idx]? with
                  | some closure =>
                      -- §10.2.1 [[Call]]: bind params to args in closure's captured environment.
                      let pairs := closure.params.zip argVals
                      let bodyBindings :=
                        pairs.foldr (fun pv bs => (pv.1, pv.2) :: bs) closure.capturedEnv
                      let bodyEnv : Env := { bindings := bodyBindings }
                      -- Bind function name for recursion (§14.1.20 step 28).
                      let bodyEnv' : Env := match closure.name with
                        | some n => { bindings := (n, .function idx) :: bodyEnv.bindings }
                        | none => bodyEnv
                      -- Push caller env onto call stack for restoration on return.
                      -- Wrap body in tryCatch with special catch param to intercept returns.
                      let wrapped := .tryCatch closure.body "__call_frame_return__"
                        (.var "__call_frame_return__") none
                      let s' := pushTrace { s with
                        expr := wrapped
                        env := bodyEnv'
                        callStack := s.env.bindings :: s.callStack } .silent
                      some (.silent, s')
                  | none =>
                      let s' := pushTrace { s with expr := .lit .undefined } .silent
                      some (.silent, s')
              | _ =>
                  -- Non-function callee: return undefined.
                  let s' := pushTrace { s with expr := .lit .undefined } .silent
                  some (.silent, s')
          | none =>
              -- Step first non-value argument (left-to-right evaluation §12.3.4.1).
              match hf : firstNonValueExpr args with
              | some (done, target, remaining) =>
                  have : Expr.depth target < Expr.depth s.expr := by
                    rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
                  match step? { s with expr := target } with
                  | some (t, sa) =>
                      let s' := pushTrace { sa with expr := .call (.lit cv) (done ++ [sa.expr] ++ remaining), trace := s.trace } t
                      some (t, s')
                  | none => none
              | none => none
  -- ECMA-262 §12.3.2 Property Accessors.
  | .getProp obj prop =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .getProp so.expr prop, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          -- ECMA-262 §9.1.8 [[Get]]: look up property on heap object.
          let v := match s.heap.objects[addr]? with
            | some props =>
                match props.find? (fun kv => kv.fst == prop) with
                | some (_, v) => v
                | none => .undefined
            | none => .undefined
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | some _ =>
          -- Property access on primitive: return undefined.
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- ECMA-262 §12.3.2 Computed Property Accessors (bracket notation).
  | .getIndex obj idx =>
      match exprValue? obj, exprValue? idx with
      | none, _ =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .getIndex so.expr idx, trace := s.trace } t
              some (t, s')
          | none => none
      | some _, none =>
          match step? { s with expr := idx } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .getIndex (.lit (match exprValue? obj with | some v => v | none => .undefined)) si.expr, trace := s.trace } t
              some (t, s')
          | none => none
      | some objVal, some idxVal =>
          -- ECMA-262 §9.1.8 [[Get]] with computed key: convert index to string.
          let propName := match idxVal with
            | .string s => s
            | .number n => toString n
            | _ => toString (repr idxVal)
          match objVal with
          | .object addr =>
              let v := match s.heap.objects[addr]? with
                | some props =>
                    match props.find? (fun kv => kv.fst == propName) with
                    | some (_, v) => v
                    | none => .undefined
                | none => .undefined
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | _ =>
              let s' := pushTrace { s with expr := .lit .undefined } .silent
              some (.silent, s')
  -- ECMA-262 §14.1 Function Definitions — capture closure as function value.
  | .functionDef fname params body _isAsync _isGenerator =>
      -- §10.2: Create a function closure capturing the current lexical environment.
      let closure : FuncClosure := ⟨fname, params, body, s.env.bindings⟩
      let idx := s.funcs.size
      let funcs' := s.funcs.push closure
      let s' := pushTrace { s with expr := .lit (.function idx), funcs := funcs' } .silent
      some (.silent, s')
  -- ECMA-262 §12.2.6 Object Initializer.
  | .objectLit props =>
      match hf : firstNonValueProp props with
      | some (done, k, target, rest) =>
          have : Expr.depth target < Expr.depth s.expr := by
            rw [h]; simp [Expr.depth]; have := firstNonValueProp_depth hf; omega
          match step? { s with expr := target } with
          | some (t, se) =>
              let s' := pushTrace { se with expr := .objectLit (done ++ [(k, se.expr)] ++ rest), trace := s.trace } t
              some (t, s')
          | none => none
      | none =>
          -- All props are values: allocate object on heap with properties.
          let addr := s.heap.nextAddr
          let heapProps := props.filterMap fun (k, e) =>
            match exprValue? e with
            | some v => some (k, v)
            | none => none  -- shouldn't happen
          let heap' := { objects := s.heap.objects.push heapProps, nextAddr := addr + 1 }
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
  -- ECMA-262 §12.2.5 Array Initializer.
  | .arrayLit elems =>
      match hf : firstNonValueExpr elems with
      | some (done, target, rest) =>
          have : Expr.depth target < Expr.depth s.expr := by
            rw [h]; simp [Expr.depth]; have := firstNonValueExpr_depth hf; omega
          match step? { s with expr := target } with
          | some (t, se) =>
              let s' := pushTrace { se with expr := .arrayLit (done ++ [se.expr] ++ rest), trace := s.trace } t
              some (t, s')
          | none => none
      | none =>
          -- All elements are values: allocate array on heap with indexed entries.
          let addr := s.heap.nextAddr
          let heapProps := mkIndexedProps 0 elems
          let heap' := { objects := s.heap.objects.push heapProps, nextAddr := addr + 1 }
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
          some (.silent, s')
  | .while_ cond body =>
      let lowered := .if cond (.seq body (.while_ cond body)) (.lit .undefined)
      let s' := pushTrace { s with expr := lowered } .silent
      some (.silent, s')
  -- ECMA-262 §13.7.5 for-in: EnumerateObjectProperties (§13.7.5.15).
  -- Desugars to sequential iteration over property keys of the object.
  | .forIn binding obj body =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .forIn binding so.expr body, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          -- §13.7.5.15 EnumerateObjectProperties: iterate over own enumerable string-keyed properties.
          let keys : List PropName := match s.heap.objects[addr]? with
            | some props => props.map (fun p : PropName × Value => p.1)
            | none => []
          -- Desugar: for each key, bind it and run body.
          let lowered := keys.foldr (fun key acc =>
            .seq (.«let» binding (.lit (.string key)) body) acc
          ) (.lit .undefined)
          let s' := pushTrace { s with expr := lowered } .silent
          some (.silent, s')
      | some _ =>
          -- for-in on non-object: no iteration (per spec, ToObject then enumerate).
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- ECMA-262 §13.7.5.13 for-of: GetIterator (§7.4.1) / IteratorStep.
  -- Simplified: for arrays on heap, iterate over stored elements.
  | .forOf binding iterable body =>
      match exprValue? iterable with
      | none =>
          match step? { s with expr := iterable } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .forOf binding si.expr body, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          -- Simplified iterator: treat heap object entries as ordered elements.
          let elems : List Value := match s.heap.objects[addr]? with
            | some props => props.map (fun p : PropName × Value => p.2)
            | none => []
          -- Desugar: for each element value, bind it and run body.
          let lowered := elems.foldr (fun val acc =>
            .seq (.«let» binding (.lit val) body) acc
          ) (.lit .undefined)
          let s' := pushTrace { s with expr := lowered } .silent
          some (.silent, s')
      | some _ =>
          -- for-of on non-iterable: no iteration.
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  | .labeled _ body =>
      let s' := pushTrace { s with expr := body } .silent
      some (.silent, s')
  | .throw arg =>
      match exprValue? arg with
      | some v =>
          -- ECMA-262 §13.14 throw: produce error event with stringified value.
          let msg := valueToString v
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .throw sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  -- ECMA-262 §13.15 try/catch/finally: exception handling.
  | .tryCatch body catchParam catchBody finally_ =>
      let isCallFrame := catchParam == "__call_frame_return__"
      match exprValue? body with
      | some v =>
          if isCallFrame then
              -- Function normal completion: restore caller env from callStack.
              let restoredEnv : Env := match s.callStack with
                | saved :: _ => ⟨saved⟩
                | [] => s.env
              let newStack := match s.callStack with
                | _ :: rest => rest
                | [] => []
              let s' := pushTrace { s with expr := .lit v, env := restoredEnv, callStack := newStack } .silent
              some (.silent, s')
          else
              -- Normal completion: run finally (if present), then yield value.
              match finally_ with
              | some fin =>
                  let s' := pushTrace { s with expr := .seq fin (.lit v) } .silent
                  some (.silent, s')
              | none =>
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
      | none =>
          -- Step the try-body; intercept error events for catch.
          match step? { s with expr := body } with
          | some (.error msg, sb) =>
              if isCallFrame && msg.startsWith "return:" then
                  -- Function return: extract value from sb.expr, restore caller env.
                  let retVal := match exprValue? sb.expr with
                    | some v => v
                    | none => .undefined
                  let restoredEnv : Env := match s.callStack with
                    | saved :: _ => ⟨saved⟩
                    | [] => sb.env
                  let newStack := match s.callStack with
                    | _ :: rest => rest
                    | [] => []
                  let s' := pushTrace
                    { s with expr := .lit retVal, env := restoredEnv
                           , heap := sb.heap, funcs := sb.funcs
                           , callStack := newStack } .silent
                  some (.silent, s')
              else if isCallFrame then
                  -- Function threw: propagate error, restore caller env.
                  let restoredEnv : Env := match s.callStack with
                    | saved :: _ => ⟨saved⟩
                    | [] => sb.env
                  let newStack := match s.callStack with
                    | _ :: rest => rest
                    | [] => []
                  let s' := pushTrace
                    { s with expr := .lit .undefined, env := restoredEnv
                           , heap := sb.heap, funcs := sb.funcs
                           , callStack := newStack } (.error msg)
                  some (.error msg, s')
              else
                  -- Regular exception caught: bind error to catchParam, run catch body.
                  let handler :=
                    match finally_ with
                    | some fin => .seq catchBody fin
                    | none => catchBody
                  let catchEnv := sb.env.extend catchParam (.string msg)
                  let s' := pushTrace
                    { sb with expr := handler, env := catchEnv, trace := s.trace } (.error msg)
                  some (.error msg, s')
          | some (t, sb) =>
              -- Normal step inside try body: keep wrapping in tryCatch.
              let s' := pushTrace
                { sb with expr := .tryCatch sb.expr catchParam catchBody finally_
                        , trace := s.trace } t
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
  -- ECMA-262 §12.5.6 typeof operator.
  | .typeof arg =>
      match exprValue? arg with
      | some v =>
          let result := match v with
            | .undefined => "undefined"
            | .null => "object"  -- typeof null === "object" per spec
            | .bool _ => "boolean"
            | .number _ => "number"
            | .string _ => "string"
            | .function _ => "function"
            | .object _ => "object"
          let s' := pushTrace { s with expr := .lit (.string result) } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .typeof sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  -- ECMA-262 §13.1 Block statement / §13.6 return / §13.8 break / §13.9 continue
  | .«return» arg =>
      match arg with
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } (.error ("return:" ++ toString (repr v)))
              some (.error ("return:" ++ toString (repr v)), s')
          | none =>
              match step? { s with expr := e } with
              | some (t, sa) =>
                  let s' := pushTrace { sa with expr := .«return» (some sa.expr), trace := s.trace } t
                  some (t, s')
              | none => none
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } (.error "return:undefined")
          some (.error "return:undefined", s')
  | .«break» label =>
      let l := match label with | some s => "break:" ++ s | none => "break:"
      let s' := pushTrace { s with expr := .lit .undefined } (.error l)
      some (.error l, s')
  | .«continue» label =>
      let l := match label with | some s => "continue:" ++ s | none => "continue:"
      let s' := pushTrace { s with expr := .lit .undefined } (.error l)
      some (.error l, s')
  -- ECMA-262 §9.1.9 [[Set]]: property assignment on heap objects.
  | .setProp obj prop value =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .setProp so.expr prop value, trace := s.trace } t
              some (t, s')
          | none => none
      | some objVal =>
          match exprValue? value with
          | none =>
              match step? { s with expr := value } with
              | some (t, sv) =>
                  let s' := pushTrace { sv with expr := .setProp (.lit objVal) prop sv.expr, trace := s.trace } t
                  some (t, s')
              | none => none
          | some v =>
              match objVal with
              | .object addr =>
                  -- Update or add property on the heap object.
                  let heap' := match s.heap.objects[addr]? with
                    | some props =>
                        let updated := if props.any (fun kv => kv.fst == prop)
                          then props.map (fun kv => if kv.fst == prop then (prop, v) else kv)
                          else props ++ [(prop, v)]
                        { s.heap with objects := s.heap.objects.set! addr updated }
                    | none => s.heap
                  let s' := pushTrace { s with expr := .lit v, heap := heap' } .silent
                  some (.silent, s')
              | _ =>
                  -- Property set on non-object: silently return value.
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
  -- ECMA-262 §9.1.9 [[Set]] computed property: bracket notation assignment.
  | .setIndex obj idx value =>
      match exprValue? obj, exprValue? idx, exprValue? value with
      | none, _, _ =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .setIndex so.expr idx value, trace := s.trace } t
              some (t, s')
          | none => none
      | some _, none, _ =>
          match step? { s with expr := idx } with
          | some (t, si) =>
              let s' := pushTrace { si with expr := .setIndex (.lit (match exprValue? obj with | some v => v | none => .undefined)) si.expr value, trace := s.trace } t
              some (t, s')
          | none => none
      | some _, some _, none =>
          match step? { s with expr := value } with
          | some (t, sv) =>
              let s' := pushTrace { sv with expr := .setIndex (.lit (match exprValue? obj with | some v => v | none => .undefined)) (.lit (match exprValue? idx with | some v => v | none => .undefined)) sv.expr, trace := s.trace } t
              some (t, s')
          | none => none
      | some objVal, some idxVal, some v =>
          let propName := match idxVal with
            | .string s => s
            | .number n => toString n
            | _ => toString (repr idxVal)
          match objVal with
          | .object addr =>
              let heap' := match s.heap.objects[addr]? with
                | some props =>
                    let updated := if props.any (fun kv => kv.fst == propName)
                      then props.map (fun kv => if kv.fst == propName then (propName, v) else kv)
                      else props ++ [(propName, v)]
                    { s.heap with objects := s.heap.objects.set! addr updated }
                | none => s.heap
              let s' := pushTrace { s with expr := .lit v, heap := heap' } .silent
              some (.silent, s')
          | _ =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
  -- ECMA-262 §12.4.3 delete operator on object properties.
  | .deleteProp obj prop =>
      match exprValue? obj with
      | none =>
          match step? { s with expr := obj } with
          | some (t, so) =>
              let s' := pushTrace { so with expr := .deleteProp so.expr prop, trace := s.trace } t
              some (t, s')
          | none => none
      | some (.object addr) =>
          let heap' := match s.heap.objects[addr]? with
            | some props =>
                let filtered := props.filter (fun kv => kv.fst != prop)
                { s.heap with objects := s.heap.objects.set! addr filtered }
            | none => s.heap
          let s' := pushTrace { s with expr := .lit (.bool true), heap := heap' } .silent
          some (.silent, s')
      | some _ =>
          let s' := pushTrace { s with expr := .lit (.bool true) } .silent
          some (.silent, s')
  -- ECMA-262 §12.3.3 new operator (simplified: allocate empty object).
  | .newObj _callee _args =>
      let addr := s.heap.nextAddr
      let heap' := { objects := s.heap.objects.push [], nextAddr := addr + 1 }
      let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
      some (.silent, s')
  -- ECMA-262 §14.4.14 yield: simplified — evaluate argument and return it.
  | .yield arg _delegate =>
      match arg with
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | none =>
              match step? { s with expr := e } with
              | some (t, sa) =>
                  let s' := pushTrace { sa with expr := .yield (some sa.expr) _delegate, trace := s.trace } t
                  some (t, s')
              | none => none
      | none =>
          let s' := pushTrace { s with expr := .lit .undefined } .silent
          some (.silent, s')
  -- ECMA-262 §14.7.14 await: simplified — evaluate argument and return it.
  | .await arg =>
      match exprValue? arg with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          match step? { s with expr := arg } with
          | some (t, sa) =>
              let s' := pushTrace { sa with expr := .await sa.expr, trace := s.trace } t
              some (t, s')
          | none => none
  termination_by s.expr.depth
  decreasing_by all_goals (try cases ‹Option Expr›) <;> simp_all [Expr.depth] <;> omega
/-- Small-step relation induced by `step?`.
    ECMA-262 §8.3 execution context stepping. -/
inductive Step : State → TraceEvent → State → Prop where
  | mk {s : State} {t : TraceEvent} {s' : State} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of Core steps with trace accumulation. -/
inductive Steps : State → List TraceEvent → State → Prop where
  | refl (s : State) : Steps s [] s
  | tail {s1 s2 s3 : State} {t : TraceEvent} {ts : List TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Initial Core machine state for a program body.
    Preloads the `console` global with a `log` method (§18.2). -/
def initialState (p : Program) : State :=
  -- Reserve heap address 0 for the console object.
  let consoleProps : List (PropName × Value) := [("log", .function consoleLogIdx)]
  let heap : Heap := { objects := #[consoleProps], nextAddr := 1 }
  -- Reserve function index 0 for the console.log built-in.
  let logBuiltin : FuncClosure := ⟨some "log", ["__arg__"], .lit .undefined, []⟩
  let env := Env.empty.extend "console" (.object 0)
  { expr := p.body, env := env, heap := heap, trace := []
  , funcs := #[logBuiltin], callStack := [] }

/-- Program behavior as finite terminating trace sequence. -/
def Behaves (p : Program) (b : List TraceEvent) : Prop :=
  ∃ sFinal,
    Steps (initialState p) b sFinal ∧
    step? sFinal = none

end VerifiedJS.Core
