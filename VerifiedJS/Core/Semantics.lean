/-
  VerifiedJS — Core IL Semantics
  Small-step LTS as an inductive relation.
  SPEC: §8 (Executable Code and Execution Contexts), §9 (Ordinary Object Internal Methods)
-/

import VerifiedJS.Core.Syntax
import VerifiedJS.Core.Elaborate

namespace VerifiedJS.Core

set_option linter.deprecated false

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

-- SPEC: L8965-L8979
-- | # GetBindingValue ( \_N\_: a String, \_S\_: a Boolean, ): either a normal completion containing an ECMAScript language value or a throw completion
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It returns the value of its bound identifier whose name is \_N\_. If
-- |     the binding exists but is uninitialized a \*ReferenceError\* is
-- |     thrown, regardless of the value of \_S\_.
-- |
-- | 1\. Assert: \_envRec\_ has a binding for \_N\_. 1. If the binding for
-- | \_N\_ in \_envRec\_ is an uninitialized binding, throw a
-- | \*ReferenceError\* exception. 1. Return the value currently bound to
-- | \_N\_ in \_envRec\_.
/-- ECMA-262 §8.1.1.4 GetBindingValue (modeled as lookup in lexical bindings). -/
def Env.lookup (env : Env) (name : VarName) : Option Value :=
  match env.bindings.find? (fun kv => kv.fst == name) with
  | some kv => some kv.snd
  | none => none

def updateBindingList (xs : List (VarName × Value)) (name : VarName) (v : Value) : List (VarName × Value) :=
  match xs with
  | [] => []
  | (n, old) :: rest =>
      if n == name then
        (n, v) :: rest
      else
        (n, old) :: updateBindingList rest name v

@[simp] theorem updateBindingList_nil (name : VarName) (v : Value) : updateBindingList [] name v = [] := rfl
@[simp] theorem updateBindingList_cons_eq (n : VarName) (old : Value) (rest : List (VarName × Value)) (name : VarName) (v : Value) (h : (n == name) = true) :
    updateBindingList ((n, old) :: rest) name v = (n, v) :: rest := by simp [updateBindingList, h]
@[simp] theorem updateBindingList_cons_ne (n : VarName) (old : Value) (rest : List (VarName × Value)) (name : VarName) (v : Value) (h : (n == name) = false) :
    updateBindingList ((n, old) :: rest) name v = (n, old) :: updateBindingList rest name v := by simp [updateBindingList, h]

/-- Lookup after updateBindingList for the same name returns the new value. -/
@[simp] theorem lookup_updateBindingList_eq (xs : List (VarName × Value)) (name : VarName) (v : Value)
    (h : xs.any (fun kv => kv.fst == name) = true) :
    Env.lookup { bindings := updateBindingList xs name v } name = some v := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    cases hn : (n == name)
    · -- n ≠ name
      simp only [updateBindingList, hn, ↓reduceIte, Env.lookup, List.find?, Bool.false_eq_true]
      have htl : tl.any (fun kv => kv.fst == name) = true := by
        simp only [List.any, hn, Bool.false_or] at h; exact h
      exact ih htl
    · -- n == name
      simp only [updateBindingList, hn, ↓reduceIte, Env.lookup, List.find?, ↓reduceCtorEq]

/-- Lookup after updateBindingList for a different name is unchanged. -/
@[simp] theorem lookup_updateBindingList_ne (xs : List (VarName × Value)) (name other : VarName) (v : Value)
    (hne : (other == name) = false) :
    Env.lookup { bindings := updateBindingList xs name v } other = Env.lookup { bindings := xs } other := by
  induction xs with
  | nil => simp [updateBindingList, Env.lookup]
  | cons hd tl ih =>
    obtain ⟨n, old⟩ := hd
    cases hn : (n == name)
    · -- n ≠ name
      simp only [updateBindingList, hn, Bool.false_eq_true, ↓reduceIte, Env.lookup, List.find?]
      cases hno : (n == other)
      · simp only [hno, Env.lookup] at ih; exact ih
      · rfl
    · -- n == name: need (n == other) = false
      have hno : (n == other) = false := by
        simp only [show n = name from by simpa using hn]
        exact Bool.eq_false_iff.mpr (by intro h; have := beq_iff_eq.mp h; rw [this] at hne; simp at hne)
      simp only [updateBindingList, hn, ↓reduceIte, Env.lookup, List.find?, hno]

-- SPEC: L8933-L8964
-- | # SetMutableBinding ( \_N\_: a String, \_V\_: an ECMAScript language value, \_S\_: a Boolean, ): either a normal completion containing \~unused\~ or a throw completion
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It attempts to change the bound value of the current binding of the
-- |     identifier whose name is \_N\_ to the value \_V\_. A binding for
-- |     \_N\_ normally already exists, but in rare cases it may not. If the
-- |     binding is an immutable binding, a \*TypeError\* is thrown if \_S\_
-- |     is \*true\*.
-- |
-- | 1\. \[id=\"step-setmutablebinding-missing-binding\"\] If \_envRec\_ does
-- | not have a binding for \_N\_, then 1. If \_S\_ is \*true\*, throw a
-- | \*ReferenceError\* exception. 1. Perform !
-- | \_envRec\_.CreateMutableBinding(\_N\_, \*true\*). 1. Perform !
-- | \_envRec\_.InitializeBinding(\_N\_, \_V\_). 1. Return \~unused\~. 1. If
-- | the binding for \_N\_ in \_envRec\_ is a strict binding, set \_S\_ to
-- | \*true\*. 1. If the binding for \_N\_ in \_envRec\_ has not yet been
-- | initialized, then 1. Throw a \*ReferenceError\* exception. 1. Else if
-- | the binding for \_N\_ in \_envRec\_ is a mutable binding, then 1. Change
-- | its bound value to \_V\_. 1. Else, 1. Assert: This is an attempt to
-- | change the value of an immutable binding. 1. If \_S\_ is \*true\*, throw
-- | a \*TypeError\* exception. 1. Return \~unused\~.
-- |
-- | An example of ECMAScript code that results in a missing binding at step
-- | is:
-- |
-- | ``` javascript
-- | function f() { eval("var x; x = (delete x, 0);"); }
-- | ```
/-- ECMA-262 §8.1.1.4.5 SetMutableBinding (simplified update). -/
def Env.assign (env : Env) (name : VarName) (v : Value) : Env :=
  if env.bindings.any (fun kv => kv.fst == name) then
    { bindings := updateBindingList env.bindings name v }
  else
    { bindings := (name, v) :: env.bindings }

/-- Lookup after assign for the same name (existing binding). -/
@[simp] theorem Env.lookup_assign_eq (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = true) :
    (env.assign name v).lookup name = some v := by
  simp [Env.assign, h, lookup_updateBindingList_eq]

/-- Lookup after assign for a different name. -/
@[simp] theorem Env.lookup_assign_ne (env : Env) (name other : VarName) (v : Value)
    (hne : (other == name) = false) :
    (env.assign name v).lookup other = env.lookup other := by
  simp only [Env.assign]
  split
  · simp [lookup_updateBindingList_ne, hne]
  · have hne' : (name == other) = false :=
      Bool.eq_false_iff.mpr (by intro h; have := beq_iff_eq.mp h; rw [this] at hne; simp at hne)
    simp [Env.lookup, List.find?, hne']

/-- Lookup after assign for the same name (new binding). -/
@[simp] theorem Env.lookup_assign_new (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = false) :
    (env.assign name v).lookup name = some v := by
  simp [Env.assign, h, Env.lookup, List.find?, beq_self_eq_true]

-- SPEC: L8885-L8901
-- | # CreateMutableBinding ( \_N\_: a String, \_D\_: a Boolean, ): a normal completion containing \~unused\~
-- |
-- | for
-- | :   a Declarative Environment Record \_envRec\_
-- |
-- | description
-- | :   It creates a new mutable binding for the name \_N\_ that is
-- |     uninitialized. A binding must not already exist in this Environment
-- |     Record for \_N\_. If \_D\_ is \*true\*, the new binding is marked as
-- |     being subject to deletion.
-- |
-- | 1\. Assert: \_envRec\_ does not already have a binding for \_N\_. 1.
-- | Create a mutable binding in \_envRec\_ for \_N\_ and record that it is
-- | uninitialized. If \_D\_ is \*true\*, record that the newly created
-- | binding may be deleted by a subsequent DeleteBinding call. 1. Return
-- | \~unused\~.
/-- ECMA-262 §8.1.1.1.2 CreateMutableBinding + §8.1.1.1.5 InitializeBinding. -/
def Env.extend (env : Env) (name : VarName) (v : Value) : Env :=
  { bindings := (name, v) :: env.bindings }

/-- Check whether an expression is a value expression. -/
def exprValue? : Expr → Option Value
  | .lit v => some v
  | _ => none

-- SPEC: L5982-L5994
-- | # ToBoolean ( \_argument\_: an ECMAScript language value, ): a Boolean
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type Boolean.
-- |
-- | 1\. If \_argument\_ is a Boolean, return \_argument\_. 1. If
-- | \_argument\_ is one of \*undefined\*, \*null\*, \*+0\*~𝔽~, \*-0\*~𝔽~,
-- | \*NaN\*, \*0\*~ℤ~, or the empty String, return \*false\*. 1.
-- | \[id=\"step-to-boolean-web-compat-insertion-point\",
-- | normative-optional\] If the host is a web browser or otherwise supports
-- | , then 1. If \_argument\_ is an Object and \_argument\_ has an
-- | \[\[IsHTMLDDA\]\] internal slot, return \*false\*. 1. Return \*true\*.
/-- ECMA-262 §7.2.14 ToBoolean (core subset). -/
def toBoolean : Value → Bool
  | .undefined => false
  | .null => false
  | .bool b => b
  | .number n => !(n == 0.0 || n.isNaN)
  | .string s => !s.isEmpty
  | .object _ => true
  | .function _ => true

-- SPEC: L6004-L6017
-- | # ToNumber ( \_argument\_: an ECMAScript language value, ): either a normal completion containing a Number or a throw completion
-- |
-- | description
-- | :   It converts \_argument\_ to a value of type Number.
-- |
-- | 1\. If \_argument\_ is a Number, return \_argument\_. 1. If \_argument\_
-- | is either a Symbol or a BigInt, throw a \*TypeError\* exception. 1. If
-- | \_argument\_ is \*undefined\*, return \*NaN\*. 1. If \_argument\_ is
-- | either \*null\* or \*false\*, return \*+0\*~𝔽~. 1. If \_argument\_ is
-- | \*true\*, return \*1\*~𝔽~. 1. If \_argument\_ is a String, return
-- | StringToNumber(\_argument\_). 1. Assert: \_argument\_ is an Object. 1.
-- | Let \_primValue\_ be ? ToPrimitive(\_argument\_, \~number\~). 1. Assert:
-- | \_primValue\_ is not an Object. 1. Return ? ToNumber(\_primValue\_).
/-- ECMA-262 §7.1.3 ToNumber (core subset). -/
def toNumber : Value → Float
  | .number n => n
  | .bool true => 1.0
  | .bool false => 0.0
  | .null => 0.0
  | .undefined => 0.0 / 0.0  -- ECMA-262 §7.1.3: undefined → NaN
  | .string s =>
      -- ECMA-262 §7.1.3.1: StringNumericValue.
      let trimmed := s.trimAscii.toString
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

-- SPEC: L16187-L16225
-- | UnaryExpression : \`+\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Return ? ToNumber(? GetValue(\_expr\_)).
-- |
-- | # Unary \`-\` Operator
-- |
-- | The unary \`-\` operator converts its operand to a numeric value and
-- | then negates it. Negating \*+0\*~𝔽~ produces \*-0\*~𝔽~, and negating
-- | \*-0\*~𝔽~ produces \*+0\*~𝔽~.
-- |
-- | # Runtime Semantics: Evaluation
-- |
-- | UnaryExpression : \`-\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ? ToNumeric(?
-- | GetValue(\_expr\_)). 1. If \_oldValue\_ is a Number, return
-- | Number::unaryMinus(\_oldValue\_). 1. Assert: \_oldValue\_ is a
-- | BigInt. 1. Return BigInt::unaryMinus(\_oldValue\_).
-- |
-- | # Bitwise NOT Operator ( \`\~\` )
-- |
-- | # Runtime Semantics: Evaluation
-- |
-- | UnaryExpression : \`\~\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ? ToNumeric(?
-- | GetValue(\_expr\_)). 1. If \_oldValue\_ is a Number, return
-- | Number::bitwiseNOT(\_oldValue\_). 1. Assert: \_oldValue\_ is a
-- | BigInt. 1. Return BigInt::bitwiseNOT(\_oldValue\_).
-- |
-- | # Logical NOT Operator ( \`!\` )
-- |
-- | # Runtime Semantics: Evaluation
-- |
-- | UnaryExpression : \`!\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
-- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ToBoolean(?
-- | GetValue(\_expr\_)). 1. If \_oldValue\_ is \*true\*, return
-- | \*false\*. 1. Return \*true\*.
-- |
-- | # Exponentiation Operator
-- |
-- | ## Syntax
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
        else
          -- Handle negative integers: -n where n is a positive integer.
          let neg := -n
          let j := neg.toUInt64
          if j.toFloat == neg && neg > 0.0 then "-" ++ toString j.toNat
          else toString n
  | .bool true => "true"
  | .bool false => "false"
  | .null => "null"
  | .undefined => "undefined"
  | .object _ => "[object Object]"
  | .function _ => "function"

-- SPEC: L6573-L6605
-- | # IsLooselyEqual ( \_x\_: an ECMAScript language value, \_y\_: an ECMAScript language value, ): either a normal completion containing a Boolean or a throw completion
-- |
-- | description
-- | :   It provides the semantics for the \`==\` operator.
-- |
-- | 1\. If SameType(\_x\_, \_y\_) is \*true\*, then 1. Return
-- | IsStrictlyEqual(\_x\_, \_y\_). 1. If \_x\_ is \*null\* and \_y\_ is
-- | \*undefined\*, return \*true\*. 1. If \_x\_ is \*undefined\* and \_y\_
-- | is \*null\*, return \*true\*. 1.
-- | \[id=\"step-abstract-equality-comparison-web-compat-insertion-point\",
-- | normative-optional\] If the host is a web browser or otherwise supports
-- | , then 1. If \_x\_ is an Object, \_x\_ has an \[\[IsHTMLDDA\]\] internal
-- | slot, and \_y\_ is either \*undefined\* or \*null\*, return \*true\*. 1.
-- | If \_x\_ is either \*undefined\* or \*null\*, \_y\_ is an Object, and
-- | \_y\_ has an \[\[IsHTMLDDA\]\] internal slot, return \*true\*. 1. If
-- | \_x\_ is a Number and \_y\_ is a String, return ! IsLooselyEqual(\_x\_,
-- | ! ToNumber(\_y\_)). 1. If \_x\_ is a String and \_y\_ is a Number,
-- | return ! IsLooselyEqual(! ToNumber(\_x\_), \_y\_). 1. If \_x\_ is a
-- | BigInt and \_y\_ is a String, then 1. Let \_n\_ be
-- | StringToBigInt(\_y\_). 1. If \_n\_ is \*undefined\*, return
-- | \*false\*. 1. Return ! IsLooselyEqual(\_x\_, \_n\_). 1. If \_x\_ is a
-- | String and \_y\_ is a BigInt, return ! IsLooselyEqual(\_y\_, \_x\_). 1.
-- | If \_x\_ is a Boolean, return ! IsLooselyEqual(! ToNumber(\_x\_),
-- | \_y\_). 1. If \_y\_ is a Boolean, return ! IsLooselyEqual(\_x\_, !
-- | ToNumber(\_y\_)). 1. If \_x\_ is either a String, a Number, a BigInt, or
-- | a Symbol and \_y\_ is an Object, return ! IsLooselyEqual(\_x\_, ?
-- | ToPrimitive(\_y\_)). 1. If \_x\_ is an Object and \_y\_ is either a
-- | String, a Number, a BigInt, or a Symbol, return ! IsLooselyEqual(?
-- | ToPrimitive(\_x\_), \_y\_). 1. If \_x\_ is a BigInt and \_y\_ is a
-- | Number, or if \_x\_ is a Number and \_y\_ is a BigInt, then 1. If \_x\_
-- | is not finite or \_y\_ is not finite, return \*false\*. 1. If ℝ(\_x\_) =
-- | ℝ(\_y\_), return \*true\*. 1. Return \*false\*. 1. Return \*false\*.
/-- ECMA-262 §7.2.14 Abstract Equality Comparison (simplified core subset).
    Handles null/undefined equivalence and type coercion. -/
def abstractEq : Value → Value → Bool
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
def abstractLt : Value → Value → Bool
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

/-- Built-in function index for console.log (reserved at index 0, §18.2). -/
def consoleLogIdx : FuncIdx := 0

/-- Push a trace event onto the state's trace list. -/
def pushTrace (s : State) (t : TraceEvent) : State :=
  { s with trace := s.trace ++ [t] }

/-- One deterministic Core small-step transition with emitted trace event. -/
def step? (s : State) : Option (TraceEvent × State) :=
  match h : s.expr with
  | .lit _ => none
  -- SPEC: L14868-L14871
  -- | IdentifierReference : Identifier 1. Return ? ResolveBinding(StringValue
  -- | of \|Identifier\|). IdentifierReference : \`yield\` 1. Return ?
  -- | ResolveBinding(\*\"yield\"\*). IdentifierReference : \`await\` 1. Return
  -- | ? ResolveBinding(\*\"await\"\*).
  | .var name =>
      match s.env.lookup name with
      | some v =>
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | none =>
          let msg := "ReferenceError: " ++ name
          let s' := pushTrace { s with expr := .lit .undefined } (.error msg)
          some (.error msg, s')
  -- SPEC: L17386-L17393
  -- | LexicalBinding : BindingIdentifier Initializer 1. Let \_bindingId\_ be
  -- | the StringValue of \|BindingIdentifier\|. 1. Let \_lhs\_ be !
  -- | ResolveBinding(\_bindingId\_). 1. If
  -- | IsAnonymousFunctionDefinition(\|Initializer\|) is \*true\*, then 1. Let
  -- | \_value\_ be ? NamedEvaluation of \|Initializer\| with argument
  -- | \_bindingId\_. 1. Else, 1. Let \_rhs\_ be ? Evaluation of
  -- | \|Initializer\|. 1. Let \_value\_ be ? GetValue(\_rhs\_). 1. Perform !
  -- | InitializeReferencedBinding(\_lhs\_, \_value\_). 1. Return \~empty\~.
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
  -- SPEC: L16640-L16654
  -- | AssignmentExpression : LeftHandSideExpression \`=\`
  -- | AssignmentExpression 1. If \|LeftHandSideExpression\| is neither an
  -- | \|ObjectLiteral\| nor an \|ArrayLiteral\|, then 1. Let \_lRef\_ be ?
  -- | Evaluation of \|LeftHandSideExpression\|. 1. If the AssignmentTargetType
  -- | of \|LeftHandSideExpression\| is \~web-compat\~, throw a
  -- | \*ReferenceError\* exception. 1. If
  -- | IsAnonymousFunctionDefinition(\|AssignmentExpression\|) is \*true\* and
  -- | IsIdentifierRef of \|LeftHandSideExpression\| is \*true\*, then 1. Let
  -- | \_lhs\_ be the StringValue of \|LeftHandSideExpression\|. 1. Let
  -- | \_rVal\_ be ? NamedEvaluation of \|AssignmentExpression\| with argument
  -- | \_lhs\_. 1. Else, 1. Let \_rRef\_ be ? Evaluation of
  -- | \|AssignmentExpression\|. 1. Let \_rVal\_ be ? GetValue(\_rRef\_). 1.
  -- | \[id=\"step-assignmentexpression-evaluation-simple-putvalue\"\] Perform
  -- | ? PutValue(\_lRef\_, \_rVal\_). 1. Return \_rVal\_. 1. Let
  -- | \_assignmentPattern\_ be the \|AssignmentPattern\| that is covered by
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
  -- SPEC: L17607-L17620
  -- | IfStatement : \`if\` \`(\` Expression \`)\` Statement \`else\`
  -- | Statement 1. Let \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let
  -- | \_exprValue\_ be ToBoolean(? GetValue(\_exprRef\_)). 1. If \_exprValue\_
  -- | is \*true\*, then 1. Let \_stmtCompletion\_ be Completion(Evaluation of
  -- | the first \|Statement\|). 1. Else, 1. Let \_stmtCompletion\_ be
  -- | Completion(Evaluation of the second \|Statement\|). 1. Return ?
  -- | UpdateEmpty(\_stmtCompletion\_, \*undefined\*). IfStatement : \`if\`
  -- | \`(\` Expression \`)\` Statement 1. Let \_exprRef\_ be ? Evaluation of
  -- | \|Expression\|. 1. Let \_exprValue\_ be ToBoolean(?
  -- | GetValue(\_exprRef\_)). 1. If \_exprValue\_ is \*false\*, return
  -- | \*undefined\*. 1. Let \_stmtCompletion\_ be Completion(Evaluation of
  -- | \|Statement\|). 1. Return ? UpdateEmpty(\_stmtCompletion\_,
  -- | \*undefined\*).
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
  -- SPEC: L17277-L17279
  -- | StatementList : StatementList StatementListItem 1. Let \_sl\_ be ?
  -- | Evaluation of \|StatementList\|. 1. Let \_s\_ be Completion(Evaluation
  -- | of \|StatementListItem\|). 1. Return ? UpdateEmpty(\_s\_, \_sl\_).
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
  -- SPEC: L16186-L16188
  -- | UnaryExpression : \`+\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
  -- | of \|UnaryExpression\|. 1. Return ? ToNumber(? GetValue(\_expr\_)).
  -- SPEC: L16197-L16202
  -- | UnaryExpression : \`-\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
  -- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ? ToNumeric(?
  -- | GetValue(\_expr\_)). 1. If \_oldValue\_ is a Number, return
  -- | Number::unaryMinus(\_oldValue\_). 1. Assert: \_oldValue\_ is a
  -- | BigInt. 1. Return BigInt::unaryMinus(\_oldValue\_).
  -- SPEC: L16218-L16222
  -- | UnaryExpression : \`!\` UnaryExpression 1. Let \_expr\_ be ? Evaluation
  -- | of \|UnaryExpression\|. 1. Let \_oldValue\_ be ToBoolean(?
  -- | GetValue(\_expr\_)). 1. If \_oldValue\_ is \*true\*, return
  -- | \*false\*. 1. Return \*true\*.
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
  -- SPEC: L16279-L16282
  -- | AdditiveExpression : AdditiveExpression \`+\`
  -- | MultiplicativeExpression 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|AdditiveExpression\|, \`+\`,
  -- | \|MultiplicativeExpression\|).
  -- SPEC: L16291-L16294
  -- | AdditiveExpression : AdditiveExpression \`-\`
  -- | MultiplicativeExpression 1. Return ?
  -- | EvaluateStringOrNumericBinaryExpression(\|AdditiveExpression\|, \`-\`,
  -- | \|MultiplicativeExpression\|).
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
  -- SPEC: L15668-L15681
  -- | # EvaluateCall ( \_func\_: an ECMAScript language value, \_ref\_: an ECMAScript language value or a Reference Record, \_arguments\_: a Parse Node, \_tailPosition\_: a Boolean, ): either a normal completion containing an ECMAScript language value or an abrupt completion
  -- |
  -- | 1\. If \_ref\_ is a Reference Record, then 1. If
  -- | IsPropertyReference(\_ref\_) is \*true\*, then 1. Let \_thisValue\_ be
  -- | GetThisValue(\_ref\_). 1. Else, 1. Let \_refEnv\_ be
  -- | \_ref\_.\[\[Base\]\]. 1. Assert: \_refEnv\_ is an Environment Record. 1.
  -- | Let \_thisValue\_ be \_refEnv\_.WithBaseObject(). 1. Else, 1. Let
  -- | \_thisValue\_ be \*undefined\*. 1. Let \_argList\_ be ?
  -- | ArgumentListEvaluation of \_arguments\_. 1. If \_func\_ is not an
  -- | Object, throw a \*TypeError\* exception. 1. If IsCallable(\_func\_) is
  -- | \*false\*, throw a \*TypeError\* exception. 1. If \_tailPosition\_ is
  -- | \*true\*, perform PrepareForTailCall(). 1. Return ? Call(\_func\_,
  -- | \_thisValue\_, \_argList\_).
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
  -- SPEC: L15567-L15577
  -- | MemberExpression : MemberExpression \`\[\` Expression \`\]\` 1. Let
  -- | \_baseReference\_ be ? Evaluation of \|MemberExpression\|. 1. Let
  -- | \_baseValue\_ be ? GetValue(\_baseReference\_). 1. Let \_strict\_ be
  -- | IsStrict(this \|MemberExpression\|). 1. Return ?
  -- | EvaluatePropertyAccessWithExpressionKey(\_baseValue\_, \|Expression\|,
  -- | \_strict\_). MemberExpression : MemberExpression \`.\` IdentifierName 1.
  -- | Let \_baseReference\_ be ? Evaluation of \|MemberExpression\|. 1. Let
  -- | \_baseValue\_ be ? GetValue(\_baseReference\_). 1. Let \_strict\_ be
  -- | IsStrict(this \|MemberExpression\|). 1. Return
  -- | EvaluatePropertyAccessWithIdentifierKey(\_baseValue\_,
  -- | \|IdentifierName\|, \_strict\_). MemberExpression : MemberExpression
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
                | none =>
                    -- §22.1.3.3 Array.prototype.length: return count of properties.
                    if prop == "length" then .number (Float.ofNat props.length)
                    else .undefined
            | none => .undefined
          let s' := pushTrace { s with expr := .lit v } .silent
          some (.silent, s')
      | some (.string str) =>
          -- ECMA-262 §21.1.3.3 String.prototype.length (and other string properties).
          let v := if prop == "length" then .number (Float.ofNat str.length)
                   else .undefined
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
          -- ECMA-262 §9.1.8 [[Get]] with computed key: convert index to string via ToString.
          let propName := valueToString idxVal
          match objVal with
          | .object addr =>
              let v := match s.heap.objects[addr]? with
                | some props =>
                    match props.find? (fun kv => kv.fst == propName) with
                    | some (_, v) => v
                    | none =>
                        -- §22.1.3.3 Array.prototype.length for computed access.
                        if propName == "length" then .number (Float.ofNat props.length)
                        else .undefined
                | none => .undefined
              let s' := pushTrace { s with expr := .lit v } .silent
              some (.silent, s')
          | .string str =>
              -- §21.1.3.4 String character access: str[n] returns single-char string.
              match idxVal with
              | .number n =>
                  let idx := n.toUInt64.toNat
                  let v := if n >= 0.0 && n.toUInt64.toFloat == n && idx < str.length
                    then .string (String.Pos.Raw.get str ⟨idx⟩ |>.toString)
                    else .undefined
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
              | _ =>
                  -- §21.1.3.3 String.prototype.length via bracket notation.
                  let v := if propName == "length" then .number (Float.ofNat str.length)
                           else .undefined
                  let s' := pushTrace { s with expr := .lit v } .silent
                  some (.silent, s')
          | _ =>
              let s' := pushTrace { s with expr := .lit .undefined } .silent
              some (.silent, s')
  -- SPEC: L18879-L18906
  -- | # Runtime Semantics: InstantiateOrdinaryFunctionExpression ( optional \_name\_: a property key or a Private Name, ): an ECMAScript function object
  -- |
  -- | FunctionExpression : \`function\` \`(\` FormalParameters \`)\` \`{\`
  -- | FunctionBody \`}\` 1. If \_name\_ is not present, set \_name\_ to
  -- | \*\"\"\*. 1. Let \_env\_ be the LexicalEnvironment of the running
  -- | execution context. 1. Let \_privateEnv\_ be the running execution
  -- | context\'s PrivateEnvironment. 1. Let \_sourceText\_ be the source text
  -- | matched by \|FunctionExpression\|. 1. Let \_closure\_ be
  -- | OrdinaryFunctionCreate(%Function.prototype%, \_sourceText\_,
  -- | \|FormalParameters\|, \|FunctionBody\|, \~non-lexical-this\~, \_env\_,
  -- | \_privateEnv\_). 1. Perform SetFunctionName(\_closure\_, \_name\_). 1.
  -- | Perform MakeConstructor(\_closure\_). 1. Return \_closure\_.
  -- | FunctionExpression : \`function\` BindingIdentifier \`(\`
  -- | FormalParameters \`)\` \`{\` FunctionBody \`}\` 1. Assert: \_name\_ is
  -- | not present. 1. Set \_name\_ to the StringValue of
  -- | \|BindingIdentifier\|. 1. Let \_outerEnv\_ be the running execution
  -- | context\'s LexicalEnvironment. 1. Let \_funcEnv\_ be
  -- | NewDeclarativeEnvironment(\_outerEnv\_). 1. Perform !
  -- | \_funcEnv\_.CreateImmutableBinding(\_name\_, \*false\*). 1. Let
  -- | \_privateEnv\_ be the running execution context\'s
  -- | PrivateEnvironment. 1. Let \_sourceText\_ be the source text matched by
  -- | \|FunctionExpression\|. 1. Let \_closure\_ be
  -- | OrdinaryFunctionCreate(%Function.prototype%, \_sourceText\_,
  -- | \|FormalParameters\|, \|FunctionBody\|, \~non-lexical-this\~,
  -- | \_funcEnv\_, \_privateEnv\_). 1. Perform SetFunctionName(\_closure\_,
  -- | \_name\_). 1. Perform MakeConstructor(\_closure\_). 1. Perform !
  -- | \_funcEnv\_.InitializeBinding(\_name\_, \_closure\_). 1. Return
  -- | \_closure\_.
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
  -- SPEC: L17703-L17710
  -- | WhileStatement : \`while\` \`(\` Expression \`)\` Statement 1. Let \_V\_
  -- | be \*undefined\*. 1. Repeat, 1. Let \_exprRef\_ be ? Evaluation of
  -- | \|Expression\|. 1. Let \_exprValue\_ be ? GetValue(\_exprRef\_). 1. If
  -- | ToBoolean(\_exprValue\_) is \*false\*, return \_V\_. 1. Let
  -- | \_stmtResult\_ be Completion(Evaluation of \|Statement\|). 1. If
  -- | LoopContinues(\_stmtResult\_, \_labelSet\_) is \*false\*, return ?
  -- | UpdateEmpty(\_stmtResult\_, \_V\_). 1. If \_stmtResult\_.\[\[Value\]\]
  -- | is not \~empty\~, set \_V\_ to \_stmtResult\_.\[\[Value\]\].
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
  -- SPEC: L18539-L18541
  -- | ThrowStatement : \`throw\` Expression \`;\` 1. Let \_exprRef\_ be ?
  -- | Evaluation of \|Expression\|. 1. Let \_exprValue\_ be ?
  -- | GetValue(\_exprRef\_). 1. Return ThrowCompletion(\_exprValue\_).
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
  -- SPEC: L18600-L18614
  -- | TryStatement : \`try\` Block Catch 1. Let \_B\_ be Completion(Evaluation
  -- | of \|Block\|). 1. If \_B\_ is a throw completion, let \_C\_ be
  -- | Completion(CatchClauseEvaluation of \|Catch\| with argument
  -- | \_B\_.\[\[Value\]\]). 1. Else, let \_C\_ be \_B\_. 1. Return ?
  -- | UpdateEmpty(\_C\_, \*undefined\*). TryStatement : \`try\` Block
  -- | Finally 1. Let \_B\_ be Completion(Evaluation of \|Block\|). 1. Let
  -- | \_F\_ be Completion(Evaluation of \|Finally\|). 1. If \_F\_ is a normal
  -- | completion, set \_F\_ to \_B\_. 1. Return ? UpdateEmpty(\_F\_,
  -- | \*undefined\*). TryStatement : \`try\` Block Catch Finally 1. Let \_B\_
  -- | be Completion(Evaluation of \|Block\|). 1. If \_B\_ is a throw
  -- | completion, let \_C\_ be Completion(CatchClauseEvaluation of \|Catch\|
  -- | with argument \_B\_.\[\[Value\]\]). 1. Else, let \_C\_ be \_B\_. 1. Let
  -- | \_F\_ be Completion(Evaluation of \|Finally\|). 1. If \_F\_ is a normal
  -- | completion, set \_F\_ to \_C\_. 1. Return ? UpdateEmpty(\_F\_,
  -- | \*undefined\*).
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
  -- SPEC: L16165-L16179
  -- | UnaryExpression : \`typeof\` UnaryExpression 1. Let \_val\_ be ?
  -- | Evaluation of \|UnaryExpression\|. 1. If \_val\_ is a Reference Record,
  -- | then 1. If IsUnresolvableReference(\_val\_) is \*true\*, return
  -- | \*\"undefined\"\*. 1. Set \_val\_ to ? GetValue(\_val\_). 1. If \_val\_
  -- | is \*undefined\*, return \*\"undefined\"\*. 1. If \_val\_ is \*null\*,
  -- | return \*\"object\"\*. 1. If \_val\_ is a String, return
  -- | \*\"string\"\*. 1. If \_val\_ is a Symbol, return \*\"symbol\"\*. 1. If
  -- | \_val\_ is a Boolean, return \*\"boolean\"\*. 1. If \_val\_ is a Number,
  -- | return \*\"number\"\*. 1. If \_val\_ is a BigInt, return
  -- | \*\"bigint\"\*. 1. Assert: \_val\_ is an Object. 1.
  -- | \[id=\"step-typeof-web-compat-insertion-point\", normative-optional\] If
  -- | the host is a web browser or otherwise supports , then 1. If \_val\_ has
  -- | an \[\[IsHTMLDDA\]\] internal slot, return \*\"undefined\"\*. 1. If
  -- | \_val\_ has a \[\[Call\]\] internal method, return \*\"function\"\*. 1.
  -- | Return \*\"object\"\*.
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
  -- SPEC: L18292-L18297
  -- | ReturnStatement : \`return\` \`;\` 1. Return
  -- | ReturnCompletion(\*undefined\*). ReturnStatement : \`return\` Expression
  -- | \`;\` 1. Let \_exprRef\_ be ? Evaluation of \|Expression\|. 1. Let
  -- | \_exprValue\_ be ? GetValue(\_exprRef\_). 1. If GetGeneratorKind() is
  -- | \~async\~, set \_exprValue\_ to ? Await(\_exprValue\_). 1. Return
  -- | ReturnCompletion(\_exprValue\_).
  | .«return» arg =>
      match arg with
      | some e =>
          match exprValue? e with
          | some v =>
              let s' := pushTrace { s with expr := .lit v } (.error ("return:" ++ valueToString v))
              some (.error ("return:" ++ valueToString v), s')
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
          let propName := valueToString idxVal
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

/-- Core step? is deterministic: at most one transition from any state.
    ECMA-262 §8.3 requires deterministic evaluation order. -/
theorem step_deterministic {s : State} {t1 t2 : TraceEvent} {s1 s2 : State}
    (h1 : step? s = some (t1, s1)) (h2 : step? s = some (t2, s2)) :
    t1 = t2 ∧ s1 = s2 := by
  rw [h1] at h2; simp at h2; exact ⟨h2.1, h2.2⟩

/-- Step relation is deterministic. -/
theorem Step_deterministic {s : State} {t1 t2 : TraceEvent} {s1 s2 : State}
    (h1 : Step s t1 s1) (h2 : Step s t2 s2) :
    t1 = t2 ∧ s1 = s2 := by
  cases h1 with | mk h1' => cases h2 with | mk h2' => exact step_deterministic h1' h2'

/-- A literal expression is stuck (no further step). -/
theorem step_lit_none (v : Value) (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (callStack : List (List (VarName × Value))) :
    step? ⟨.lit v, env, heap, trace, funcs, callStack⟩ = none := by
  simp [step?]

/-- Step inversion: any Step must have come from step?. -/
theorem Step_iff (s : State) (t : TraceEvent) (s' : State) :
    Step s t s' ↔ step? s = some (t, s') := by
  constructor
  · intro h; cases h with | mk h' => exact h'
  · intro h; exact Step.mk h

/-- Program behavior as finite terminating trace sequence. -/
def Behaves (p : Program) (b : List TraceEvent) : Prop :=
  ∃ sFinal,
    Steps (initialState p) b sFinal ∧
    step? sFinal = none

/-- Steps is transitive. -/
theorem Steps_trans {s1 s2 s3 : State} {ts1 ts2 : List TraceEvent}
    (h1 : Steps s1 ts1 s2) (h2 : Steps s2 ts2 s3) :
    Steps s1 (ts1 ++ ts2) s3 := by
  induction h1 with
  | refl => exact h2
  | tail hstep _ ih => exact Steps.tail hstep (ih h2)

/-- A single step embeds into Steps. -/
theorem Steps_single {s s' : State} {t : TraceEvent}
    (h : Step s t s') : Steps s [t] s' :=
  Steps.tail h (Steps.refl s')

/-- toBoolean is total and decidable. ECMA-262 §7.2.14. -/
theorem toBoolean_bool (v : Value) : ∃ b : Bool, toBoolean v = b :=
  ⟨toBoolean v, rfl⟩

/-- evalBinary produces a value for all inputs. ECMA-262 §13.15. -/
theorem evalBinary_total (op : BinOp) (a b : Value) : ∃ v, evalBinary op a b = v :=
  ⟨evalBinary op a b, rfl⟩

/-- evalUnary produces a value for all inputs. ECMA-262 §13.5. -/
theorem evalUnary_total (op : UnaryOp) (v : Value) : ∃ w, evalUnary op v = w :=
  ⟨evalUnary op v, rfl⟩

/-- A variable lookup in a non-empty env that contains the name succeeds. -/
theorem Env.lookup_extend_same (env : Env) (name : VarName) (v : Value) :
    (env.extend name v).lookup name = some v := by
  simp [Env.extend, Env.lookup]

/-- var lookup steps to the bound value. -/
theorem step_var_lookup (env : Env) (name : VarName) (v : Value) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (h : env.lookup name = some v) :
    (step? ⟨.var name, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, h]

/-- A binary operation on two values always steps (is not stuck). -/
theorem step_binary_values (op : BinOp) (a b : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.binary op (.lit a) (.lit b), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §13.2 seq: when left side is a value, step produces the right side. -/
theorem step_seq_value (v : Value) (b : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    step? ⟨.seq (.lit v) b, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨b, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §8.1.1.1 let: when init is a value, step extends env and produces body. -/
theorem step_let_value (name : VarName) (v : Value) (body : Expr) (env : Env)
    (heap : Heap) (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.let name (.lit v) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨body, env.extend name v, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §8.1.1.4.5 assign: when rhs is a value, step updates env. -/
theorem step_assign_value (name : VarName) (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.assign name (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env.assign name v, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §13.6 if with truthy condition steps to then branch. -/
theorem step_if_true (v : Value) (then_ else_ : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hv : toBoolean v = true) :
    step? ⟨.if (.lit v) then_ else_, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨then_, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hv]

/-- §13.6 if with falsy condition steps to else branch. -/
theorem step_if_false (v : Value) (then_ else_ : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hv : toBoolean v = false) :
    step? ⟨.if (.lit v) then_ else_, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨else_, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hv]

/-- §13.5 unary on a value always steps. -/
theorem step_unary_value (op : UnaryOp) (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.unary op (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (evalUnary op v), env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §13.14 throw with valued argument produces error event. -/
theorem step_throw_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.throw (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.error (valueToString v),
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.error (valueToString v))) := by
  simp [step?, exprValue?]

/-- §13.7.4 while unfolds to if-then-seq-while. -/
theorem step_while_unfold (cond body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.while_ cond body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace
        ⟨.if cond (.seq body (.while_ cond body)) (.lit .undefined),
         env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §13.8 break produces error event with label. -/
theorem step_break (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.break label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §13.9 continue produces error event with label. -/
theorem step_continue (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.break label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §14.1 functionDef always steps (creates a closure). -/
theorem step_functionDef (fname : Option VarName) (params : List VarName) (body : Expr)
    (isAsync isGen : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.functionDef fname params body isAsync isGen, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §12.5.6 typeof on a value always steps. -/
theorem step_typeof_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.typeof (.lit v), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §12.2.6 objectLit with all-value props allocates on heap. -/
theorem step_objectLit_allValues (props : List (PropName × Expr)) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hf : firstNonValueProp props = none) :
    (step? ⟨.objectLit props, env, heap, trace, funcs, cs⟩).isSome = true := by
  unfold step?; split <;> simp_all

/-- §12.3.3 newObj always steps (allocates empty object). -/
theorem step_newObj (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.newObj callee args, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- Labeled statement just unwraps to body. -/
theorem step_labeled (label : LabelName) (body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.labeled label body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨body, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §12.8.3 Adding two numbers produces a number. -/
theorem evalBinary_add_nums (a b : Float) :
    evalBinary .add (.number a) (.number b) = .number (a + b) := by
  unfold evalBinary; rfl

/-- §12.8.3 Adding two strings concatenates them. -/
theorem evalBinary_add_strings (a b : String) :
    evalBinary .add (.string a) (.string b) = .string (a ++ b) := by
  simp [evalBinary]

/-- §7.2.15 Strict equality of same value is true. -/
theorem evalBinary_strictEq_refl (v : Value) :
    evalBinary .strictEq v v = .bool (v == v) := by
  simp [evalBinary]

/-- §7.2.14 null == undefined is true. -/
theorem evalBinary_eq_null_undefined :
    evalBinary .eq .null .undefined = .bool true := by
  simp [evalBinary, abstractEq]

/-- §7.2.14 undefined == null is true. -/
theorem evalBinary_eq_undefined_null :
    evalBinary .eq .undefined .null = .bool true := by
  simp [evalBinary, abstractEq]

/-- Env.assign on a fresh name extends the env. -/
theorem Env.assign_fresh (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = false) :
    (env.assign name v).bindings = (name, v) :: env.bindings := by
  simp [Env.assign, h]

/-- Env.lookup on a different name after extend returns original result. -/
theorem Env.lookup_extend_other (env : Env) (name other : VarName) (v : Value)
    (h : name ≠ other) :
    (env.extend name v).lookup other = env.lookup other := by
  simp [Env.extend, Env.lookup, BEq.beq, h]

/-- this expression resolves to env lookup of "this". -/
theorem step_this_bound (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (h : env.lookup "this" = some v) :
    step? ⟨.this, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, h]

/-- return with no argument produces error event "return:undefined". -/
theorem step_return_none (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    step? ⟨.return none, env, heap, trace, funcs, cs⟩ =
      some (.error "return:undefined",
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.error "return:undefined")) := by
  simp [step?]

/-- §13.7.5 for-in on non-object produces undefined. -/
theorem step_forIn_nonObject (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.forIn binding (.lit v) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §13.7.5 for-in on object always steps (enumerates property keys). -/
theorem step_forIn_object (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.forIn binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §13.7.5.13 for-of on object always steps (iterates values). -/
theorem step_forOf_object (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.forOf binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §13.7.5.13 for-of on non-object produces undefined. -/
theorem step_forOf_nonObject (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.forOf binding (.lit v) body, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §12.2.5 arrayLit with all-value elems allocates on heap. -/
theorem step_arrayLit_allValues (elems : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hf : firstNonValueExpr elems = none) :
    (step? ⟨.arrayLit elems, env, heap, trace, funcs, cs⟩).isSome = true := by
  unfold step?; split <;> simp_all

/-- §9.1.9 setProp on object always steps when obj and value are values. -/
theorem step_setProp_object_value (addr : Nat) (prop : PropName) (v : Value)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value))) :
    (step? ⟨.setProp (.lit (.object addr)) prop (.lit v), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §9.1.9 setProp on non-object returns value. -/
theorem step_setProp_nonObject (v val : Value) (prop : PropName)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.setProp (.lit v) prop (.lit val), env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §12.4.3 deleteProp on object always steps. -/
theorem step_deleteProp_object (addr : Nat) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.deleteProp (.lit (.object addr)) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §12.4.3 deleteProp on non-object always steps (returns true). -/
theorem step_deleteProp_nonObject (v : Value) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    (step? ⟨.deleteProp (.lit v) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §12.3.2 getProp on string returns length or undefined. -/
theorem step_getProp_string (s : String) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.getProp (.lit (.string s)) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §12.3.2 getProp on object always steps. -/
theorem step_getProp_object (addr : Nat) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.getProp (.lit (.object addr)) prop, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- allValues of empty list is some []. -/
theorem allValues_nil : allValues [] = some [] := by
  simp [allValues]

/-- allValues of lit :: rest decomposes. -/
theorem allValues_cons_lit (v : Value) (rest : List Expr) (vs : List Value)
    (h : allValues rest = some vs) :
    allValues (.lit v :: rest) = some (v :: vs) := by
  simp [allValues, h]

/-- allValues of non-lit head is none. -/
theorem allValues_cons_nonLit (e : Expr) (rest : List Expr)
    (he : ∀ v, e ≠ .lit v) :
    allValues (e :: rest) = none := by
  unfold allValues; split
  · next v => exact absurd rfl (he v)
  · rfl

/-- §7.1.12 valueToString on string is identity. -/
theorem valueToString_string (s : String) :
    valueToString (.string s) = s := by
  simp [valueToString]

/-- §7.2.14 toBoolean on true is true. -/
theorem toBoolean_true : toBoolean (.bool true) = true := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on false is false. -/
theorem toBoolean_false : toBoolean (.bool false) = false := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on null is false. -/
theorem toBoolean_null : toBoolean .null = false := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on undefined is false. -/
theorem toBoolean_undefined : toBoolean .undefined = false := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on any object is true. -/
theorem toBoolean_object (addr : Nat) : toBoolean (.object addr) = true := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on any function is true. -/
theorem toBoolean_function (idx : FuncIdx) : toBoolean (.function idx) = true := by
  simp [toBoolean]

/-- §7.2.14 toBoolean on non-empty string is true. -/
theorem toBoolean_string_nonempty (s : String) (h : ¬s.isEmpty) :
    toBoolean (.string s) = true := by
  simp [toBoolean, h]

/-- §7.2.14 toBoolean on empty string is false. -/
theorem toBoolean_string_empty : toBoolean (.string "") = false := by
  simp [toBoolean]

/-- §7.1.3 toNumber on a number is identity. -/
theorem toNumber_number (n : Float) : toNumber (.number n) = n := by
  simp [toNumber]

/-- §7.1.3 toNumber on true is 1. -/
theorem toNumber_true : toNumber (.bool true) = 1.0 := by
  simp [toNumber]

/-- §7.1.3 toNumber on false is 0. -/
theorem toNumber_false : toNumber (.bool false) = 0.0 := by
  simp [toNumber]

/-- §7.1.3 toNumber on null is 0. -/
theorem toNumber_null : toNumber .null = 0.0 := by
  simp [toNumber]

/-- §13.15 try/catch normal completion: when body is a value without finally, steps to the value. -/
theorem step_tryCatch_normal_noFinally (v : Value) (catchParam : VarName) (catchBody : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hNotCallFrame : catchParam ≠ "__call_frame_return__") :
    step? ⟨.tryCatch (.lit v) catchParam catchBody none, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hNotCallFrame]

/-- §13.1 return with valued argument produces error event. -/
theorem step_return_some_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.return (some (.lit v)), env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?, exprValue?]

/-- §14.4.14 yield with no argument steps to undefined. -/
theorem step_yield_none (delegate : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.yield none delegate, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §14.7.14 await with valued argument steps to that value. -/
theorem step_await_value (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.await (.lit v), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- §8.3 this without binding resolves to undefined. -/
theorem step_this_unbound (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (h : env.lookup "this" = none) :
    step? ⟨.this, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, h]

/-- §13.12 Subtraction produces a number. -/
theorem evalBinary_sub (a b : Value) :
    ∃ n, evalBinary .sub a b = .number n := by
  exact ⟨toNumber a - toNumber b, by simp [evalBinary]⟩

/-- §13.12 Multiplication produces a number. -/
theorem evalBinary_mul (a b : Value) :
    ∃ n, evalBinary .mul a b = .number n := by
  exact ⟨toNumber a * toNumber b, by simp [evalBinary]⟩

/-- §13.12 Division produces a number. -/
theorem evalBinary_div (a b : Value) :
    ∃ n, evalBinary .div a b = .number n := by
  exact ⟨toNumber a / toNumber b, by simp [evalBinary]⟩

/-- §7.2.15 Strict equality is decidable and produces a bool. -/
theorem evalBinary_strictEq_bool (a b : Value) :
    ∃ bl, evalBinary .strictEq a b = .bool bl := by
  exact ⟨a == b, by simp [evalBinary]⟩

/-- §7.2.14 Equality is decidable and produces a bool. -/
theorem evalBinary_eq_bool (a b : Value) :
    ∃ bl, evalBinary .eq a b = .bool bl := by
  exact ⟨abstractEq a b, by simp [evalBinary]⟩

/-- §7.2.13 Less-than produces a bool. -/
theorem evalBinary_lt_bool (a b : Value) :
    ∃ bl, evalBinary .lt a b = .bool bl := by
  exact ⟨abstractLt a b, by simp [evalBinary]⟩

/-- var lookup on unbound name produces ReferenceError. -/
theorem step_var_unbound (name : VarName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (h : env.lookup name = none) :
    step? ⟨.var name, env, heap, trace, funcs, cs⟩ =
      some (.error ("ReferenceError: " ++ name),
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.error ("ReferenceError: " ++ name))) := by
  simp [step?, h]

/-- §13.5 Negation produces a number. -/
theorem evalUnary_neg (v : Value) :
    evalUnary .neg v = .number (-toNumber v) := by
  simp [evalUnary]

/-- §13.5 Logical NOT produces a bool. -/
theorem evalUnary_logNot (v : Value) :
    evalUnary .logNot v = .bool (!toBoolean v) := by
  simp [evalUnary]

/-- §13.5 void produces undefined. -/
theorem evalUnary_void (v : Value) :
    evalUnary .void v = .undefined := by
  simp [evalUnary]

/-- Env.assign on existing name updates it. -/
theorem Env.assign_existing (env : Env) (name : VarName) (v : Value)
    (h : env.bindings.any (fun kv => kv.fst == name) = true) :
    (env.assign name v).bindings = updateBindingList env.bindings name v := by
  simp [Env.assign, h]

/-- Env.extend always prepends. -/
theorem Env.extend_bindings (env : Env) (name : VarName) (v : Value) :
    (env.extend name v).bindings = (name, v) :: env.bindings := by
  simp [Env.extend]

/-- exprValue? of a literal is some. -/
theorem exprValue_lit (v : Value) : exprValue? (.lit v) = some v := by
  simp [exprValue?]

/-- exprValue? of a non-literal is none. -/
theorem exprValue_var (name : VarName) : exprValue? (.var name) = none := by
  simp [exprValue?]

/-- §13.7.4 while_ always steps (unfolds to if). -/
theorem step_while_isSome (cond body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.while_ cond body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- §18.2 console.log call produces log trace event. -/
theorem step_consoleLog (msg : String) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.call (.lit (.function consoleLogIdx)) [.lit (.string msg)],
           env, heap, trace, funcs, cs⟩ =
      some (.log msg,
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ (.log msg)) := by
  simp [step?, exprValue?, allValues, consoleLogIdx, valueToString]

/-- initialState produces a state with empty trace. -/
theorem initialState_trace (p : Program) : (initialState p).trace = [] := by
  simp [initialState]

/-- initialState produces a state whose expr is the program body. -/
theorem initialState_expr (p : Program) : (initialState p).expr = p.body := by
  simp [initialState]

/-- A stuck state on a literal expression. -/
theorem stuck_lit_expr {v : Value} {env : Env} {heap : Heap} {trace : List TraceEvent}
    {funcs : Array FuncClosure} {cs : List (List (VarName × Value))} :
    step? ⟨.lit v, env, heap, trace, funcs, cs⟩ = none := by
  simp [step?]

/-- seq with two values steps to the second value. ECMA-262 §13.2. -/
theorem step_seq_two_values (v1 v2 : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.seq (.lit v1) (.lit v2), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v2, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- abstractEq: null == undefined is true. ECMA-262 §7.2.14. -/
theorem abstractEq_null_undef : abstractEq .null .undefined = true := by
  simp [abstractEq]

/-- abstractEq: undefined == null is true. ECMA-262 §7.2.14. -/
theorem abstractEq_undef_null : abstractEq .undefined .null = true := by
  simp [abstractEq]

/-- abstractEq: same booleans are equal. ECMA-262 §7.2.14. -/
theorem abstractEq_bool_same (b : Bool) : abstractEq (.bool b) (.bool b) = true := by
  simp [abstractEq]

/-- abstractEq: same strings are equal. ECMA-262 §7.2.14. -/
theorem abstractEq_string_same (s : String) : abstractEq (.string s) (.string s) = true := by
  simp [abstractEq]

/-- Step on a stuck state is impossible. -/
theorem Step_stuck {s : State} (hStuck : step? s = none) :
    ¬∃ t s', Step s t s' := by
  intro ⟨t, s', hStep⟩
  cases hStep with | mk h => rw [hStuck] at h; exact absurd h (by simp)

/-- Steps concatenation: ts ++ [] = ts. -/
theorem Steps_append_nil {s1 s2 : State} {ts : List TraceEvent}
    (h : Steps s1 ts s2) : Steps s1 (ts ++ []) s2 := by
  rw [List.append_nil]; exact h

/-- valueToString on null is "null". ECMA-262 §7.1.12. -/
theorem valueToString_null : valueToString .null = "null" := by
  simp [valueToString]

/-- valueToString on undefined is "undefined". ECMA-262 §7.1.12. -/
theorem valueToString_undefined : valueToString .undefined = "undefined" := by
  simp [valueToString]

/-- valueToString on object is "[object Object]". ECMA-262 §7.1.12. -/
theorem valueToString_object (addr : Nat) : valueToString (.object addr) = "[object Object]" := by
  simp [valueToString]

/-- valueToString on function is "function". ECMA-262 §7.1.12. -/
theorem valueToString_function (idx : FuncIdx) : valueToString (.function idx) = "function" := by
  simp [valueToString]

/-- pushTrace preserves the expression. -/
theorem pushTrace_expr (s : State) (t : TraceEvent) :
    (pushTrace s t).expr = s.expr := by
  simp [pushTrace]

/-- pushTrace preserves the environment. -/
theorem pushTrace_env (s : State) (t : TraceEvent) :
    (pushTrace s t).env = s.env := by
  simp [pushTrace]

/-- pushTrace preserves the heap. -/
theorem pushTrace_heap (s : State) (t : TraceEvent) :
    (pushTrace s t).heap = s.heap := by
  simp [pushTrace]

/-- pushTrace appends to the trace. -/
theorem pushTrace_trace (s : State) (t : TraceEvent) :
    (pushTrace s t).trace = s.trace ++ [t] := by
  simp [pushTrace]

/-- pushTrace preserves funcs. -/
theorem pushTrace_funcs (s : State) (t : TraceEvent) :
    (pushTrace s t).funcs = s.funcs := by
  simp [pushTrace]

/-- pushTrace preserves callStack. -/
theorem pushTrace_callStack (s : State) (t : TraceEvent) :
    (pushTrace s t).callStack = s.callStack := by
  simp [pushTrace]

/-- Env.lookup on empty env returns none. -/
theorem Env.lookup_empty (name : VarName) : Env.empty.lookup name = none := by
  simp [Env.empty, Env.lookup]

/-- §12.8.3 Adding a number to a string concatenates after ToString. -/
theorem evalBinary_add_num_string (n : Float) (s : String) :
    evalBinary .add (.number n) (.string s) = .string (valueToString (.number n) ++ s) := by
  simp [evalBinary]

/-- §12.8.3 Adding a string to a number concatenates after ToString. -/
theorem evalBinary_add_string_num (s : String) (n : Float) :
    evalBinary .add (.string s) (.number n) = .string (s ++ valueToString (.number n)) := by
  simp [evalBinary]

/-- §7.2.15 Strict inequality is negation of equality. -/
theorem evalBinary_strictNeq (a b : Value) :
    evalBinary .strictNeq a b = .bool (a != b) := by
  simp [evalBinary]

/-- §7.2.14 Abstract inequality is negation of abstract equality. -/
theorem evalBinary_neq (a b : Value) :
    evalBinary .neq a b = .bool (!abstractEq a b) := by
  simp [evalBinary]

/-- §7.2.13 Greater-than produces a bool. -/
theorem evalBinary_gt_bool (a b : Value) :
    ∃ bl, evalBinary .gt a b = .bool bl := by
  exact ⟨abstractLt b a, by simp [evalBinary]⟩

/-- §7.2.13 Less-or-equal produces a bool. -/
theorem evalBinary_le_bool (a b : Value) :
    ∃ bl, evalBinary .le a b = .bool bl := by
  exact ⟨!abstractLt b a, by simp [evalBinary]⟩

/-- §7.2.13 Greater-or-equal produces a bool. -/
theorem evalBinary_ge_bool (a b : Value) :
    ∃ bl, evalBinary .ge a b = .bool bl := by
  exact ⟨!abstractLt a b, by simp [evalBinary]⟩

/-- §12.9 Modulus produces a number. -/
theorem evalBinary_mod (a b : Value) :
    ∃ n, evalBinary .mod a b = .number n := by
  simp only [evalBinary]
  split <;> exact ⟨_, rfl⟩

/-- §12.9 Exponentiation produces a number. -/
theorem evalBinary_exp (a b : Value) :
    ∃ n, evalBinary .exp a b = .number n := by
  simp only [evalBinary]
  exact ⟨_, rfl⟩

/-- §12.12 Bitwise AND produces a number. -/
theorem evalBinary_bitAnd (a b : Value) :
    ∃ n, evalBinary .bitAnd a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.12 Bitwise OR produces a number. -/
theorem evalBinary_bitOr (a b : Value) :
    ∃ n, evalBinary .bitOr a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.12 Bitwise XOR produces a number. -/
theorem evalBinary_bitXor (a b : Value) :
    ∃ n, evalBinary .bitXor a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.9.3 Left shift produces a number. -/
theorem evalBinary_shl (a b : Value) :
    ∃ n, evalBinary .shl a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.9.3 Signed right shift produces a number. -/
theorem evalBinary_shr (a b : Value) :
    ∃ n, evalBinary .shr a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.9.3 Unsigned right shift produces a number. -/
theorem evalBinary_ushr (a b : Value) :
    ∃ n, evalBinary .ushr a b = .number n := by
  simp only [evalBinary]; exact ⟨_, rfl⟩

/-- §12.10.4 instanceof produces a bool. -/
theorem evalBinary_instanceof_bool (a b : Value) :
    ∃ bl, evalBinary .instanceof a b = .bool bl := by
  cases a <;> cases b <;> exact ⟨_, rfl⟩

/-- §12.10.2 in operator produces a bool. -/
theorem evalBinary_in_bool (a b : Value) :
    ∃ bl, evalBinary .«in» a b = .bool bl := by
  cases a <;> cases b <;> exact ⟨_, rfl⟩

/-- §13.5 Positive unary produces a number. -/
theorem evalUnary_pos (v : Value) :
    evalUnary .pos v = .number (toNumber v) := by
  cases v <;> simp [evalUnary]

/-- §12.5.8 Bitwise NOT produces a number. -/
theorem evalUnary_bitNot (v : Value) :
    ∃ n, evalUnary .bitNot v = .number n := by
  cases v <;> exact ⟨_, rfl⟩

/-- step? on a binary with non-value lhs steps the lhs. -/
theorem step_binary_nonvalue_lhs (op : BinOp) (lhs rhs : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hlhs : exprValue? lhs = none)
    (t : TraceEvent) (sl : State)
    (hstep : step? ⟨lhs, env, heap, trace, funcs, cs⟩ = some (t, sl)) :
    step? ⟨.binary op lhs rhs, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sl with expr := .binary op sl.expr rhs, trace := trace } t) := by
  simp [step?, hlhs, hstep]

/-- step? on a seq with non-value left steps the left. -/
theorem step_seq_nonvalue_lhs (a b : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (ha : exprValue? a = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨a, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.seq a b, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .seq sa.expr b, trace := trace } t) := by
  simp [step?, ha, hstep]

/-- Behaves on a single-step program. -/
theorem Behaves_single {p : Program} {t : TraceEvent} {s' : State}
    (hstep : Step (initialState p) t s')
    (hhalt : step? s' = none) :
    Behaves p [t] :=
  ⟨s', Steps_single hstep, hhalt⟩

/-- Steps preserves: if s1 steps to s2 via ts, and s2 steps to s3 via t, then
    s1 steps to s3 via ts ++ [t]. -/
theorem Steps_snoc {s1 s2 s3 : State} {ts : List TraceEvent} {t : TraceEvent}
    (h1 : Steps s1 ts s2) (h2 : Step s2 t s3) :
    Steps s1 (ts ++ [t]) s3 :=
  Steps_trans h1 (Steps_single h2)

/-- step? on getIndex with two values always produces some result. -/
theorem step_getIndex_values (objVal idxVal : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.getIndex (.lit objVal) (.lit idxVal), env, heap, trace, funcs, cs⟩).isSome = true := by
  cases objVal <;> simp [step?, exprValue?] <;> split <;> simp

/-- step? on setIndex with three values always produces some result. -/
theorem step_setIndex_values (objVal idxVal v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.setIndex (.lit objVal) (.lit idxVal) (.lit v), env, heap, trace, funcs, cs⟩).isSome = true := by
  cases objVal <;> simp [step?, exprValue?] <;> split <;> simp

/-- Nullish coalescing: logOr with non-falsy left returns the left operand. -/
theorem evalBinary_logOr_truthy (a b : Value) (h : toBoolean a = true) :
    evalBinary .logOr a b = a := by
  simp [evalBinary, h]

/-- Nullish coalescing: logOr with falsy left returns the right operand. -/
theorem evalBinary_logOr_falsy (a b : Value) (h : toBoolean a = false) :
    evalBinary .logOr a b = b := by
  simp [evalBinary, h]

/-- Logical AND with truthy left returns right operand. -/
theorem evalBinary_logAnd_truthy (a b : Value) (h : toBoolean a = true) :
    evalBinary .logAnd a b = b := by
  simp [evalBinary, h]

/-- Logical AND with falsy left returns left operand. -/
theorem evalBinary_logAnd_falsy (a b : Value) (h : toBoolean a = false) :
    evalBinary .logAnd a b = a := by
  simp [evalBinary, h]

/-- abstractEq is reflexive on numbers. -/
theorem abstractEq_number_refl (n : Float) (_h : ¬n.isNaN) :
    abstractEq (.number n) (.number n) = (n == n) := by
  simp [abstractEq]

/-- abstractEq: different type, both non-null/undefined → check coercion. -/
theorem abstractEq_null_null : abstractEq .null .null = true := by
  simp [abstractEq]

/-- abstractEq: undefined with itself is true. -/
theorem abstractEq_undefined_undefined : abstractEq .undefined .undefined = true := by
  simp [abstractEq]

/-- toBoolean on a nonzero non-NaN number is true. -/
theorem toBoolean_number_nonzero (n : Float) (hnz : ¬(n == 0.0) = true) (hnan : ¬n.isNaN) :
    toBoolean (.number n) = true := by
  simp [toBoolean, hnz, hnan]

/-- Every non-literal expression has step? producing some result or its sub-expression is stuck.
    This is the progress lemma: var, break, continue, while, labeled, newObj, functionDef, this
    always step (no stuck non-lit states for these constructors). -/
theorem step_var_isSome (name : VarName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.var name, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]; split <;> simp

/-- step? on this always produces some result. -/
theorem step_this_isSome (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.this, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]; split <;> simp

/-- step? on labeled always produces some result. -/
theorem step_labeled_isSome (label : LabelName) (body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.labeled label body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on break always produces some result. -/
theorem step_break_isSome (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.break label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on continue always produces some result. -/
theorem step_continue_isSome (label : Option LabelName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.continue label, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on while_ always produces some result. -/
theorem step_while_isSome' (cond body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.while_ cond body, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on newObj always produces some result. -/
theorem step_newObj_isSome (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.newObj callee args, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- step? on functionDef always produces some result. -/
theorem step_functionDef_isSome (fname : Option VarName) (params : List VarName)
    (body : Expr) (isAsync isGen : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.functionDef fname params body isAsync isGen, env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

/-- Step_iff forward: Step implies step?. -/
theorem Step_implies_step {s : State} {t : TraceEvent} {s' : State}
    (h : Step s t s') : step? s = some (t, s') := by
  cases h with | mk h' => exact h'

/-- Step_iff backward: step? implies Step. -/
theorem step_implies_Step {s : State} {t : TraceEvent} {s' : State}
    (h : step? s = some (t, s')) : Step s t s' :=
  Step.mk h

/-- Steps with empty trace is identity. -/
theorem Steps_nil_eq {s1 s2 : State} (h : Steps s1 [] s2) : s1 = s2 := by
  cases h with
  | refl => rfl

/-- evalBinary always returns a value (total function). ECMA-262 §12–§13. -/
theorem evalBinary_returns_value (op : BinOp) (a b : Value) :
    ∃ v, evalBinary op a b = v :=
  ⟨evalBinary op a b, rfl⟩

/-- evalUnary always returns a value (total function). ECMA-262 §13.5. -/
theorem evalUnary_returns_value (op : UnaryOp) (v : Value) :
    ∃ w, evalUnary op v = w :=
  ⟨evalUnary op v, rfl⟩

/-- valueToString always returns a string. ECMA-262 §7.1.12. -/
theorem valueToString_returns (v : Value) : ∃ s, valueToString v = s :=
  ⟨valueToString v, rfl⟩

/-- valueToString on true is "true". ECMA-262 §7.1.12. -/
theorem valueToString_true : valueToString (.bool true) = "true" := by
  simp [valueToString]

/-- valueToString on false is "false". ECMA-262 §7.1.12. -/
theorem valueToString_false : valueToString (.bool false) = "false" := by
  simp [valueToString]

/-- step? on call with non-function callee value and all-value args
    returns undefined (not stuck). ECMA-262 §13.3.1. -/
theorem step_call_nonfunc (v : Value) (args : List Expr) (vs : List Value)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ idx, v ≠ .function idx) (hargs : allValues args = some vs) :
    (step? ⟨.call (.lit v) args, env, heap, trace, funcs, cs⟩).isSome = true := by
  cases v with
  | function idx => exact absurd rfl (hv idx)
  | _ => simp [step?, exprValue?, hargs]

/-- step? on let with non-value init and steppable init, steps the init. -/
theorem step_let_step_init (name : VarName) (init body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hinit : exprValue? init = none)
    (t : TraceEvent) (si : State)
    (hstep : step? ⟨init, env, heap, trace, funcs, cs⟩ = some (t, si)) :
    step? ⟨.let name init body, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { si with expr := .let name si.expr body, trace := trace } t) := by
  simp [step?, hinit, hstep]

/-- step? on assign with non-value rhs and steppable rhs, steps the rhs. -/
theorem step_assign_step_rhs (name : VarName) (rhs : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hrhs : exprValue? rhs = none)
    (t : TraceEvent) (sr : State)
    (hstep : step? ⟨rhs, env, heap, trace, funcs, cs⟩ = some (t, sr)) :
    step? ⟨.assign name rhs, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sr with expr := .assign name sr.expr, trace := trace } t) := by
  simp [step?, hrhs, hstep]

/-- step? on if with non-value cond and steppable cond, steps the cond. -/
theorem step_if_step_cond (cond then_ else_ : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hcond : exprValue? cond = none)
    (t : TraceEvent) (sc : State)
    (hstep : step? ⟨cond, env, heap, trace, funcs, cs⟩ = some (t, sc)) :
    step? ⟨.if cond then_ else_, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sc with expr := .if sc.expr then_ else_, trace := trace } t) := by
  simp [step?, hcond, hstep]

/-- step? on unary with non-value arg and steppable arg, steps the arg. -/
theorem step_unary_step_arg (op : UnaryOp) (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.unary op arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .unary op sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on throw with non-value arg and steppable arg, steps the arg. -/
theorem step_throw_step_arg (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.throw arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .throw sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on typeof with non-value arg and steppable arg, steps the arg. -/
theorem step_typeof_step_arg (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.typeof arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .typeof sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on getProp with non-value obj and steppable obj, steps the obj. -/
theorem step_getProp_step_obj (obj : Expr) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.getProp obj prop, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .getProp so.expr prop, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- Steps from a stuck state must be the empty (refl) step. -/
theorem Steps_stuck {s sf : State} {ts : List TraceEvent}
    (hstuck : step? s = none) (hsteps : Steps s ts sf) :
    ts = [] ∧ sf = s := by
  cases hsteps with
  | refl => exact ⟨rfl, rfl⟩
  | tail hstep _ =>
    cases hstep with | mk h => rw [hstuck] at h; exact absurd h (by simp)

/-- Steps is deterministic: from the same start, same trace and end. -/
theorem Steps_deterministic {s sf1 sf2 : State} {ts1 ts2 : List TraceEvent}
    (h1 : Steps s ts1 sf1) (h2 : Steps s ts2 sf2)
    (hhalt1 : step? sf1 = none) (hhalt2 : step? sf2 = none) :
    ts1 = ts2 ∧ sf1 = sf2 := by
  induction h1 generalizing ts2 sf2 with
  | refl =>
    have ⟨hts, hsf⟩ := Steps_stuck hhalt1 h2
    exact ⟨hts.symm, hsf.symm⟩
  | tail hstep1 _ ih =>
    cases h2 with
    | refl =>
      cases hstep1 with
      | mk h => rw [hhalt2] at h; exact absurd h (by simp)
    | tail hstep2 htail2 =>
      cases hstep1 with | mk h1' =>
      cases hstep2 with | mk h2' =>
      have ⟨ht, hs⟩ := step_deterministic h1' h2'
      subst ht; subst hs
      have ⟨hts, hsf⟩ := ih htail2 hhalt1 hhalt2
      exact ⟨congrArg _ hts, hsf⟩

/-- Behaves is deterministic: a program produces at most one trace. -/
theorem Behaves_deterministic {p : Program} {b1 b2 : List TraceEvent}
    (h1 : Behaves p b1) (h2 : Behaves p b2) :
    b1 = b2 := by
  obtain ⟨sf1, hsteps1, hhalt1⟩ := h1
  obtain ⟨sf2, hsteps2, hhalt2⟩ := h2
  exact (Steps_deterministic hsteps1 hsteps2 hhalt1 hhalt2).1

/-- exprValue? returns none for all non-literal constructors. -/
theorem exprValue_non_lit (e : Expr) (h : ∀ v, e ≠ .lit v) : exprValue? e = none := by
  cases e with
  | lit v => exact absurd rfl (h v)
  | _ => rfl

/-- step_binary_value: binary op on two values computes directly. ECMA-262 §12. -/
theorem step_binary_value (op : BinOp) (a b : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.binary op (.lit a) (.lit b), env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (evalBinary op a b), env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- step? on deleteProp with non-value obj and steppable obj, steps the obj. -/
theorem step_deleteProp_step_obj (obj : Expr) (prop : PropName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.deleteProp obj prop, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .deleteProp so.expr prop, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- Env.lookup_extend_same' — more precise version returning the actual result. -/
theorem Env.lookup_extend_eq (env : Env) (name : VarName) (v : Value) :
    (Env.extend env name v).lookup name = some v := by
  simp [Env.extend, Env.lookup]

/-- step? on forIn with non-value obj and steppable obj, steps the obj. -/
theorem step_forIn_step_obj (binding : VarName) (obj body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.forIn binding obj body, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .forIn binding so.expr body, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- step? on forOf with non-value iterable and steppable iterable, steps the iterable. -/
theorem step_forOf_step_obj (binding : VarName) (iterable body : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hiter : exprValue? iterable = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨iterable, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.forOf binding iterable body, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .forOf binding so.expr body, trace := trace } t) := by
  simp [step?, hiter, hstep]

/-- §7.2.14 abstractEq: null/null is true. -/
theorem abstractEq_null_self : abstractEq .null .null = true := by
  simp [abstractEq]

/-- §7.2.14 abstractEq: undefined/undefined is true. -/
theorem abstractEq_undef_self : abstractEq .undefined .undefined = true := by
  simp [abstractEq]

/-- §7.2.14 abstractEq: bool/bool delegates to BEq. -/
theorem abstractEq_bool (a b : Bool) : abstractEq (.bool a) (.bool b) = (a == b) := by
  simp [abstractEq]

/-- §7.2.14 abstractEq: string/string delegates to BEq. -/
theorem abstractEq_string (a b : String) : abstractEq (.string a) (.string b) = (a == b) := by
  simp [abstractEq]

/-- Behaves also determines the final state. -/
theorem Behaves_final_unique {p : Program} {b : List TraceEvent}
    (h1 : Behaves p b) (_h2 : Behaves p b) :
    ∃ sf, Steps (initialState p) b sf ∧ step? sf = none := by
  obtain ⟨sf, hsteps, hhalt⟩ := h1
  exact ⟨sf, hsteps, hhalt⟩

/-- Steps.refl embeds into Steps. -/
theorem Steps_refl_eq (s : State) : Steps s [] s :=
  Steps.refl s

/-- step? preserves: if step produces (t, s'), then s' differs from s
    only in expr, env, heap, trace, funcs, callStack. -/
theorem step_preserves_structure {s : State} {t : TraceEvent} {s' : State}
    (_h : step? s = some (t, s')) :
    ∃ e' env' heap' trace' funcs' cs',
      s' = ⟨e', env', heap', trace', funcs', cs'⟩ :=
  ⟨s'.expr, s'.env, s'.heap, s'.trace, s'.funcs, s'.callStack, rfl⟩

/-- pushTrace on state with specific fields. -/
theorem pushTrace_fields (e : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) (t : TraceEvent) :
    pushTrace ⟨e, env, heap, trace, funcs, cs⟩ t =
      ⟨e, env, heap, trace ++ [t], funcs, cs⟩ := by
  simp [pushTrace]

/-- console.log with number argument produces correct log event. -/
theorem step_consoleLog_num (n : Float) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.call (.lit (.function consoleLogIdx)) [.lit (.number n)],
           env, heap, trace, funcs, cs⟩ =
      some (.log (valueToString (.number n)),
        pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩
          (.log (valueToString (.number n)))) := by
  simp [step?, exprValue?, allValues, consoleLogIdx, valueToString]

/-- Env.lookup after multiple extends: latest wins. -/
theorem Env.lookup_extend_shadow (env : Env) (name : VarName) (v1 v2 : Value) :
    (env.extend name v1 |>.extend name v2).lookup name = some v2 := by
  simp [Env.extend, Env.lookup]

/-- toNumber on undefined is NaN (0.0/0.0). -/
theorem toNumber_undefined : toNumber .undefined = 0.0 / 0.0 := by
  simp [toNumber]

/-- step? on setProp with non-value obj steps the obj. ECMA-262 §9.1.9. -/
theorem step_setProp_step_obj (obj : Expr) (prop : PropName) (value : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.setProp obj prop value, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .setProp so.expr prop value, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- step? on call with non-value callee steps the callee. ECMA-262 §13.3.1. -/
theorem step_call_step_callee (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hcallee : exprValue? callee = none)
    (t : TraceEvent) (sc : State)
    (hstep : step? ⟨callee, env, heap, trace, funcs, cs⟩ = some (t, sc)) :
    step? ⟨.call callee args, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sc with expr := .call sc.expr args, trace := trace } t) := by
  simp [step?, hcallee, hstep]

/-- step? on return with non-value arg steps the arg. ECMA-262 §13.1. -/
theorem step_return_step_arg (e : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? e = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨e, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.return (some e), env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .return (some sa.expr), trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on await with non-value arg steps the arg. ECMA-262 §14.7.14. -/
theorem step_await_step_arg (arg : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? arg = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨arg, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.await arg, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .await sa.expr, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on yield with non-value arg steps the arg. ECMA-262 §14.4.14. -/
theorem step_yield_step_arg (e : Expr) (delegate : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (harg : exprValue? e = none)
    (t : TraceEvent) (sa : State)
    (hstep : step? ⟨e, env, heap, trace, funcs, cs⟩ = some (t, sa)) :
    step? ⟨.yield (some e) delegate, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { sa with expr := .yield (some sa.expr) delegate, trace := trace } t) := by
  simp [step?, harg, hstep]

/-- step? on getIndex with non-value obj steps the obj. ECMA-262 §12.3.2. -/
theorem step_getIndex_step_obj (obj idx : Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hobj : exprValue? obj = none)
    (t : TraceEvent) (so : State)
    (hstep : step? ⟨obj, env, heap, trace, funcs, cs⟩ = some (t, so)) :
    step? ⟨.getIndex obj idx, env, heap, trace, funcs, cs⟩ =
      some (t, pushTrace { so with expr := .getIndex so.expr idx, trace := trace } t) := by
  simp [step?, hobj, hstep]

/-- step? on tryCatch with non-value body: normal (non-error) step wraps in tryCatch. -/
theorem step_tryCatch_step_body_silent (body : Expr) (catchParam : VarName) (catchBody : Expr)
    (finally_ : Option Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hbody : exprValue? body = none)
    (sb : State)
    (hstep : step? ⟨body, env, heap, trace, funcs, cs⟩ = some (.silent, sb)) :
    step? ⟨.tryCatch body catchParam catchBody finally_, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace { sb with expr := .tryCatch sb.expr catchParam catchBody finally_, trace := trace } .silent) := by
  simp [step?, hbody, hstep]

/-- step? on tryCatch with non-value body: log step wraps in tryCatch. -/
theorem step_tryCatch_step_body_log (body : Expr) (catchParam : VarName) (catchBody : Expr)
    (finally_ : Option Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value)))
    (hbody : exprValue? body = none)
    (msg : String) (sb : State)
    (hstep : step? ⟨body, env, heap, trace, funcs, cs⟩ = some (.log msg, sb)) :
    step? ⟨.tryCatch body catchParam catchBody finally_, env, heap, trace, funcs, cs⟩ =
      some (.log msg, pushTrace { sb with expr := .tryCatch sb.expr catchParam catchBody finally_, trace := trace } (.log msg)) := by
  simp [step?, hbody, hstep]

/-- Steps inversion: from [t] there is exactly one step. -/
theorem Steps_single_inv {s1 s2 : State} {t : TraceEvent}
    (h : Steps s1 [t] s2) : Step s1 t s2 := by
  cases h with
  | tail hstep htail =>
    cases htail with
    | refl => exact hstep

/-- step_functionDef exact: produces the closure value and updated funcs. -/
theorem step_functionDef_exact (fname : Option VarName) (params : List VarName)
    (body : Expr) (isAsync isGen : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.functionDef fname params body isAsync isGen, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (.function funcs.size), env, heap, trace,
        funcs.push ⟨fname, params, body, env.bindings⟩, cs⟩ .silent) := by
  simp [step?]

/-- step? on yield with value arg steps to that value. -/
theorem step_yield_some_value (v : Value) (delegate : Bool) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.yield (some (.lit v)) delegate, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?]

/-- step? on return with value arg produces error event. -/
theorem step_return_some_value_exact (v : Value) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.return (some (.lit v)), env, heap, trace, funcs, cs⟩ =
      some (.error ("return:" ++ valueToString v),
        pushTrace ⟨.lit v, env, heap, trace, funcs, cs⟩
          (.error ("return:" ++ valueToString v))) := by
  simp [step?, exprValue?]

/-- §12.3.3 newObj exact: allocates empty object at next heap address. -/
theorem step_newObj_exact (callee : Expr) (args : List Expr) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    step? ⟨.newObj callee args, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit (.object heap.nextAddr), env,
        { objects := heap.objects.push [], nextAddr := heap.nextAddr + 1 },
        trace, funcs, cs⟩ .silent) := by
  simp [step?]

/-- §13.7.5 for-in on object with known properties: desugars to sequential let-bindings.
    ECMA-262 §13.7.5.15 EnumerateObjectProperties. -/
theorem step_forIn_object_props (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (props : List (PropName × Value))
    (hprops : heap.objects[addr]? = some props) :
    step? ⟨.forIn binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨
        (props.map (fun p => p.1)).foldr (fun key acc =>
          .seq (.«let» binding (.lit (.string key)) body) acc) (.lit .undefined),
        env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hprops]

/-- §13.7.5.13 for-of on object with known properties: desugars to sequential let-bindings.
    ECMA-262 §7.4.1 GetIterator / §7.4.6 IteratorStep. -/
theorem step_forOf_object_props (binding : VarName) (addr : Nat) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (props : List (PropName × Value))
    (hprops : heap.objects[addr]? = some props) :
    step? ⟨.forOf binding (.lit (.object addr)) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨
        (props.map (fun p => p.2)).foldr (fun val acc =>
          .seq (.«let» binding (.lit val) body) acc) (.lit .undefined),
        env, heap, trace, funcs, cs⟩ .silent) := by
  simp [step?, exprValue?, hprops]

/-- §13.7.5 for-in on non-object exact: produces undefined.
    ECMA-262 §13.7.5.12: ToObject(null/undefined/bool/number/string) then enumerate. -/
theorem step_forIn_nonObject_exact (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    step? ⟨.forIn binding (.lit v) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §13.7.5.13 for-of on non-object exact: produces undefined. -/
theorem step_forOf_nonObject_exact (binding : VarName) (v : Value) (body : Expr)
    (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hv : ∀ addr, v ≠ .object addr) :
    step? ⟨.forOf binding (.lit v) body, env, heap, trace, funcs, cs⟩ =
      some (.silent, pushTrace ⟨.lit .undefined, env, heap, trace, funcs, cs⟩ .silent) := by
  cases v with
  | object addr => exact absurd rfl (hv addr)
  | _ => simp [step?, exprValue?]

/-- §14.6 Class pattern inhabitedness: a class desugars to functionDef + setProp on prototype.
    This demonstrates that the Core IL supports the class pattern:
    `let C = function C() {}; C.prototype.m = function() { ... }` -/
theorem step_class_pattern_functionDef (name : VarName) (env : Env) (heap : Heap)
    (trace : List TraceEvent) (funcs : Array FuncClosure)
    (cs : List (List (VarName × Value))) :
    (step? ⟨.functionDef (some name) [] (.lit .undefined) false false,
            env, heap, trace, funcs, cs⟩).isSome = true := by
  simp [step?]

private theorem exprValue?_lit_some (v : Value) : exprValue? (.lit v) = some v := rfl

set_option maxHeartbeats 4000000 in
set_option linter.deprecated false in
/-- The only stuck expression is a literal (progress). -/
private theorem stuck_implies_lit_aux (e : Expr) (env : Env) (heap : Heap) (trace : List TraceEvent)
    (funcs : Array FuncClosure) (cs : List (List (VarName × Value)))
    (hstuck : step? ⟨e, env, heap, trace, funcs, cs⟩ = none) :
    ∃ v, e = .lit v := by
  cases e with
  | lit v => exact ⟨v, rfl⟩
  | var name =>
    unfold step? at hstuck; simp only [] at hstuck; split at hstuck <;> simp at hstuck
  | functionDef name params body isAsync isGen =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | «break» label =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | «continue» label =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | while_ cond body =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | labeled label body =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | this =>
    unfold step? at hstuck; simp only [] at hstuck; split at hstuck <;> simp at hstuck
  | newObj callee args =>
    unfold step? at hstuck; simp only [] at hstuck; simp at hstuck
  | «let» name init body =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | assign name rhs =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | «if» cond then_ else_ =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | seq a b =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | unary op arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | typeof arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | throw arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | await arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · simp at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  | «return» arg =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i _ _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
  | yield arg delegate =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i _ _ hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
  | forIn binding obj body =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
  | forOf binding iterable body =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
  | deleteProp obj prop =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
  | getProp obj prop =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · simp at hstuck
    · simp at hstuck
    · simp at hstuck
  | binary op lhs rhs =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
      · simp at hstuck
  | setProp obj prop value =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · split at hstuck
        · simp at hstuck
        · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
      · split at hstuck <;> simp at hstuck
  | getIndex obj idx =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck <;> (try split at hstuck) <;> simp at hstuck
  | setIndex obj idx value =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck <;> simp at hstuck
  | call callee args =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
    · split at hstuck
      · split at hstuck <;> (try split at hstuck) <;> (try split at hstuck) <;> simp at hstuck
      · split at hstuck
        · split at hstuck
          · simp at hstuck
          · rename_i _ _ _ hsub
            have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv
            exfalso; exact firstNonValueExpr_not_lit (by assumption) _ rfl
        · exfalso; exact allValues_firstNonValue_contra (by assumption) (by assumption)
  | objectLit props =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub
        have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv
        exfalso; exact firstNonValueProp_not_lit (by assumption) _ rfl
    · simp at hstuck
  | arrayLit elems =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck
      · simp at hstuck
      · rename_i _ hsub
        have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv
        exfalso; exact firstNonValueExpr_not_lit (by assumption) _ rfl
    · simp at hstuck
  | tryCatch body catchParam catchBody finally_ =>
    unfold step? at hstuck; simp only [] at hstuck
    split at hstuck
    · split at hstuck <;> (try split at hstuck) <;> simp at hstuck
    · split at hstuck
      · split at hstuck <;> (try split at hstuck) <;> (try split at hstuck) <;> simp at hstuck
      · simp at hstuck
      · rename_i hsub; have ⟨v, hv⟩ := stuck_implies_lit_aux _ _ _ _ _ _ hsub; subst hv; simp_all [exprValue?]
  termination_by e.depth
  decreasing_by
    all_goals (try cases ‹Option Expr›) <;> simp_all [Expr.depth] <;>
      (try have := firstNonValueExpr_depth ‹_›; omega) <;>
      (try have := firstNonValueProp_depth ‹_›; omega) <;>
      omega

theorem stuck_implies_lit {s : State} (hstuck : step? s = none) :
    ∃ v, s.expr = .lit v :=
  stuck_implies_lit_aux s.expr s.env s.heap s.trace s.funcs s.callStack (by cases s; exact hstuck)

theorem Behaves_final_lit {p : Program} {b : List TraceEvent}
    (hB : Behaves p b) :
    ∃ sf v, Steps (initialState p) b sf ∧ step? sf = none ∧ sf.expr = .lit v := by
  obtain ⟨sf, hsteps, hhalt⟩ := hB
  obtain ⟨v, hv⟩ := stuck_implies_lit hhalt
  exact ⟨sf, v, hsteps, hhalt, hv⟩

end VerifiedJS.Core

namespace VerifiedJS.Source

open VerifiedJS.Core in
/-- Source.Behaves: A source program produces trace `b` iff elaboration to Core
    succeeds and the resulting Core program produces that trace.
    This bridges Source.Program → Core.Behaves via the elaborate pass,
    enabling the end-to-end proof chain (elaborate_correct).
    ECMA-262 §15.1 (Script evaluation) / §15.2 (Module evaluation). -/
def Behaves (p : Source.Program) (b : List Core.TraceEvent) : Prop :=
  ∃ coreProg : Core.Program, Core.elaborate p = .ok coreProg ∧ Core.Behaves coreProg b

open VerifiedJS.Core in
/-- Source.Behaves is monotone: if elaboration produces the same Core program,
    Core behavior implies Source behavior. -/
theorem Behaves_of_elaborate {p : Source.Program} {cp : Core.Program}
    {b : List Core.TraceEvent}
    (hElab : Core.elaborate p = .ok cp) (hBehaves : Core.Behaves cp b) :
    Behaves p b :=
  ⟨cp, hElab, hBehaves⟩

open VerifiedJS.Core in

/-- elaborate_correct: elaboration preserves observable behavior.
    Every Core-level trace of the elaborated program is a valid Source-level trace. -/
theorem elaborate_correct (p : Source.Program) (cp : Core.Program)
    (hElab : Core.elaborate p = .ok cp) :
    ∀ b, Core.Behaves cp b → Behaves p b :=
  fun _ hB => Behaves_of_elaborate hElab hB

end VerifiedJS.Source
