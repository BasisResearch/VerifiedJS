/-
  VerifiedJS — Closure Conversion: JS.Core → JS.Flat
  Converts closures to (function_index, environment_pointer) pairs.
-/

import VerifiedJS.Core.Syntax
import VerifiedJS.Flat.Syntax

namespace VerifiedJS.Flat

/-- Closure conversion state: accumulated lifted functions + fresh name counter. -/
structure CCState where
  funcs : Array FuncDef
  nextId : Nat
  deriving Repr, Inhabited

def CCState.empty : CCState := { funcs := #[], nextId := 0 }

def CCState.freshVar (st : CCState) (pfx : String) : String × CCState :=
  (s!"{pfx}_{st.nextId}", { st with nextId := st.nextId + 1 })

def CCState.addFunc (st : CCState) (f : FuncDef) : Nat × CCState :=
  (st.funcs.size, { st with funcs := st.funcs.push f })

/-- Environment mapping: variable name → index in the environment array. -/
abbrev EnvMapping := List (String × Nat)

/-- Remove duplicates from a list of strings (keeping first occurrence). -/
partial def dedupStrings : List String → List String → List String
  | [], acc => acc.reverse
  | x :: xs, acc =>
    if acc.elem x then dedupStrings xs acc
    else dedupStrings xs (x :: acc)

/-- Compute free variables of a Core expression. -/
partial def freeVars : Core.Expr → List String
  | .lit _ => []
  | .var n => [n]
  | .this => []
  | .«let» name init body =>
    let fInit := freeVars init
    let fBody := (freeVars body).filter (· != name)
    dedupStrings (fInit ++ fBody) []
  | .assign name value => dedupStrings (name :: freeVars value) []
  | .«if» c t e => dedupStrings (freeVars c ++ freeVars t ++ freeVars e) []
  | .seq a b => dedupStrings (freeVars a ++ freeVars b) []
  | .call callee args =>
    let fArgs := args.foldl (fun acc a => acc ++ freeVars a) []
    dedupStrings (freeVars callee ++ fArgs) []
  | .newObj callee args =>
    let fArgs := args.foldl (fun acc a => acc ++ freeVars a) []
    dedupStrings (freeVars callee ++ fArgs) []
  | .getProp obj _ => freeVars obj
  | .setProp obj _ value => dedupStrings (freeVars obj ++ freeVars value) []
  | .getIndex obj idx => dedupStrings (freeVars obj ++ freeVars idx) []
  | .setIndex obj idx value =>
    dedupStrings (freeVars obj ++ freeVars idx ++ freeVars value) []
  | .deleteProp obj _ => freeVars obj
  | .typeof arg => freeVars arg
  | .unary _ arg => freeVars arg
  | .binary _ lhs rhs => dedupStrings (freeVars lhs ++ freeVars rhs) []
  | .objectLit props =>
    let fAll := props.foldl (fun acc (_, e) => acc ++ freeVars e) []
    dedupStrings fAll []
  | .arrayLit elems =>
    let fAll := elems.foldl (fun acc e => acc ++ freeVars e) []
    dedupStrings fAll []
  | .functionDef _name params body _ _ =>
    let fBody := freeVars body
    let bound := params
    let filtered := fBody.filter (fun v => !(bound.elem v))
    dedupStrings filtered []
  | .throw arg => freeVars arg
  | .tryCatch body catchParam catchBody finally_ =>
    let fBody := freeVars body
    let fCatch := (freeVars catchBody).filter (· != catchParam)
    let fFinally := match finally_ with
      | none => []
      | some e => freeVars e
    dedupStrings (fBody ++ fCatch ++ fFinally) []
  | .while_ cond body => dedupStrings (freeVars cond ++ freeVars body) []
  | .«break» _ => []
  | .«continue» _ => []
  | .«return» arg => match arg with
    | none => []
    | some e => freeVars e
  | .labeled _ body => freeVars body
  | .yield arg _ => match arg with
    | none => []
    | some e => freeVars e
  | .await arg => freeVars arg

/-- Look up a variable in the environment mapping. -/
def lookupEnv (envMap : EnvMapping) (name : String) : Option Nat :=
  match envMap with
  | [] => none
  | (n, idx) :: rest => if n == name then some idx else lookupEnv rest name

/-- Convert a Core.Value to a Flat.Value. -/
def convertValue : Core.Value → Value
  | .null => .null
  | .undefined => .undefined
  | .bool b => .bool b
  | .number n => .number n
  | .string s => .string s
  | .object addr => .object addr
  | .function idx => .closure idx 0

/-- Build an indexed mapping from a list: [(item0,0), (item1,1), ...]. -/
def indexedMap : List String → Nat → List (String × Nat)
  | [], _ => []
  | x :: xs, n => (x, n) :: indexedMap xs (n + 1)

mutual

/-- Convert a list of expressions, threading state. -/
partial def convertExprList
    (es : List Core.Expr) (scope : List String) (envVar : String)
    (envMap : EnvMapping) (st : CCState)
    : List Flat.Expr × CCState :=
  match es with
  | [] => ([], st)
  | e :: rest =>
    let (e', st1) := convertExpr e scope envVar envMap st
    let (rest', st2) := convertExprList rest scope envVar envMap st1
    (e' :: rest', st2)

/-- Convert a list of (PropName × Expr) pairs, threading state. -/
partial def convertPropList
    (ps : List (Core.PropName × Core.Expr)) (scope : List String) (envVar : String)
    (envMap : EnvMapping) (st : CCState)
    : List (PropName × Flat.Expr) × CCState :=
  match ps with
  | [] => ([], st)
  | (pname, e) :: rest =>
    let (e', st1) := convertExpr e scope envVar envMap st
    let (rest', st2) := convertPropList rest scope envVar envMap st1
    ((pname, e') :: rest', st2)

/-- Convert an optional Core.Expr, threading state. -/
partial def convertOptExpr
    (oe : Option Core.Expr) (scope : List String) (envVar : String)
    (envMap : EnvMapping) (st : CCState)
    : Option Flat.Expr × CCState :=
  match oe with
  | none => (none, st)
  | some e =>
    let (e', st1) := convertExpr e scope envVar envMap st
    (some e', st1)

/-- Main expression conversion: Core.Expr → Flat.Expr with state threading. -/
partial def convertExpr
    (e : Core.Expr) (scope : List String) (envVar : String)
    (envMap : EnvMapping) (st : CCState)
    : Flat.Expr × CCState :=
  match e with
  | .lit v => (.lit (convertValue v), st)
  | .var n =>
    match lookupEnv envMap n with
    | some idx => (.getEnv (.var envVar) idx, st)
    | none => (.var n, st)
  | .this => (.this, st)
  | .«let» name init body =>
    let (init', st1) := convertExpr init scope envVar envMap st
    let newScope := name :: scope
    let (body', st2) := convertExpr body newScope envVar envMap st1
    (.«let» name init' body', st2)
  | .assign name value =>
    let (value', st1) := convertExpr value scope envVar envMap st
    (.assign name value', st1)
  | .«if» cond then_ else_ =>
    let (cond', st1) := convertExpr cond scope envVar envMap st
    let (then', st2) := convertExpr then_ scope envVar envMap st1
    let (else', st3) := convertExpr else_ scope envVar envMap st2
    (.«if» cond' then' else', st3)
  | .seq a b =>
    let (a', st1) := convertExpr a scope envVar envMap st
    let (b', st2) := convertExpr b scope envVar envMap st1
    (.seq a' b', st2)
  | .call callee args =>
    let (callee', st1) := convertExpr callee scope envVar envMap st
    let (args', st2) := convertExprList args scope envVar envMap st1
    (.call callee' (.lit .null) args', st2)
  | .newObj callee args =>
    let (callee', st1) := convertExpr callee scope envVar envMap st
    let (args', st2) := convertExprList args scope envVar envMap st1
    (.newObj callee' (.lit .null) args', st2)
  | .getProp obj prop =>
    let (obj', st1) := convertExpr obj scope envVar envMap st
    (.getProp obj' prop, st1)
  | .setProp obj prop value =>
    let (obj', st1) := convertExpr obj scope envVar envMap st
    let (value', st2) := convertExpr value scope envVar envMap st1
    (.setProp obj' prop value', st2)
  | .getIndex obj idx =>
    let (obj', st1) := convertExpr obj scope envVar envMap st
    let (idx', st2) := convertExpr idx scope envVar envMap st1
    (.getIndex obj' idx', st2)
  | .setIndex obj idx value =>
    let (obj', st1) := convertExpr obj scope envVar envMap st
    let (idx', st2) := convertExpr idx scope envVar envMap st1
    let (value', st3) := convertExpr value scope envVar envMap st2
    (.setIndex obj' idx' value', st3)
  | .deleteProp obj prop =>
    let (obj', st1) := convertExpr obj scope envVar envMap st
    (.deleteProp obj' prop, st1)
  | .typeof arg =>
    let (arg', st1) := convertExpr arg scope envVar envMap st
    (.typeof arg', st1)
  | .unary op arg =>
    let (arg', st1) := convertExpr arg scope envVar envMap st
    (.unary op arg', st1)
  | .binary op lhs rhs =>
    let (lhs', st1) := convertExpr lhs scope envVar envMap st
    let (rhs', st2) := convertExpr rhs scope envVar envMap st1
    (.binary op lhs' rhs', st2)
  | .objectLit props =>
    let (props', st1) := convertPropList props scope envVar envMap st
    (.objectLit props', st1)
  | .arrayLit elems =>
    let (elems', st1) := convertExprList elems scope envVar envMap st
    (.arrayLit elems', st1)
  | .functionDef fname params body _isAsync _isGenerator =>
    -- Compute free variables of the function body, minus params
    let bodyFree := freeVars body
    let bound := params
    let free := bodyFree.filter (fun v => !(bound.elem v))
    let captured := dedupStrings free []
    -- Build inner environment mapping for captured variables
    let innerEnvMap := indexedMap captured 0
    -- Create a fresh environment parameter name
    let (innerEnvVar, st1) := st.freshVar "__env"
    -- Convert body with inner env mapping
    let innerScope := params
    let (body', st2) := convertExpr body innerScope innerEnvVar innerEnvMap st1
    -- Create the lifted function
    let funcName := match fname with
      | some n => n
      | none => s!"__anon_{st2.nextId}"
    let funcDef : FuncDef := {
      name := funcName
      params := params
      envParam := innerEnvVar
      body := body'
    }
    let (funcIdx, st3) := st2.addFunc funcDef
    -- Build makeEnv with captured variable expressions
    let capturedExprs := captured.map (fun v =>
      match lookupEnv envMap v with
      | some idx => Flat.Expr.getEnv (.var envVar) idx
      | none => Flat.Expr.var v)
    let envExpr := Flat.Expr.makeEnv capturedExprs
    (.makeClosure funcIdx envExpr, st3)
  | .throw arg =>
    let (arg', st1) := convertExpr arg scope envVar envMap st
    (.throw arg', st1)
  | .tryCatch body catchParam catchBody finally_ =>
    let (body', st1) := convertExpr body scope envVar envMap st
    let (catchBody', st2) := convertExpr catchBody (catchParam :: scope) envVar envMap st1
    let (finally', st3) := convertOptExpr finally_ scope envVar envMap st2
    (.tryCatch body' catchParam catchBody' finally', st3)
  | .while_ cond body =>
    let (cond', st1) := convertExpr cond scope envVar envMap st
    let (body', st2) := convertExpr body scope envVar envMap st1
    (.while_ cond' body', st2)
  | .«break» label => (.«break» label, st)
  | .«continue» label => (.«continue» label, st)
  | .«return» arg =>
    let (arg', st1) := convertOptExpr arg scope envVar envMap st
    (.«return» arg', st1)
  | .labeled label body =>
    let (body', st1) := convertExpr body scope envVar envMap st
    (.labeled label body', st1)
  | .yield arg delegate =>
    let (arg', st1) := convertOptExpr arg scope envVar envMap st
    (.yield arg' delegate, st1)
  | .await arg =>
    let (arg', st1) := convertExpr arg scope envVar envMap st
    (.await arg', st1)

/-- Convert a Core.FuncDef to a Flat.FuncDef (top-level, no captures). -/
partial def convertFuncDef (fd : Core.FuncDef) (st : CCState) : FuncDef × CCState :=
  let envVar := "__env_top"
  let (body', st1) := convertExpr fd.body fd.params envVar [] st
  ({ name := fd.name, params := fd.params, envParam := envVar, body := body' }, st1)

/-- Convert top-level functions array, threading state. -/
partial def convertFuncDefs (fds : List Core.FuncDef) (st : CCState)
    : List FuncDef × CCState :=
  match fds with
  | [] => ([], st)
  | fd :: rest =>
    let (fd', st1) := convertFuncDef fd st
    let (rest', st2) := convertFuncDefs rest st1
    (fd' :: rest', st2)

end -- mutual

/-- Convert a Core program to Flat by closure conversion. -/
def closureConvert (prog : Core.Program) : Except String Program :=
  let st0 := CCState.empty
  -- Convert top-level named functions first
  let (topFuncs, st1) := convertFuncDefs prog.functions.toList st0
  -- Add top-level functions to state
  let st2 := topFuncs.foldl (fun s f => (s.addFunc f).2) st1
  -- Convert the main body expression
  let (mainExpr, st3) := convertExpr prog.body [] "__env_main" [] st2
  .ok { functions := st3.funcs, main := mainExpr }

end VerifiedJS.Flat
