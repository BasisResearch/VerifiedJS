/-
  VerifiedJS — Flat IL Pretty Printer
-/

import VerifiedJS.Flat.Syntax
import VerifiedJS.Core.Print

namespace VerifiedJS.Flat

def printValue : Value → String
  | .null => "null"
  | .undefined => "undefined"
  | .bool b => if b then "true" else "false"
  | .number n => toString n
  | .string s => "\"" ++ s ++ "\""
  | .object addr => s!"<object@{addr}>"
  | .closure funcIdx envPtr => s!"<closure func#{funcIdx} env@{envPtr}>"

partial def printExpr (e : Expr) (indent : Nat := 0) : String :=
  let i := Core.ind indent
  let i1 := Core.ind (indent + 1)
  match e with
  | .lit v => printValue v
  | .var name => name
  | .«let» name init body =>
    s!"{i}let {name} = {printExpr init 0};\n{printExpr body indent}"
  | .assign name value => s!"{name} = {printExpr value 0}"
  | .«if» cond t e_ =>
    s!"{i}if ({printExpr cond 0}) \{\n{printExpr t (indent+1)}\n{i}} else \{\n{printExpr e_ (indent+1)}\n{i}}"
  | .seq a b => s!"{printExpr a indent};\n{printExpr b indent}"
  | .call funcIdx envPtr args =>
    let argStrs := args.map (printExpr · 0)
    s!"call({printExpr funcIdx 0}, {printExpr envPtr 0}, [{String.intercalate ", " argStrs}])"
  | .newObj funcIdx envPtr args =>
    let argStrs := args.map (printExpr · 0)
    s!"new({printExpr funcIdx 0}, {printExpr envPtr 0}, [{String.intercalate ", " argStrs}])"
  | .getProp obj prop => s!"{printExpr obj 0}.{prop}"
  | .setProp obj prop value => s!"{printExpr obj 0}.{prop} = {printExpr value 0}"
  | .getIndex obj idx => s!"{printExpr obj 0}[{printExpr idx 0}]"
  | .setIndex obj idx value => s!"{printExpr obj 0}[{printExpr idx 0}] = {printExpr value 0}"
  | .deleteProp obj prop => s!"delete {printExpr obj 0}.{prop}"
  | .typeof arg => s!"typeof {printExpr arg 0}"
  | .getEnv envPtr idx => s!"env_get({printExpr envPtr 0}, {idx})"
  | .makeEnv values =>
    let vs := values.map (printExpr · 0)
    s!"env_make([{String.intercalate ", " vs}])"
  | .makeClosure funcIdx env => s!"closure({funcIdx}, {printExpr env 0})"
  | .objectLit props =>
    let ps := props.map fun (k, v) => s!"{i1}{k}: {printExpr v 0}"
    s!"\{\n{String.intercalate ",\n" ps}\n{i}}"
  | .arrayLit elems =>
    let es := elems.map (printExpr · 0)
    s!"[{String.intercalate ", " es}]"
  | .throw arg => s!"throw {printExpr arg 0}"
  | .tryCatch body catchParam catchBody finally_ =>
    let fin := match finally_ with
      | some f => s!" finally \{\n{printExpr f (indent+1)}\n{i}}"
      | none => ""
    s!"{i}try \{\n{printExpr body (indent+1)}\n{i}} catch ({catchParam}) \{\n{printExpr catchBody (indent+1)}\n{i}}{fin}"
  | .while_ cond body =>
    s!"{i}while ({printExpr cond 0}) \{\n{printExpr body (indent+1)}\n{i}}"
  | .«break» label => match label with | some l => s!"break {l}" | none => "break"
  | .«continue» label => match label with | some l => s!"continue {l}" | none => "continue"
  | .labeled label body => s!"{label}: {printExpr body indent}"
  | .«return» arg => match arg with | some a => s!"return {printExpr a 0}" | none => "return"
  | .yield arg delegate =>
    let star := if delegate then "*" else ""
    match arg with | some a => s!"yield{star} {printExpr a 0}" | none => s!"yield{star}"
  | .await arg => s!"await {printExpr arg 0}"
  | .this => "this"
  | .unary op arg => s!"{Core.printUnaryOp op}{printExpr arg 0}"
  | .binary op lhs rhs => s!"({printExpr lhs 0} {Core.printBinOp op} {printExpr rhs 0})"

def printFuncDef (f : FuncDef) : String :=
  s!"function {f.name}({String.intercalate ", " f.params}; env={f.envParam}) \{\n{printExpr f.body 1}\n}"

def printProgram (p : Program) : String :=
  let funcs := p.functions.toList.map printFuncDef
  let body := printExpr p.main 0
  String.intercalate "\n\n" (funcs ++ [body])

end VerifiedJS.Flat
