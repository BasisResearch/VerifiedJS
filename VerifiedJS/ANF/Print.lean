/-
  VerifiedJS — ANF IL Pretty Printer
-/

import VerifiedJS.ANF.Syntax
import VerifiedJS.Core.Print

namespace VerifiedJS.ANF

def printTrivial : Trivial → String
  | .var name => name
  | .litNull => "null"
  | .litUndefined => "undefined"
  | .litBool b => if b then "true" else "false"
  | .litNum n => toString n
  | .litStr s => "\"" ++ s ++ "\""
  | .litObject addr => s!"<object@{addr}>"
  | .litClosure funcIdx envPtr => s!"<closure func#{funcIdx} env@{envPtr}>"

def printComplexExpr : ComplexExpr → String
  | .trivial t => printTrivial t
  | .assign name value => s!"{name} = {printTrivial value}"
  | .call callee env args =>
    let argStrs := args.map printTrivial
    s!"call({printTrivial callee}, {printTrivial env}, [{String.intercalate ", " argStrs}])"
  | .newObj callee env args =>
    let argStrs := args.map printTrivial
    s!"new({printTrivial callee}, {printTrivial env}, [{String.intercalate ", " argStrs}])"
  | .getProp obj prop => s!"{printTrivial obj}.{prop}"
  | .setProp obj prop value => s!"{printTrivial obj}.{prop} = {printTrivial value}"
  | .getIndex obj idx => s!"{printTrivial obj}[{printTrivial idx}]"
  | .setIndex obj idx value => s!"{printTrivial obj}[{printTrivial idx}] = {printTrivial value}"
  | .deleteProp obj prop => s!"delete {printTrivial obj}.{prop}"
  | .typeof arg => s!"typeof {printTrivial arg}"
  | .getEnv env idx => s!"env_get({printTrivial env}, {idx})"
  | .makeEnv values =>
    let vs := values.map printTrivial
    s!"env_make([{String.intercalate ", " vs}])"
  | .makeClosure funcIdx env => s!"closure({funcIdx}, {printTrivial env})"
  | .objectLit props =>
    let ps := props.map fun (k, v) => s!"{k}: {printTrivial v}"
    s!"\{{String.intercalate ", " ps}}"
  | .arrayLit elems =>
    let es := elems.map printTrivial
    s!"[{String.intercalate ", " es}]"
  | .unary op arg => s!"{Core.printUnaryOp op}{printTrivial arg}"
  | .binary op lhs rhs => s!"({printTrivial lhs} {Core.printBinOp op} {printTrivial rhs})"

partial def printExpr (e : Expr) (indent : Nat := 0) : String :=
  let i := Core.ind indent
  match e with
  | .trivial t => s!"{i}{printTrivial t}"
  | .«let» name rhs body =>
    s!"{i}let {name} = {printComplexExpr rhs};\n{printExpr body indent}"
  | .seq a b => s!"{printExpr a indent};\n{printExpr b indent}"
  | .«if» cond t e_ =>
    s!"{i}if ({printTrivial cond}) \{\n{printExpr t (indent+1)}\n{i}} else \{\n{printExpr e_ (indent+1)}\n{i}}"
  | .while_ cond body =>
    s!"{i}while ({printExpr cond 0}) \{\n{printExpr body (indent+1)}\n{i}}"
  | .throw arg => s!"{i}throw {printTrivial arg}"
  | .tryCatch body catchParam catchBody finally_ =>
    let fin := match finally_ with
      | some f => s!" finally \{\n{printExpr f (indent+1)}\n{i}}"
      | none => ""
    s!"{i}try \{\n{printExpr body (indent+1)}\n{i}} catch ({catchParam}) \{\n{printExpr catchBody (indent+1)}\n{i}}{fin}"
  | .«return» arg => match arg with
    | some a => s!"{i}return {printTrivial a}"
    | none => s!"{i}return"
  | .yield arg delegate =>
    let star := if delegate then "*" else ""
    match arg with | some a => s!"{i}yield{star} {printTrivial a}" | none => s!"{i}yield{star}"
  | .await arg => s!"{i}await {printTrivial arg}"
  | .labeled label body => s!"{i}{label}: {printExpr body indent}"
  | .«break» label => match label with | some l => s!"{i}break {l}" | none => s!"{i}break"
  | .«continue» label => match label with | some l => s!"{i}continue {l}" | none => s!"{i}continue"

def printFuncDef (f : FuncDef) : String :=
  s!"function {f.name}({String.intercalate ", " f.params}; env={f.envParam}) \{\n{printExpr f.body 1}\n}"

def printProgram (p : Program) : String :=
  let funcs := p.functions.toList.map printFuncDef
  let body := printExpr p.main 0
  String.intercalate "\n\n" (funcs ++ [body])

end VerifiedJS.ANF
