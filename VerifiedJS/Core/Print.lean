/-
  VerifiedJS — Core IL Pretty Printer
-/

import VerifiedJS.Core.Syntax

namespace VerifiedJS.Core

def ind (n : Nat) : String := String.ofList (List.replicate (n * 2) ' ')

def printUnaryOp : UnaryOp → String
  | .neg => "-"
  | .pos => "+"
  | .bitNot => "~"
  | .logNot => "!"
  | .void => "void "

def printBinOp : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .exp => "**"
  | .eq => "==" | .neq => "!=" | .strictEq => "===" | .strictNeq => "!=="
  | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .shl => "<<" | .shr => ">>" | .ushr => ">>>"
  | .logAnd => "&&" | .logOr => "||"
  | .instanceof => "instanceof" | .«in» => "in"

def printValue : Value → String
  | .null => "null"
  | .undefined => "undefined"
  | .bool b => if b then "true" else "false"
  | .number n => toString n
  | .string s => "\"" ++ s ++ "\""
  | .object addr => s!"<object@{addr}>"
  | .function idx => s!"<func#{idx}>"

partial def printExpr (e : Expr) (indent : Nat := 0) : String :=
  let i := ind indent
  match e with
  | .lit v => printValue v
  | .var name => name
  | .«let» name init body =>
    i ++ "let " ++ name ++ " = " ++ printExpr init 0 ++ ";\n" ++ printExpr body indent
  | .assign name value => name ++ " = " ++ printExpr value 0
  | .«if» cond t e_ =>
    i ++ "if (" ++ printExpr cond 0 ++ ") {\n" ++ printExpr t (indent+1) ++ "\n" ++ i ++ "} else {\n" ++ printExpr e_ (indent+1) ++ "\n" ++ i ++ "}"
  | .seq a b => printExpr a indent ++ ";\n" ++ printExpr b indent
  | .call callee args =>
    let argStrs := args.map (printExpr · 0)
    printExpr callee 0 ++ "(" ++ String.intercalate ", " argStrs ++ ")"
  | .newObj callee args =>
    let argStrs := args.map (printExpr · 0)
    "new " ++ printExpr callee 0 ++ "(" ++ String.intercalate ", " argStrs ++ ")"
  | .getProp obj prop => printExpr obj 0 ++ "." ++ prop
  | .setProp obj prop value => printExpr obj 0 ++ "." ++ prop ++ " = " ++ printExpr value 0
  | .getIndex obj idx => printExpr obj 0 ++ "[" ++ printExpr idx 0 ++ "]"
  | .setIndex obj idx value => printExpr obj 0 ++ "[" ++ printExpr idx 0 ++ "] = " ++ printExpr value 0
  | .deleteProp obj prop => "delete " ++ printExpr obj 0 ++ "." ++ prop
  | .typeof arg => "typeof " ++ printExpr arg 0
  | .unary op arg => printUnaryOp op ++ printExpr arg 0
  | .binary op lhs rhs => "(" ++ printExpr lhs 0 ++ " " ++ printBinOp op ++ " " ++ printExpr rhs 0 ++ ")"
  | .objectLit props =>
    let i1 := ind (indent + 1)
    let ps := props.map fun (k, v) => i1 ++ k ++ ": " ++ printExpr v 0
    "{\n" ++ String.intercalate ",\n" ps ++ "\n" ++ i ++ "}"
  | .arrayLit elems =>
    let es := elems.map (printExpr · 0)
    "[" ++ String.intercalate ", " es ++ "]"
  | .functionDef name params body isAsync isGenerator =>
    let kw := (if isAsync then "async " else "") ++ (if isGenerator then "function*" else "function")
    let nameStr := match name with | some n => " " ++ n | none => ""
    kw ++ nameStr ++ "(" ++ String.intercalate ", " params ++ ") {\n" ++ printExpr body (indent+1) ++ "\n" ++ i ++ "}"
  | .throw arg => "throw " ++ printExpr arg 0
  | .tryCatch body catchParam catchBody finally_ =>
    let fin := match finally_ with
      | some f => " finally {\n" ++ printExpr f (indent+1) ++ "\n" ++ i ++ "}"
      | none => ""
    i ++ "try {\n" ++ printExpr body (indent+1) ++ "\n" ++ i ++ "} catch (" ++ catchParam ++ ") {\n" ++ printExpr catchBody (indent+1) ++ "\n" ++ i ++ "}" ++ fin
  | .while_ cond body =>
    i ++ "while (" ++ printExpr cond 0 ++ ") {\n" ++ printExpr body (indent+1) ++ "\n" ++ i ++ "}"
  | .«break» label => match label with | some l => "break " ++ l | none => "break"
  | .«continue» label => match label with | some l => "continue " ++ l | none => "continue"
  | .«return» arg => match arg with | some a => "return " ++ printExpr a 0 | none => "return"
  | .labeled label body => label ++ ": " ++ printExpr body indent
  | .yield arg delegate =>
    let star := if delegate then "*" else ""
    match arg with | some a => "yield" ++ star ++ " " ++ printExpr a 0 | none => "yield" ++ star
  | .await arg => "await " ++ printExpr arg 0
  | .this => "this"

def printFuncDef (f : FuncDef) : String :=
  let kw := (if f.isAsync then "async " else "") ++ (if f.isGenerator then "function*" else "function")
  kw ++ " " ++ f.name ++ "(" ++ String.intercalate ", " f.params ++ ") {\n" ++ printExpr f.body 1 ++ "\n}"

/-- Pretty-print a Core program -/
def printProgram (p : Program) : String :=
  let funcs := p.functions.toList.map printFuncDef
  let body := printExpr p.body 0
  String.intercalate "\n\n" (funcs ++ [body])

end VerifiedJS.Core
