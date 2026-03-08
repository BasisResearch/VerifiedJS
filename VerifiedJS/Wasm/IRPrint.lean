/-
  VerifiedJS — Wasm IR Pretty Printer
-/

import VerifiedJS.Wasm.IR

namespace VerifiedJS.Wasm.IR

def printIRType : IRType → String
  | .i32 => "i32" | .i64 => "i64" | .f64 => "f64" | .ptr => "ptr"

partial def printInstr (instr : IRInstr) (indent : Nat := 0) : String :=
  let i := String.ofList (List.replicate (indent * 2) ' ')
  match instr with
  | .const_ t v => s!"{i}{printIRType t}.const {v}"
  | .localGet idx => s!"{i}local.get {idx}"
  | .localSet idx => s!"{i}local.set {idx}"
  | .globalGet idx => s!"{i}global.get {idx}"
  | .globalSet idx => s!"{i}global.set {idx}"
  | .load t offset => s!"{i}{printIRType t}.load offset={offset}"
  | .store t offset => s!"{i}{printIRType t}.store offset={offset}"
  | .binOp t op => s!"{i}{printIRType t}.{op}"
  | .unOp t op => s!"{i}{printIRType t}.{op}"
  | .call funcIdx => s!"{i}call {funcIdx}"
  | .callIndirect typeIdx => s!"{i}call_indirect {typeIdx}"
  | .block label body =>
    let bodyStrs := body.map (printInstr · (indent + 1))
    s!"{i}block ${label}\n{String.intercalate "\n" bodyStrs}\n{i}end"
  | .loop label body =>
    let bodyStrs := body.map (printInstr · (indent + 1))
    s!"{i}loop ${label}\n{String.intercalate "\n" bodyStrs}\n{i}end"
  | .if_ then_ else_ =>
    let thenStrs := then_.map (printInstr · (indent + 1))
    let elseStrs := else_.map (printInstr · (indent + 1))
    if else_.isEmpty then
      s!"{i}if\n{String.intercalate "\n" thenStrs}\n{i}end"
    else
      s!"{i}if\n{String.intercalate "\n" thenStrs}\n{i}else\n{String.intercalate "\n" elseStrs}\n{i}end"
  | .br label => s!"{i}br ${label}"
  | .brIf label => s!"{i}br_if ${label}"
  | .return_ => s!"{i}return"
  | .drop => s!"{i}drop"
  | .memoryGrow => s!"{i}memory.grow"

def printFunc (f : IRFunc) (idx : Nat) : String :=
  let paramStrs := f.params.map printIRType
  let resultStrs := f.results.map printIRType
  let localStrs := f.locals.map printIRType
  let bodyStrs := f.body.map (printInstr · 1)
  let header := s!"(func ${f.name} (;{idx};)"
  let params := if paramStrs.isEmpty then "" else s!" (param {String.intercalate " " paramStrs})"
  let results := if resultStrs.isEmpty then "" else s!" (result {String.intercalate " " resultStrs})"
  let locals := if localStrs.isEmpty then "" else s!"\n  (local {String.intercalate " " localStrs})"
  s!"{header}{params}{results}{locals}\n{String.intercalate "\n" bodyStrs}\n)"

def printModule (m : IRModule) : String :=
  let indexed := m.functions.toList.zip (List.range m.functions.size)
  let funcs := indexed.map fun (f, i) => printFunc f i
  let exports := m.exports.toList.map fun (name, idx) => s!"(export \"{name}\" (func {idx}))"
  let globals := m.globals.toList.map fun (t, isMut, init) =>
    let mutStr := if isMut then "(mut " ++ printIRType t ++ ")" else printIRType t
    "(global " ++ mutStr ++ " (" ++ printIRType t ++ ".const " ++ init ++ "))"
  let start := match m.startFunc with
    | some idx => [s!"(start {idx})"]
    | none => []
  let parts := ["(module"] ++ globals ++ funcs ++ exports ++ start ++ [")"]
  String.intercalate "\n" parts

end VerifiedJS.Wasm.IR
