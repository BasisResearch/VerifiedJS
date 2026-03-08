/-
  VerifiedJS — CLI Driver
  Main entry point for the compiler.
-/

import VerifiedJS.Source.Parser
import VerifiedJS.Core.Elaborate
import VerifiedJS.Core.Print
import VerifiedJS.Core.Interp
import VerifiedJS.Flat.ClosureConvert
import VerifiedJS.Flat.Print
import VerifiedJS.Flat.Interp
import VerifiedJS.ANF.Convert
import VerifiedJS.ANF.Optimize
import VerifiedJS.ANF.Print
import VerifiedJS.ANF.Interp
import VerifiedJS.Wasm.Lower
import VerifiedJS.Wasm.Emit
import VerifiedJS.Wasm.Print
import VerifiedJS.Wasm.Binary
import VerifiedJS.Wasm.IR
import VerifiedJS.Wasm.IRPrint
import VerifiedJS.Wasm.IRInterp
import VerifiedJS.Util

open VerifiedJS

/-- Helper: run pipeline through elaboration -/
private def elaborate (ast : Source.Program) : Except String Core.Program :=
  Core.elaborate ast

/-- Helper: run pipeline through closure conversion -/
private def toFlat (ast : Source.Program) : Except String Flat.Program := do
  let core ← elaborate ast
  Flat.closureConvert core

/-- Helper: run pipeline through ANF conversion + optimization -/
private def toANF (ast : Source.Program) : Except String ANF.Program := do
  let flat ← toFlat ast
  let anf ← ANF.convert flat
  pure (ANF.optimize anf)

/-- Helper: run pipeline through Wasm IR lowering -/
private def toWasmIR (ast : Source.Program) : Except String Wasm.IR.IRModule := do
  let anf ← toANF ast
  Wasm.lower anf

/-- Helper: run pipeline through Wasm AST emission -/
private def toWasm (ast : Source.Program) : Except String Wasm.Module := do
  let ir ← toWasmIR ast
  Wasm.emit ir

/-- Helper: print trace events from interpreters -/
private def printTrace (trace : List Core.TraceEvent) : IO Unit := do
  for event in trace do
    match event with
    | .log s => IO.println s
    | .error s => IO.eprintln s!"Error: {s}"
    | .silent => pure ()

/-- Emit targets for --emit flag -/
inductive EmitTarget where
  | core | flat | anf | wasmIR | wat
  deriving Repr, BEq

/-- Run targets for --run flag -/
inductive RunTarget where
  | core | flat | anf | wasmIR
  deriving Repr, BEq

def parseEmitTarget (s : String) : Option EmitTarget :=
  match s with
  | "core" => some .core
  | "flat" => some .flat
  | "anf" => some .anf
  | "wasmIR" => some .wasmIR
  | "wat" => some .wat
  | _ => none

def parseRunTarget (s : String) : Option RunTarget :=
  match s with
  | "core" => some .core
  | "flat" => some .flat
  | "anf" => some .anf
  | "wasmIR" => some .wasmIR
  | _ => none

def printUsage : IO Unit := do
  IO.println "Usage: verifiedjs <input.js> [options]"
  IO.println ""
  IO.println "Options:"
  IO.println "  -o <file>       Output .wasm file"
  IO.println "  --parse-only    Parse input and exit (no elaboration/lowering)"
  IO.println "  --emit=<target> Print intermediate representation"
  IO.println "                  Targets: core, flat, anf, wasmIR, wat"
  IO.println "  --run=<target>  Interpret at a given IL level"
  IO.println "                  Targets: core, flat, anf, wasmIR"
  IO.println "  --help          Show this help"

def findOutputFile : List String → String
  | "-o" :: path :: _ => path
  | _ :: rest => findOutputFile rest
  | [] => "output.wasm"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "--help" then
    printUsage
    return 0

  let inputFile := args.head!

  -- Read source file
  let source ← IO.FS.readFile ⟨inputFile⟩

  -- Parse
  let ast ← match Source.parse source with
    | .ok ast => pure ast
    | .error e => do IO.eprintln s!"Parse error: {e}"; return 1

  if args.contains "--parse-only" then
    let _ := ast
    IO.println "Parse OK"
    return 0

  -- Check for --emit flag
  for arg in args do
    if arg.startsWith "--emit=" then
      let target := (arg.drop 7).toString
      match parseEmitTarget target with
      | some .core => do
        match elaborate ast with
        | .ok core => IO.println (Core.printProgram core)
        | .error e => IO.eprintln s!"Elaboration error: {e}"
      | some .flat => do
        match toFlat ast with
        | .ok flat => IO.println (Flat.printProgram flat)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .anf => do
        match toANF ast with
        | .ok anf => IO.println (ANF.printProgram anf)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .wasmIR => do
        match toWasmIR ast with
        | .ok ir => IO.println (Wasm.IR.printModule ir)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .wat => do
        match toWasm ast with
        | .ok wasm => IO.println (Wasm.printWat wasm)
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | none => IO.eprintln s!"Unknown emit target: {target}"
      return 0

  -- Check for --run flag
  for arg in args do
    if arg.startsWith "--run=" then
      let target := (arg.drop 6).toString
      match parseRunTarget target with
      | some .core => do
        match elaborate ast with
        | .ok core => do
          let trace ← Core.interp core
          printTrace trace
        | .error e => IO.eprintln s!"Elaboration error: {e}"
      | some .flat => do
        match toFlat ast with
        | .ok flat => do
          let trace ← Flat.interp flat
          printTrace trace
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .anf => do
        match toANF ast with
        | .ok anf => do
          let trace ← ANF.interp anf
          printTrace trace
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | some .wasmIR => do
        match toWasmIR ast with
        | .ok ir => Wasm.IR.interp ir
        | .error e => IO.eprintln s!"Pipeline error: {e}"
      | none => IO.eprintln s!"Unknown run target: {target}"
      return 0

  -- Default: compile to wasm
  let outputFile := findOutputFile args

  match toWasm ast with
  | .ok wasm => do
    Wasm.writeWasm wasm outputFile
    IO.println s!"Compiled to {outputFile}"
    return 0
  | .error e => do
    IO.eprintln s!"Compilation error: {e}"
    return 1
