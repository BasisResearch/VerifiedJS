/-
  LeanSplitter: Parse Lean files using Lean's parser + elaborator, output structured JSON.
  Uses the full Lean frontend (Elab.IO.processCommands) so the parser gets correct
  namespace/env state between commands — no truncated declarations.
  Compiled: `lake build leansplitter`
  Run: `lake env .lake/build/bin/leansplitter <file.lean>`
-/
import Batteries.Data.String
import Lean
import Lean.Elab.Frontend

open Lean

def lineOfPos (source : String) (pos : String.Pos.Raw) : Nat := Id.run do
  let bytes := source.toUTF8
  let limit := min pos.byteIdx bytes.size
  let mut n : Nat := 1
  for i in [:limit] do
    if bytes[i]! == 10 then n := n + 1
  return n

def textSlice (source : String) (startByte endByte : Nat) : String :=
  let bytes := source.toUTF8
  let s := min startByte bytes.size
  let e := min endByte bytes.size
  let slice := bytes.extract s e
  if h : slice.IsValidUTF8 then ⟨slice, h⟩
  else String.ofList ((source.toList.drop s).take (e - s))

def classifyKind (k : Name) : Option String :=
  let s := k.toString
  if s.containsSubstr "theorem" then some "theorem"
  else if s.containsSubstr "lemma" then some "lemma"
  else if s.containsSubstr "inductive" then some "inductive"
  else if s.containsSubstr "structure" then some "structure"
  else if s.containsSubstr "instance" then some "instance"
  else if s.containsSubstr "axiom" then some "axiom"
  else if s.containsSubstr "abbrev" then some "abbrev"
  else if s.containsSubstr "definition" || s.containsSubstr "noncomputableDef" then some "def"
  else none

partial def findName (stx : Syntax) : Option String :=
  match stx with
  | .node _ kind args =>
    if kind.toString.containsSubstr "declId" then
      args.findSome? fun | .ident _ _ n _ => some n.toString | _ => none
    else args.findSome? findName
  | .ident _ _ n _ => some n.toString
  | _ => none

partial def collectCases (source : String) (stx : Syntax) : Array Json := Id.run do
  let mut result : Array Json := #[]
  match stx with
  | .node _ kind args =>
    let k := kind.toString
    if k.containsSubstr "matchAlt" || k.containsSubstr "ctor" then
      let sp := stx.getPos? (canonicalOnly := false) |>.getD ⟨0⟩
      let ep := stx.getTailPos? (canonicalOnly := false) |>.getD ⟨0⟩
      let name := findCaseIdent stx |>.getD "?"
      result := result.push (Json.mkObj [
        ("name", name), ("start_line", lineOfPos source sp),
        ("end_line", lineOfPos source ep),
        ("text", textSlice source sp.byteIdx ep.byteIdx)])
    else
      for arg in args do
        result := result ++ collectCases source arg
  | _ => ()
  return result
where
  findCaseIdent : Syntax → Option String
    | .ident _ _ n _ =>
      let s := n.toString
      if s != "|" && s != "=>" && s != "with" && s != "match" then some s else none
    | .node _ _ args => args.findSome? findCaseIdent
    | _ => none

/-- Build a JSON object for a declaration.
    startByte/endByte come from the gap between consecutive commands. -/
def mkDeclJson (source : String) (stx : Syntax) (startByte endByte : Nat) : Option Json := do
  let kind ← match stx with
    | .node _ k _ => classifyKind k
    | _ => none
  let name := findName stx |>.getD "?"
  let text := textSlice source startByte endByte
  let cases := collectCases source stx
  return Json.mkObj [
    ("kind", kind), ("name", name),
    ("start_line", lineOfPos source ⟨startByte⟩),
    ("end_line", lineOfPos source ⟨endByte⟩),
    ("has_sorry", text.containsSubstr "sorry"),
    ("is_private", match stx with | .node _ k _ => k.toString.containsSubstr "private" | _ => false),
    ("num_cases", cases.size), ("cases", Json.arr cases),
    ("text", text)]

/-- Extract declarations from a command syntax tree. Walks into namespace/section blocks. -/
partial def extractDecls (source : String) (cmd : Syntax) (startByte endByte : Nat) : Array Json := Id.run do
  let mut decls : Array Json := #[]
  -- Try top-level classification
  match mkDeclJson source cmd startByte endByte with
  | some j => decls := decls.push j
  | none =>
    match cmd with
    | .node _ _ args =>
      for arg in args do
        match mkDeclJson source arg startByte endByte with
        | some j => decls := decls.push j
        | none =>
          match arg with
          | .node _ _ inner =>
            for x in inner do
              match mkDeclJson source x startByte endByte with
              | some j => decls := decls.push j
              | none => pure ()
          | _ => pure ()
    | _ => pure ()
  return decls

unsafe def main (args : List String) : IO Unit := do
  let path ← match args.head? with
    | some p => pure p
    | none => do IO.eprintln "Usage: leansplitter <file.lean>"; IO.Process.exit 1

  let source ← IO.FS.readFile path
  let ictx := Parser.mkInputContext source path
  let (header, parserState, _) ← Parser.parseHeader ictx

  -- Initialize search path and import the file's actual modules
  initSearchPath (← findSysroot)
  let imports := Elab.headerToImports header
  IO.eprintln s!"Importing {imports.size} modules..."
  let env ← importModules imports {} 0
  IO.eprintln "Environment loaded, running frontend..."

  -- Run the full Lean frontend: parse + elaborate each command with proper state
  let commandState := Elab.Command.mkState env {} {}
  let state ← Elab.IO.processCommands ictx parserState commandState
  let commands := state.commands

  IO.eprintln s!"Processed {commands.size} commands."

  let debug := args.contains "--debug"
  let sourceBytes := source.utf8ByteSize

  -- Derive byte ranges from consecutive command start positions
  let mut decls : Array Json := #[]
  for i in [:commands.size] do
    let cmd := commands[i]!
    let startByte := cmd.getPos? (canonicalOnly := false) |>.map (·.byteIdx) |>.getD 0
    let endByte :=
      if i + 1 < commands.size then
        commands[i+1]!.getPos? (canonicalOnly := false) |>.map (·.byteIdx) |>.getD sourceBytes
      else sourceBytes

    if debug then
      let kindStr := match cmd with | .node _ k _ => k.toString | _ => "?"
      let sl := lineOfPos source ⟨startByte⟩
      let el := lineOfPos source ⟨endByte⟩
      IO.eprintln s!"CMD[{i}] L{sl}-L{el} kind={kindStr}"

    decls := decls ++ extractDecls source cmd startByte endByte

  IO.println (Json.arr decls).pretty
