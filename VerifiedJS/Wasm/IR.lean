/-
  VerifiedJS — Wasm IR
  Structured control flow, Wasm types, linear memory ops.
  Higher-level than Wasm.AST, lower-level than ANF.
-/

import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm.IR

/-- Wasm IR types -/
inductive IRType where
  | i32 | i64 | f64 | ptr
  deriving Repr, BEq

/-- Wasm IR instructions — structured control flow -/
inductive IRInstr where
  | const_ (t : IRType) (v : String) -- string representation of value
  | localGet (idx : Nat)
  | localSet (idx : Nat)
  | globalGet (idx : Nat)
  | globalSet (idx : Nat)
  | load (t : IRType) (offset : Nat)
  | store (t : IRType) (offset : Nat)
  | binOp (t : IRType) (op : String) -- e.g., "add", "sub"
  | unOp (t : IRType) (op : String)
  | call (funcIdx : Nat)
  | callIndirect (typeIdx : Nat)
  | block (label : String) (body : List IRInstr)
  | loop (label : String) (body : List IRInstr)
  | if_ (then_ : List IRInstr) (else_ : List IRInstr)
  | br (label : String)
  | brIf (label : String)
  | return_
  | drop
  | memoryGrow
  deriving Repr

/-- Wasm IR function -/
structure IRFunc where
  name : String
  params : List IRType
  results : List IRType
  locals : List IRType
  body : List IRInstr
  deriving Repr

/-- Wasm IR module -/
structure IRModule where
  functions : Array IRFunc
  memories : Array Wasm.Memory
  globals : Array (IRType × Bool × String) -- type, mutable, init value
  exports : Array (String × Nat)  -- name, func idx
  dataSegments : Array (Nat × ByteArray) -- offset, data
  startFunc : Option Nat
  deriving Repr

end VerifiedJS.Wasm.IR
