/-
  VerifiedJS — Wasm Execution Semantics
  Small-step reduction: store, stack, frames.
  Ported from WasmCert-Coq `theories/operations.v`.
-/

import VerifiedJS.Wasm.Syntax

namespace VerifiedJS.Wasm

/-- Wasm runtime values -/
inductive WasmValue where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  | f32 (n : Float)
  | f64 (n : Float)
  deriving Repr, BEq

/-- Wasm store -/
structure Store where
  funcs : Array Func
  tables : Array (Array (Option Nat))
  memories : Array ByteArray
  globals : Array WasmValue

/-- Wasm frame -/
structure Frame where
  locals : Array WasmValue
  moduleInst : Nat
  deriving Repr

/-- Wasm execution state -/
structure ExecState where
  store : Store
  stack : List WasmValue
  frames : List Frame
  code : List Instr

/-- Small-step reduction for Wasm -/
inductive Step : ExecState → ExecState → Prop where
  -- TODO: Define Wasm reduction rules
  | placeholder (s : ExecState) : Step s s

end VerifiedJS.Wasm
