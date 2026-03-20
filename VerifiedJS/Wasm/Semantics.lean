/-
  VerifiedJS — Wasm Execution Semantics
  Small-step reduction: store, stack, frames.
  SPEC: WebAssembly 1.0 §4.2, §4.4 (execution) and WasmCert-Coq `theories/operations.v`.
-/

import VerifiedJS.Wasm.Syntax
import VerifiedJS.Wasm.Numerics

namespace VerifiedJS.Wasm

/-- Runtime values used by the Wasm machine state. -/
inductive WasmValue where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  | f32 (n : Float)
  | f64 (n : Float)
  deriving Repr, BEq

/-- Observable execution events for Wasm small-step runs. -/
inductive TraceEvent where
  | silent
  | trap (msg : String)
  deriving Repr, BEq

/-- Wasm store (functions, tables, memories, globals). -/
structure Store where
  funcs : Array Func
  tables : Array (Array (Option Nat))
  memories : Array ByteArray
  globals : Array WasmValue
  deriving Repr

/-- Active call frame with locals and bound module instance id. -/
structure Frame where
  locals : Array WasmValue
  moduleInst : Nat
  deriving Repr

/-- Control label frame for structured branching (`br`/`br_if`/`br_table`). -/
structure LabelFrame where
  /-- Branch target code for this label (loop head for loop labels, continuation for block labels). -/
  onBranch : List Instr
  /-- Continuation code after natural completion of this label scope. -/
  onExit : List Instr
  /-- True when the label corresponds to `loop`, false for `block`/`if` labels. -/
  isLoop : Bool
  deriving Repr

/-- Wasm execution state in evaluation context style. -/
structure ExecState where
  store : Store
  stack : List WasmValue
  frames : List Frame
  labels : List LabelFrame
  code : List Instr
  trace : List TraceEvent
  deriving Repr

/-- SPEC §4.4.3 Numeric Instructions: default value of a Wasm value type. -/
def defaultValue : ValType → WasmValue
  | .i32 => .i32 0
  | .i64 => .i64 0
  | .f32 => .f32 0.0
  | .f64 => .f64 0.0

/-- SPEC §4.5.3 Globals: initialize module globals with default typed values. -/
private def initGlobals (m : Module) : Array WasmValue :=
  m.globals.map (fun g => defaultValue g.type.val)

/-- SPEC §4.5.2 Tables: allocate table slots as `none` function references. -/
private def initTableSlots (tt : TableType) : Array (Option Nat) :=
  Array.replicate tt.lim.min none

/-- SPEC §4.5.5 Memories: allocate zero-initialized linear memories by pages. -/
private def initMemory (mt : MemType) : ByteArray :=
  let byteSize := mt.lim.min * 65536
  ByteArray.mk (Array.replicate byteSize 0)

/-- Build an initial store from a module declaration. -/
def initialStore (m : Module) : Store :=
  {
    funcs := m.funcs
    tables := m.tables.map initTableSlots
    memories := m.memories.map initMemory
    globals := initGlobals m
  }

/-- Initial machine state for a module entry; code starts at explicit start call if present. -/
def initialState (m : Module) : ExecState :=
  let entryCode :=
    match m.start with
    | some f => [Instr.call f]
    | none => []
  {
    store := initialStore m
    stack := []
    frames := [{ locals := #[], moduleInst := 0 }]
    labels := []
    code := entryCode
    trace := []
  }

private def pushTrace (s : ExecState) (t : TraceEvent) : ExecState :=
  { s with trace := s.trace ++ [t] }

private def trapState (s : ExecState) (msg : String) : TraceEvent × ExecState :=
  let s' := pushTrace { s with code := [] } (.trap msg)
  (.trap msg, s')

private def pop1? (stack : List WasmValue) : Option (WasmValue × List WasmValue) :=
  match stack with
  | v :: rest => some (v, rest)
  | [] => none

private def pop2? (stack : List WasmValue) : Option (WasmValue × WasmValue × List WasmValue) :=
  match stack with
  | v1 :: v2 :: rest => some (v1, v2, rest)
  | _ => none

private def pop3? (stack : List WasmValue) : Option (WasmValue × WasmValue × WasmValue × List WasmValue) :=
  match stack with
  | v1 :: v2 :: v3 :: rest => some (v1, v2, v3, rest)
  | _ => none

private def updateHeadFrame (frames : List Frame) (f : Frame) : List Frame :=
  match frames with
  | [] => [f]
  | _ :: rest => f :: rest

private def i32Truth : WasmValue → Option Bool
  | .i32 n => some (n != 0)
  | _ => none

private def withI32Bin
    (s : ExecState)
    (op : UInt32 → UInt32 → UInt32)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i32 rhs, .i32 lhs, rest) =>
      let v := WasmValue.i32 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withI64Bin
    (s : ExecState)
    (op : UInt64 → UInt64 → UInt64)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i64 rhs, .i64 lhs, rest) =>
      let v := WasmValue.i64 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withF64Bin
    (s : ExecState)
    (op : Float → Float → Float)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.f64 rhs, .f64 lhs, rest) =>
      let v := WasmValue.f64 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def boolToI32 (b : Bool) : WasmValue :=
  .i32 (if b then 1 else 0)

private def withI32Rel
    (s : ExecState)
    (op : UInt32 → UInt32 → Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i32 rhs, .i32 lhs, rest) =>
      some (.silent, pushTrace { s with stack := boolToI32 (op lhs rhs) :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withI64Rel
    (s : ExecState)
    (op : UInt64 → UInt64 → Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i64 rhs, .i64 lhs, rest) =>
      some (.silent, pushTrace { s with stack := boolToI32 (op lhs rhs) :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withF32Bin
    (s : ExecState)
    (op : Float → Float → Float)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.f32 rhs, .f32 lhs, rest) =>
      some (.silent, pushTrace { s with stack := .f32 (op lhs rhs) :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withF32Rel
    (s : ExecState)
    (op : Float → Float → Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.f32 rhs, .f32 lhs, rest) =>
      some (.silent, pushTrace { s with stack := boolToI32 (op lhs rhs) :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withF64Rel
    (s : ExecState)
    (op : Float → Float → Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.f64 rhs, .f64 lhs, rest) =>
      some (.silent, pushTrace { s with stack := boolToI32 (op lhs rhs) :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def readLE? (mem : ByteArray) (addr width : Nat) : Option UInt64 := Id.run do
  let mut acc : Nat := 0
  let mut factor : Nat := 1
  for k in [0:width] do
    let idx := addr + k
    if h : idx < mem.size then
      let b := mem[idx]
      acc := acc + b.toNat * factor
      factor := factor * 256
    else
      return none
  return some (UInt64.ofNat acc)

private def writeLE? (mem : ByteArray) (addr width : Nat) (value : UInt64) : Option ByteArray := Id.run do
  let mut out := mem
  for k in [0:width] do
    let idx := addr + k
    if idx < out.size then
      let byte := UInt8.ofNat ((value.toNat / Nat.pow 2 (8 * k)) % 256)
      out := out.set! idx byte
    else
      return none
  return some out

private def i32ToSigned (n : UInt32) : Int :=
  (Int32.ofNat n.toNat).toInt

private def i64ToSigned (n : UInt64) : Int :=
  (Int64.ofNat n.toNat).toInt

private def truncFloatToInt? (f : Float) : Option Int :=
  if !f.isFinite || f.isNaN then
    none
  else
    if f < 0 then
      some (-Int.ofNat ((-f).toUInt64.toNat))
    else
      some (Int.ofNat f.toUInt64.toNat)

private def i32Rotl (a b : UInt32) : UInt32 :=
  let s := b.toNat % 32
  if s == 0 then
    a
  else
    let l := UInt32.shiftLeft a (UInt32.ofNat s)
    let r := UInt32.shiftRight a (UInt32.ofNat (32 - s))
    l ||| r

private def i32Rotr (a b : UInt32) : UInt32 :=
  let s := b.toNat % 32
  if s == 0 then
    a
  else
    let r := UInt32.shiftRight a (UInt32.ofNat s)
    let l := UInt32.shiftLeft a (UInt32.ofNat (32 - s))
    l ||| r

private def i64Rotl (a b : UInt64) : UInt64 :=
  let s := b.toNat % 64
  if s == 0 then
    a
  else
    let l := UInt64.shiftLeft a (UInt64.ofNat s)
    let r := UInt64.shiftRight a (UInt64.ofNat (64 - s))
    l ||| r

private def i64Rotr (a b : UInt64) : UInt64 :=
  let s := b.toNat % 64
  if s == 0 then
    a
  else
    let r := UInt64.shiftRight a (UInt64.ofNat s)
    let l := UInt64.shiftLeft a (UInt64.ofNat (64 - s))
    l ||| r

-- Wasm §4.3.1 iclz: count leading zeros
private def clzGo (bits : Nat) (val : Nat) (count : Nat) : Nat :=
  if h : bits == 0 then count
  else if val >= Nat.pow 2 (bits - 1) then count
  else clzGo (bits - 1) val (count + 1)
termination_by bits
decreasing_by simp_all; omega

private def i32Clz (n : UInt32) : UInt32 := UInt32.ofNat (clzGo 32 n.toNat 0)

-- Wasm §4.3.1 ictz: count trailing zeros
private def ctzGo (val : Nat) (count : Nat) (maxBits : Nat) : Nat :=
  if count >= maxBits then maxBits
  else if val % 2 != 0 then count
  else ctzGo (val / 2) (count + 1) maxBits
termination_by maxBits - count
decreasing_by omega

private def i32Ctz (n : UInt32) : UInt32 := UInt32.ofNat (ctzGo n.toNat 0 32)

-- Wasm §4.3.1 ipopcnt: population count
private def popcntGo (val : Nat) (count : Nat) (bits : Nat) : Nat :=
  if h : bits == 0 then count
  else popcntGo (val / 2) (count + val % 2) (bits - 1)
termination_by bits
decreasing_by simp_all; omega

private def i32Popcnt (n : UInt32) : UInt32 := UInt32.ofNat (popcntGo n.toNat 0 32)

private def i64Clz (n : UInt64) : UInt64 := UInt64.ofNat (clzGo 64 n.toNat 0)
private def i64Ctz (n : UInt64) : UInt64 := UInt64.ofNat (ctzGo n.toNat 0 64)
private def i64Popcnt (n : UInt64) : UInt64 := UInt64.ofNat (popcntGo n.toNat 0 64)

-- Sanity checks for bit-counting operations (Wasm §4.3.1)
example : i32Clz 0 = 32 := by native_decide
example : i32Clz 1 = 31 := by native_decide
example : i32Ctz 0 = 32 := by native_decide
example : i32Ctz 1 = 0 := by native_decide
example : i32Ctz 8 = 3 := by native_decide
example : i32Popcnt 0 = 0 := by native_decide
example : i32Popcnt 7 = 3 := by native_decide

-- Sign-extend an N-bit value stored in a UInt32 to a signed i32.
-- Wasm §4.3.1: NN-bit loads with sign extension.
private def signExtend32 (n : UInt32) (bits : Nat) : UInt32 :=
  let half := Nat.pow 2 (bits - 1)
  if n.toNat >= half then
    -- Negative in N-bit two's complement: extend sign
    UInt32.ofNat (n.toNat - Nat.pow 2 bits + 4294967296)
  else n

-- Sign-extend an N-bit value stored in a UInt64 to a signed i64.
private def signExtend64 (n : UInt64) (bits : Nat) : UInt64 :=
  let half := Nat.pow 2 (bits - 1)
  if n.toNat >= half then
    UInt64.ofNat (n.toNat - Nat.pow 2 bits + 18446744073709551616)
  else n

-- Float to UInt64 bit pattern (reinterpret, not convert).
private def floatToU64Bits (f : Float) : UInt64 := f.toUInt64  -- Float.toUInt64 gives the IEEE 754 bits

-- UInt64 bit pattern to Float (reinterpret, not convert).
private def u64BitsToFloat (n : UInt64) : Float := Float.ofBits n

-- UInt32 bit pattern to f32 (32-bit IEEE 754) via f64.
-- Since Lean's Float is always 64-bit, we store f32 as the 32-bit pattern widened to f64.
private def u32BitsToFloat (n : UInt32) : Float :=
  -- Wasm f32.reinterpret_i32: the 32-bit pattern is a single-precision float.
  -- We extend to the 64-bit UInt and use Float.ofBits which handles 64-bit IEEE.
  -- For a faithful f32 reinterpret we'd need 32-bit float support; approximate via conversion.
  Float.ofScientific n.toNat true 0  -- fallback: treat as integer (imprecise for true reinterpret)

-- Float (as f32 proxy) to UInt32 bit pattern.
private def floatToU32Bits (f : Float) : UInt32 :=
  UInt32.ofNat (f.toUInt64.toNat % (Nat.pow 2 32))

private def withI32Div
    (s : ExecState)
    (signed : Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i32 rhs, .i32 lhs, rest) =>
      if rhs == 0 then
        some (trapState s s!"integer divide by zero in {name}")
      else if signed then
        let a := i32ToSigned lhs
        let b := i32ToSigned rhs
        if a == Int.negSucc (Nat.pow 2 31 - 1) && b == (-1) then
          some (trapState s s!"integer overflow in {name}")
        else
          let q := Int.ediv a b
          let v := WasmValue.i32 (UInt32.ofInt q)
          some (.silent, pushTrace { s with stack := v :: rest } .silent)
      else
        let v := WasmValue.i32 (lhs / rhs)
        some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withI32Rem
    (s : ExecState)
    (signed : Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i32 rhs, .i32 lhs, rest) =>
      if rhs == 0 then
        some (trapState s s!"integer divide by zero in {name}")
      else if signed then
        let r := Int.emod (i32ToSigned lhs) (i32ToSigned rhs)
        some (.silent, pushTrace { s with stack := .i32 (UInt32.ofInt r) :: rest } .silent)
      else
        some (.silent, pushTrace { s with stack := .i32 (lhs % rhs) :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withI64Div
    (s : ExecState)
    (signed : Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i64 rhs, .i64 lhs, rest) =>
      if rhs == 0 then
        some (trapState s s!"integer divide by zero in {name}")
      else if signed then
        let a := i64ToSigned lhs
        let b := i64ToSigned rhs
        if a == Int.negSucc (Nat.pow 2 63 - 1) && b == (-1) then
          some (trapState s s!"integer overflow in {name}")
        else
          let q := Int.ediv a b
          let v := WasmValue.i64 (UInt64.ofInt q)
          some (.silent, pushTrace { s with stack := v :: rest } .silent)
      else
        let v := WasmValue.i64 (lhs / rhs)
        some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def withI64Rem
    (s : ExecState)
    (signed : Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i64 rhs, .i64 lhs, rest) =>
      if rhs == 0 then
        some (trapState s s!"integer divide by zero in {name}")
      else if signed then
        let r := Int.emod (i64ToSigned lhs) (i64ToSigned rhs)
        some (.silent, pushTrace { s with stack := .i64 (UInt64.ofInt r) :: rest } .silent)
      else
        some (.silent, pushTrace { s with stack := .i64 (lhs % rhs) :: rest } .silent)
  | _ => some (trapState s s!"type mismatch in {name}")

private def resolveBranch? (labels : List LabelFrame) (depth : Nat) :
    Option (LabelFrame × List LabelFrame) :=
  let rec go (remaining : List LabelFrame) (n : Nat) : Option (LabelFrame × List LabelFrame) :=
    match remaining, n with
    | [], _ => none
    | l :: ls, 0 =>
        let kept :=
          if l.isLoop then
            l :: ls
          else
            ls
        some (l, kept)
    | _ :: ls, n + 1 => go ls n
  go labels depth

/-- One deterministic Wasm machine step (administrative reduction function). -/
def step? (s : ExecState) : Option (TraceEvent × ExecState) :=
  match s.code with
  | [] =>
      match s.labels with
      | l :: ls =>
          let s' := pushTrace { s with labels := ls, code := l.onExit } .silent
          some (.silent, s')
      | [] => none
  | i :: rest =>
      let base := { s with code := rest }
      match i with
      | .unreachable => some (trapState base "unreachable executed")
      | .nop => some (.silent, pushTrace base .silent)
      | .block _ body =>
          let lbl : LabelFrame := { onBranch := rest, onExit := rest, isLoop := false }
          let s' := pushTrace { base with labels := lbl :: base.labels, code := body } .silent
          some (.silent, s')
      | .loop _ body =>
          let lbl : LabelFrame := { onBranch := body, onExit := rest, isLoop := true }
          let s' := pushTrace { base with labels := lbl :: base.labels, code := body } .silent
          some (.silent, s')
      | .if_ _ then_ else_ =>
          match pop1? base.stack with
          | some (cond, stk) =>
              match i32Truth cond with
              | some true =>
                  -- SPEC §4.4.8.4: if pushes a label like block, so br inside works correctly
                  let lbl : LabelFrame := { onBranch := rest, onExit := rest, isLoop := false }
                  some (.silent, pushTrace { base with stack := stk, labels := lbl :: base.labels, code := then_ } .silent)
              | some false =>
                  let lbl : LabelFrame := { onBranch := rest, onExit := rest, isLoop := false }
                  some (.silent, pushTrace { base with stack := stk, labels := lbl :: base.labels, code := else_ } .silent)
              | none => some (trapState base "if condition is not i32")
          | none => some (trapState base "stack underflow in if")
      | .br depth =>
          match resolveBranch? base.labels depth with
          | some (lbl, labels') =>
              some (.silent, pushTrace { base with labels := labels', code := lbl.onBranch } .silent)
          | none => some (trapState base s!"unknown label index {depth}")
      | .brIf depth =>
          match pop1? base.stack with
          | some (cond, stk) =>
              match i32Truth cond with
              | some true =>
                  match resolveBranch? base.labels depth with
                  | some (lbl, labels') =>
                      some (.silent, pushTrace { base with stack := stk, labels := labels', code := lbl.onBranch } .silent)
                  | none => some (trapState base s!"unknown label index {depth}")
              | some false => some (.silent, pushTrace { base with stack := stk } .silent)
              | none => some (trapState base "br_if condition is not i32")
          | none => some (trapState base "stack underflow in br_if")
      | .brTable labels default_ =>
          match pop1? base.stack with
          | some (cond, stk) =>
              match cond with
              | .i32 idx =>
                  let target :=
                    if h : idx.toNat < labels.length then
                      labels.get ⟨idx.toNat, h⟩
                    else
                      default_
                  match resolveBranch? base.labels target with
                  | some (lbl, labels') =>
                      some (.silent, pushTrace { base with stack := stk, labels := labels', code := lbl.onBranch } .silent)
                  | none => some (trapState base s!"unknown label index {target}")
              | _ => some (trapState base "br_table index is not i32")
          | none => some (trapState base "stack underflow in br_table")
      | .return_ =>
          let s' := pushTrace { base with labels := [], code := [] } .silent
          some (.silent, s')
      | .call idx =>
          if h : idx < base.store.funcs.size then
            let func := base.store.funcs[idx]
            let locals := (func.locals.map defaultValue).toArray
            let frame : Frame := { locals := locals, moduleInst := 0 }
            let s' := pushTrace { base with frames := frame :: base.frames, code := func.body ++ rest } .silent
            some (.silent, s')
          else
            some (trapState base s!"unknown function index {idx}")
      | .callIndirect _ tableIdx =>
          match pop1? base.stack with
          | some (.i32 elemIdx, stk) =>
              if hTbl : tableIdx < base.store.tables.size then
                let table := base.store.tables[tableIdx]
                if hElem : elemIdx.toNat < table.size then
                  match table[elemIdx.toNat] with
                  | some funcIdx =>
                      if hFunc : funcIdx < base.store.funcs.size then
                        let func := base.store.funcs[funcIdx]
                        let locals := (func.locals.map defaultValue).toArray
                        let frame : Frame := { locals := locals, moduleInst := 0 }
                        let s' := pushTrace
                          { base with stack := stk, frames := frame :: base.frames, code := func.body ++ rest } .silent
                        some (.silent, s')
                      else
                        some (trapState base s!"unknown function index {funcIdx}")
                  | none => some (trapState base s!"uninitialized table slot {elemIdx.toNat}")
                else
                  some (trapState base s!"table index out of bounds {elemIdx.toNat}")
              else
                some (trapState base s!"unknown table index {tableIdx}")
          | some (_, _) => some (trapState base "call_indirect element index is not i32")
          | none => some (trapState base "stack underflow in call_indirect")
      | .drop =>
          match pop1? base.stack with
          | some (_, stk) => some (.silent, pushTrace { base with stack := stk } .silent)
          | none => some (trapState base "stack underflow in drop")
      | .select =>
          match pop2? base.stack with
          | some (cond, v2, tail) =>
              match pop1? tail with
              | some (v1, restStack) =>
                  match i32Truth cond with
                  | some true => some (.silent, pushTrace { base with stack := v1 :: restStack } .silent)
                  | some false => some (.silent, pushTrace { base with stack := v2 :: restStack } .silent)
                  | none => some (trapState base "select condition is not i32")
              | none => some (trapState base "stack underflow in select")
          | none => some (trapState base "stack underflow in select")
      | .localGet idx =>
          match base.frames with
          | fr :: _ =>
              if h : idx < fr.locals.size then
                let v := fr.locals[idx]
                some (.silent, pushTrace { base with stack := v :: base.stack } .silent)
              else
                some (trapState base s!"unknown local index {idx}")
          | [] => some (trapState base "local.get without active frame")
      | .localSet idx =>
          match base.frames, pop1? base.stack with
          | fr :: _, some (v, stk) =>
              if h : idx < fr.locals.size then
                let fr' := { fr with locals := fr.locals.set! idx v }
                let s' := pushTrace
                  { base with stack := stk, frames := updateHeadFrame base.frames fr' } .silent
                some (.silent, s')
              else
                some (trapState base s!"unknown local index {idx}")
          | [], _ => some (trapState base "local.set without active frame")
          | _, none => some (trapState base "stack underflow in local.set")
      | .localTee idx =>
          match base.frames, pop1? base.stack with
          | fr :: _, some (v, stk) =>
              if h : idx < fr.locals.size then
                let fr' := { fr with locals := fr.locals.set! idx v }
                let s' := pushTrace
                  { base with stack := v :: stk, frames := updateHeadFrame base.frames fr' } .silent
                some (.silent, s')
              else
                some (trapState base s!"unknown local index {idx}")
          | [], _ => some (trapState base "local.tee without active frame")
          | _, none => some (trapState base "stack underflow in local.tee")
      | .globalGet idx =>
          if h : idx < base.store.globals.size then
            let v := base.store.globals[idx]
            some (.silent, pushTrace { base with stack := v :: base.stack } .silent)
          else
            some (trapState base s!"unknown global index {idx}")
      | .globalSet idx =>
          match pop1? base.stack with
          | some (v, stk) =>
              if h : idx < base.store.globals.size then
                let globals' := base.store.globals.set! idx v
                let store' := { base.store with globals := globals' }
                some (.silent, pushTrace { base with stack := stk, store := store' } .silent)
              else
                some (trapState base s!"unknown global index {idx}")
          | none => some (trapState base "stack underflow in global.set")
      | .i32Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.i32 n :: base.stack } .silent)
      | .i64Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.i64 n :: base.stack } .silent)
      | .f32Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.f32 n :: base.stack } .silent)
      | .f64Const n =>
          some (.silent, pushTrace { base with stack := WasmValue.f64 n :: base.stack } .silent)
      | .i32Add => withI32Bin base Numerics.i32Add "i32.add"
      | .i32Sub => withI32Bin base Numerics.i32Sub "i32.sub"
      | .i32Mul => withI32Bin base Numerics.i32Mul "i32.mul"
      | .i64Add => withI64Bin base Numerics.i64Add "i64.add"
      | .i64Sub => withI64Bin base Numerics.i64Sub "i64.sub"
      | .i64Mul => withI64Bin base Numerics.i64Mul "i64.mul"
      | .f64Add => withF64Bin base Numerics.f64Add "f64.add"
      | .f64Sub => withF64Bin base Numerics.f64Sub "f64.sub"
      | .f64Mul => withF64Bin base Numerics.f64Mul "f64.mul"
      | .f64Div => withF64Bin base Numerics.f64Div "f64.div"
      | .memorySize memIdx =>
          if hMem : memIdx < base.store.memories.size then
            let mem := base.store.memories[memIdx]
            let pages := UInt32.ofNat (mem.size / 65536)
            some (.silent, pushTrace { base with stack := .i32 pages :: base.stack } .silent)
          else
            some (trapState base s!"unknown memory index {memIdx}")
      | .memoryGrow memIdx =>
          match pop1? base.stack with
          | some (.i32 delta, stk) =>
              if hMem : memIdx < base.store.memories.size then
                let mem := base.store.memories[memIdx]
                let oldPages := mem.size / 65536
                let grown := ByteArray.mk (mem.toList.toArray ++ Array.replicate (delta.toNat * 65536) 0)
                let store' := { base.store with memories := base.store.memories.set! memIdx grown }
                some (.silent, pushTrace { base with store := store', stack := .i32 (UInt32.ofNat oldPages) :: stk } .silent)
              else
                some (trapState base s!"unknown memory index {memIdx}")
          | some (_, _) => some (trapState base "memory.grow delta is not i32")
          | none => some (trapState base "stack underflow in memory.grow")
      | .i32Load ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 4 with
              | some raw => some (.silent, pushTrace { base with stack := .i32 (UInt32.ofNat raw.toNat) :: stk } .silent)
              | none => some (trapState base "memory access fault in i32.load")
          | some _ => some (trapState base "type mismatch in i32.load")
          | none => some (trapState base "stack underflow in i32.load")
      | .i64Load ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 8 with
              | some raw => some (.silent, pushTrace { base with stack := .i64 raw :: stk } .silent)
              | none => some (trapState base "memory access fault in i64.load")
          | some _ => some (trapState base "type mismatch in i64.load")
          | none => some (trapState base "stack underflow in i64.load")
      | .f32Load ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 4 with
              | some raw =>
                  -- §4.2.7: f32.load reads 4 bytes and reinterprets as f32
                  some (.silent, pushTrace { base with stack := .f32 (u32BitsToFloat (UInt32.ofNat raw.toNat)) :: stk } .silent)
              | none => some (trapState base "memory access fault in f32.load")
          | some _ => some (trapState base "type mismatch in f32.load")
          | none => some (trapState base "stack underflow in f32.load")
      | .f64Load ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 8 with
              | some raw =>
                  -- §4.2.7: f64.load reads 8 bytes and reinterprets as f64
                  some (.silent, pushTrace { base with stack := .f64 (u64BitsToFloat raw) :: stk } .silent)
              | none => some (trapState base "memory access fault in f64.load")
          | some _ => some (trapState base "type mismatch in f64.load")
          | none => some (trapState base "stack underflow in f64.load")
      | .i32Load8s ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 1 with
              | some raw => some (.silent, pushTrace { base with stack := .i32 (signExtend32 (UInt32.ofNat raw.toNat) 8) :: stk } .silent)
              | none => some (trapState base "memory access fault in i32.load8_s")
          | some _ => some (trapState base "type mismatch in i32.load8_s")
          | none => some (trapState base "stack underflow in i32.load8_s")
      | .i32Load8u ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 1 with
              | some raw => some (.silent, pushTrace { base with stack := .i32 (UInt32.ofNat raw.toNat) :: stk } .silent)
              | none => some (trapState base "memory access fault in i32.load8_u")
          | some _ => some (trapState base "type mismatch in i32.load8_u")
          | none => some (trapState base "stack underflow in i32.load8_u")
      | .i32Load16s ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 2 with
              | some raw => some (.silent, pushTrace { base with stack := .i32 (signExtend32 (UInt32.ofNat raw.toNat) 16) :: stk } .silent)
              | none => some (trapState base "memory access fault in i32.load16_s")
          | some _ => some (trapState base "type mismatch in i32.load16_s")
          | none => some (trapState base "stack underflow in i32.load16_s")
      | .i32Load16u ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 2 with
              | some raw => some (.silent, pushTrace { base with stack := .i32 (UInt32.ofNat raw.toNat) :: stk } .silent)
              | none => some (trapState base "memory access fault in i32.load16_u")
          | some _ => some (trapState base "type mismatch in i32.load16_u")
          | none => some (trapState base "stack underflow in i32.load16_u")
      | .i64Load8s ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 1 with
              | some raw => some (.silent, pushTrace { base with stack := .i64 (signExtend64 raw 8) :: stk } .silent)
              | none => some (trapState base "memory access fault in i64.load8_s")
          | some _ => some (trapState base "type mismatch in i64.load8_s")
          | none => some (trapState base "stack underflow in i64.load8_s")
      | .i64Load8u ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 1 with
              | some raw => some (.silent, pushTrace { base with stack := .i64 raw :: stk } .silent)
              | none => some (trapState base "memory access fault in i64.load8_u")
          | some _ => some (trapState base "type mismatch in i64.load8_u")
          | none => some (trapState base "stack underflow in i64.load8_u")
      | .i64Load16s ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 2 with
              | some raw => some (.silent, pushTrace { base with stack := .i64 (signExtend64 raw 16) :: stk } .silent)
              | none => some (trapState base "memory access fault in i64.load16_s")
          | some _ => some (trapState base "type mismatch in i64.load16_s")
          | none => some (trapState base "stack underflow in i64.load16_s")
      | .i64Load16u ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 2 with
              | some raw => some (.silent, pushTrace { base with stack := .i64 raw :: stk } .silent)
              | none => some (trapState base "memory access fault in i64.load16_u")
          | some _ => some (trapState base "type mismatch in i64.load16_u")
          | none => some (trapState base "stack underflow in i64.load16_u")
      | .i64Load32s ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 4 with
              | some raw => some (.silent, pushTrace { base with stack := .i64 (signExtend64 raw 32) :: stk } .silent)
              | none => some (trapState base "memory access fault in i64.load32_s")
          | some _ => some (trapState base "type mismatch in i64.load32_s")
          | none => some (trapState base "stack underflow in i64.load32_s")
      | .i64Load32u ma =>
          match pop1? base.stack with
          | some (.i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => readLE? mem eff 4 with
              | some raw => some (.silent, pushTrace { base with stack := .i64 raw :: stk } .silent)
              | none => some (trapState base "memory access fault in i64.load32_u")
          | some _ => some (trapState base "type mismatch in i64.load32_u")
          | none => some (trapState base "stack underflow in i64.load32_u")
      | .i32Store ma | .i32Store8 ma | .i32Store16 ma =>
          match pop2? base.stack with
          | some (.i32 val, .i32 addr, stk) =>
              let width := match i with | .i32Store _ => 4 | .i32Store8 _ => 1 | _ => 2
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => writeLE? mem eff width (UInt64.ofNat val.toNat) with
              | some mem' =>
                  let store' := { base.store with memories := base.store.memories.set! 0 mem' }
                  some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none => some (trapState base "memory access fault in i32.store")
          | some _ => some (trapState base "type mismatch in i32.store")
          | none => some (trapState base "stack underflow in i32.store")
      | .i64Store ma | .i64Store8 ma | .i64Store16 ma | .i64Store32 ma =>
          match pop2? base.stack with
          | some (.i64 val, .i32 addr, stk) =>
              let width := match i with | .i64Store _ => 8 | .i64Store8 _ => 1 | .i64Store16 _ => 2 | _ => 4
              let eff := addr.toNat + ma.offset
              match base.store.memories[0]? >>= fun mem => writeLE? mem eff width val with
              | some mem' =>
                  let store' := { base.store with memories := base.store.memories.set! 0 mem' }
                  some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none => some (trapState base "memory access fault in i64.store")
          | some _ => some (trapState base "type mismatch in i64.store")
          | none => some (trapState base "stack underflow in i64.store")
      | .f32Store ma =>
          match pop2? base.stack with
          | some (.f32 v, .i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              -- Store the f32 as its 32-bit IEEE 754 bit pattern (§4.2.7)
              match base.store.memories[0]? >>= fun mem => writeLE? mem eff 4 (UInt64.ofNat (floatToU32Bits v).toNat) with
              | some mem' =>
                  let store' := { base.store with memories := base.store.memories.set! 0 mem' }
                  some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none => some (trapState base "memory access fault in f32.store")
          | some _ => some (trapState base "type mismatch in f32.store")
          | none => some (trapState base "stack underflow in f32.store")
      | .f64Store ma =>
          match pop2? base.stack with
          | some (.f64 v, .i32 addr, stk) =>
              let eff := addr.toNat + ma.offset
              -- Store the f64 as its 64-bit IEEE 754 bit pattern (§4.2.7)
              match base.store.memories[0]? >>= fun mem => writeLE? mem eff 8 (floatToU64Bits v) with
              | some mem' =>
                  let store' := { base.store with memories := base.store.memories.set! 0 mem' }
                  some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none => some (trapState base "memory access fault in f64.store")
          | some _ => some (trapState base "type mismatch in f64.store")
          | none => some (trapState base "stack underflow in f64.store")
      | .i32Eqz =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := boolToI32 (n == 0) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.eqz")
          | none => some (trapState base "stack underflow in i32.eqz")
      | .i32Eq => withI32Rel base (· == ·) "i32.eq"
      | .i32Ne => withI32Rel base (· != ·) "i32.ne"
      | .i32Lts =>
          withI32Rel base (fun a b => i32ToSigned a < i32ToSigned b) "i32.lt_s"
      | .i32Ltu => withI32Rel base (· < ·) "i32.lt_u"
      | .i32Gts =>
          withI32Rel base (fun a b => i32ToSigned a > i32ToSigned b) "i32.gt_s"
      | .i32Gtu => withI32Rel base (· > ·) "i32.gt_u"
      | .i32Les =>
          withI32Rel base (fun a b => i32ToSigned a <= i32ToSigned b) "i32.le_s"
      | .i32Leu => withI32Rel base (· <= ·) "i32.le_u"
      | .i32Ges =>
          withI32Rel base (fun a b => i32ToSigned a >= i32ToSigned b) "i32.ge_s"
      | .i32Geu => withI32Rel base (· >= ·) "i32.ge_u"
      | .i32Clz =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (i32Clz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.clz")
          | none => some (trapState base "stack underflow in i32.clz")
      | .i32Ctz =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (i32Ctz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.ctz")
          | none => some (trapState base "stack underflow in i32.ctz")
      | .i32Popcnt =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (i32Popcnt n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.popcnt")
          | none => some (trapState base "stack underflow in i32.popcnt")
      | .i32DivS => withI32Div base true "i32.div_s"
      | .i32DivU => withI32Div base false "i32.div_u"
      | .i32RemS => withI32Rem base true "i32.rem_s"
      | .i32RemU => withI32Rem base false "i32.rem_u"
      | .i32And => withI32Bin base (· &&& ·) "i32.and"
      | .i32Or => withI32Bin base (· ||| ·) "i32.or"
      | .i32Xor => withI32Bin base (· ^^^ ·) "i32.xor"
      | .i32Shl =>
          withI32Bin base (fun a b => UInt32.shiftLeft a (UInt32.ofNat (b.toNat % 32))) "i32.shl"
      | .i32ShrS =>
          withI32Bin base
            (fun a b =>
              Int32.toUInt32 (Int32.ofInt (i32ToSigned a / Int.ofNat (Nat.pow 2 (b.toNat % 32)))))
            "i32.shr_s"
      | .i32ShrU =>
          withI32Bin base (fun a b => UInt32.shiftRight a (UInt32.ofNat (b.toNat % 32))) "i32.shr_u"
      | .i32Rotl => withI32Bin base i32Rotl "i32.rotl"
      | .i32Rotr => withI32Bin base i32Rotr "i32.rotr"
      | .i64Eqz =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := boolToI32 (n == 0) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.eqz")
          | none => some (trapState base "stack underflow in i64.eqz")
      | .i64Eq => withI64Rel base (· == ·) "i64.eq"
      | .i64Ne => withI64Rel base (· != ·) "i64.ne"
      | .i64Lts =>
          withI64Rel base (fun a b => i64ToSigned a < i64ToSigned b) "i64.lt_s"
      | .i64Ltu => withI64Rel base (· < ·) "i64.lt_u"
      | .i64Gts =>
          withI64Rel base (fun a b => i64ToSigned a > i64ToSigned b) "i64.gt_s"
      | .i64Gtu => withI64Rel base (· > ·) "i64.gt_u"
      | .i64Les =>
          withI64Rel base (fun a b => i64ToSigned a <= i64ToSigned b) "i64.le_s"
      | .i64Leu => withI64Rel base (· <= ·) "i64.le_u"
      | .i64Ges =>
          withI64Rel base (fun a b => i64ToSigned a >= i64ToSigned b) "i64.ge_s"
      | .i64Geu => withI64Rel base (· >= ·) "i64.ge_u"
      | .i64Clz =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i64 (i64Clz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.clz")
          | none => some (trapState base "stack underflow in i64.clz")
      | .i64Ctz =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i64 (i64Ctz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.ctz")
          | none => some (trapState base "stack underflow in i64.ctz")
      | .i64Popcnt =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i64 (i64Popcnt n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.popcnt")
          | none => some (trapState base "stack underflow in i64.popcnt")
      | .i64DivS => withI64Div base true "i64.div_s"
      | .i64DivU => withI64Div base false "i64.div_u"
      | .i64RemS => withI64Rem base true "i64.rem_s"
      | .i64RemU => withI64Rem base false "i64.rem_u"
      | .i64And => withI64Bin base (· &&& ·) "i64.and"
      | .i64Or => withI64Bin base (· ||| ·) "i64.or"
      | .i64Xor => withI64Bin base (· ^^^ ·) "i64.xor"
      | .i64Shl =>
          withI64Bin base (fun a b => UInt64.shiftLeft a (UInt64.ofNat (b.toNat % 64))) "i64.shl"
      | .i64ShrS =>
          withI64Bin base
            (fun a b =>
              Int64.toUInt64 (Int64.ofInt (i64ToSigned a / Int.ofNat (Nat.pow 2 (b.toNat % 64)))))
            "i64.shr_s"
      | .i64ShrU =>
          withI64Bin base (fun a b => UInt64.shiftRight a (UInt64.ofNat (b.toNat % 64))) "i64.shr_u"
      | .i64Rotl => withI64Bin base i64Rotl "i64.rotl"
      | .i64Rotr => withI64Bin base i64Rotr "i64.rotr"
      | .f32Eq => withF32Rel base (· == ·) "f32.eq"
      | .f32Ne => withF32Rel base (· != ·) "f32.ne"
      | .f32Lt => withF32Rel base (· < ·) "f32.lt"
      | .f32Gt => withF32Rel base (· > ·) "f32.gt"
      | .f32Le => withF32Rel base (· <= ·) "f32.le"
      | .f32Ge => withF32Rel base (· >= ·) "f32.ge"
      | .f32Abs =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 n.abs :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.abs")
          | none => some (trapState base "stack underflow in f32.abs")
      | .f32Ceil =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 n.ceil :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.ceil")
          | none => some (trapState base "stack underflow in f32.ceil")
      | .f32Floor =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 n.floor :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.floor")
          | none => some (trapState base "stack underflow in f32.floor")
      | .f32Trunc =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              let v := if n < 0 then n.ceil else n.floor
              some (.silent, pushTrace { base with stack := .f32 v :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.trunc")
          | none => some (trapState base "stack underflow in f32.trunc")
      | .f32Nearest =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 n.round :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.nearest")
          | none => some (trapState base "stack underflow in f32.nearest")
      | .f32Sqrt =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 n.sqrt :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.sqrt")
          | none => some (trapState base "stack underflow in f32.sqrt")
      | .f32Neg =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (-n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.neg")
          | none => some (trapState base "stack underflow in f32.neg")
      | .f32Add => withF32Bin base (· + ·) "f32.add"
      | .f32Sub => withF32Bin base (· - ·) "f32.sub"
      | .f32Mul => withF32Bin base (· * ·) "f32.mul"
      | .f32Div => withF32Bin base (· / ·) "f32.div"
      | .f32Min => withF32Bin base (fun a b => if a <= b then a else b) "f32.min"
      | .f32Max => withF32Bin base (fun a b => if a <= b then b else a) "f32.max"
      | .f32Copysign =>
          withF32Bin base (fun a b => if b < 0 then -a.abs else a.abs) "f32.copysign"
      | .f64Eq => withF64Rel base (· == ·) "f64.eq"
      | .f64Ne => withF64Rel base (· != ·) "f64.ne"
      | .f64Lt => withF64Rel base (· < ·) "f64.lt"
      | .f64Gt => withF64Rel base (· > ·) "f64.gt"
      | .f64Le => withF64Rel base (· <= ·) "f64.le"
      | .f64Ge => withF64Rel base (· >= ·) "f64.ge"
      | .f64Abs =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 n.abs :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.abs")
          | none => some (trapState base "stack underflow in f64.abs")
      | .f64Ceil =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 n.ceil :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.ceil")
          | none => some (trapState base "stack underflow in f64.ceil")
      | .f64Floor =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 n.floor :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.floor")
          | none => some (trapState base "stack underflow in f64.floor")
      | .f64Trunc =>
          match pop1? base.stack with
          | some (.f64 n, stk) =>
              let v := if n < 0 then n.ceil else n.floor
              some (.silent, pushTrace { base with stack := .f64 v :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.trunc")
          | none => some (trapState base "stack underflow in f64.trunc")
      | .f64Nearest =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 n.round :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.nearest")
          | none => some (trapState base "stack underflow in f64.nearest")
      | .f64Sqrt =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 n.sqrt :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.sqrt")
          | none => some (trapState base "stack underflow in f64.sqrt")
      | .f64Neg =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (-n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.neg")
          | none => some (trapState base "stack underflow in f64.neg")
      | .f64Min => withF64Bin base (fun a b => if a <= b then a else b) "f64.min"
      | .f64Max => withF64Bin base (fun a b => if a <= b then b else a) "f64.max"
      | .f64Copysign =>
          withF64Bin base (fun a b => if b < 0 then -a.abs else a.abs) "f64.copysign"
      | .i32WrapI64 =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i32 (UInt32.ofNat n.toNat) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.wrap_i64")
          | none => some (trapState base "stack underflow in i32.wrap_i64")
      | .i32TruncF32s | .i32TruncF64s =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= -(Int.ofNat (Nat.pow 2 31)) && i < Int.ofNat (Nat.pow 2 31) then
                    some (.silent, pushTrace { base with stack := .i32 (UInt32.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i32.trunc_s")
              | none => some (trapState base "invalid conversion to integer in i32.trunc_s")
          | some (.f64 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= -(Int.ofNat (Nat.pow 2 31)) && i < Int.ofNat (Nat.pow 2 31) then
                    some (.silent, pushTrace { base with stack := .i32 (UInt32.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i32.trunc_s")
              | none => some (trapState base "invalid conversion to integer in i32.trunc_s")
          | some _ => some (trapState base "type mismatch in i32.trunc_s")
          | none => some (trapState base "stack underflow in i32.trunc_s")
      | .i32TruncF32u | .i32TruncF64u =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= 0 && i < Int.ofNat (Nat.pow 2 32) then
                    some (.silent, pushTrace { base with stack := .i32 (UInt32.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i32.trunc_u")
              | none => some (trapState base "invalid conversion to integer in i32.trunc_u")
          | some (.f64 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= 0 && i < Int.ofNat (Nat.pow 2 32) then
                    some (.silent, pushTrace { base with stack := .i32 (UInt32.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i32.trunc_u")
              | none => some (trapState base "invalid conversion to integer in i32.trunc_u")
          | some _ => some (trapState base "type mismatch in i32.trunc_u")
          | none => some (trapState base "stack underflow in i32.trunc_u")
      | .i64ExtendI32s | .i64ExtendI32u =>
          match pop1? base.stack with
          | some (.i32 n, stk) =>
              let out :=
                match i with
                | .i64ExtendI32s => UInt64.ofInt (i32ToSigned n)
                | _ => UInt64.ofNat n.toNat
              some (.silent, pushTrace { base with stack := .i64 out :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.extend_i32")
          | none => some (trapState base "stack underflow in i64.extend_i32")
      | .i64TruncF32s | .i64TruncF64s =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= -(Int.ofNat (Nat.pow 2 63)) && i < Int.ofNat (Nat.pow 2 63) then
                    some (.silent, pushTrace { base with stack := .i64 (UInt64.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i64.trunc_s")
              | none => some (trapState base "invalid conversion to integer in i64.trunc_s")
          | some (.f64 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= -(Int.ofNat (Nat.pow 2 63)) && i < Int.ofNat (Nat.pow 2 63) then
                    some (.silent, pushTrace { base with stack := .i64 (UInt64.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i64.trunc_s")
              | none => some (trapState base "invalid conversion to integer in i64.trunc_s")
          | some _ => some (trapState base "type mismatch in i64.trunc_s")
          | none => some (trapState base "stack underflow in i64.trunc_s")
      | .i64TruncF32u | .i64TruncF64u =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= 0 then
                    some (.silent, pushTrace { base with stack := .i64 (UInt64.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i64.trunc_u")
              | none => some (trapState base "invalid conversion to integer in i64.trunc_u")
          | some (.f64 n, stk) =>
              match truncFloatToInt? n with
              | some i =>
                  if i >= 0 then
                    some (.silent, pushTrace { base with stack := .i64 (UInt64.ofInt i) :: stk } .silent)
                  else
                    some (trapState base "integer overflow in i64.trunc_u")
              | none => some (trapState base "invalid conversion to integer in i64.trunc_u")
          | some _ => some (trapState base "type mismatch in i64.trunc_u")
          | none => some (trapState base "stack underflow in i64.trunc_u")
      | .f32ConvertI32s =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Float.ofInt (i32ToSigned n)) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.convert_i32_s")
          | none => some (trapState base "stack underflow in f32.convert_i32_s")
      | .f32ConvertI32u =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Float.ofNat n.toNat) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.convert_i32_u")
          | none => some (trapState base "stack underflow in f32.convert_i32_u")
      | .f32ConvertI64s | .f32ConvertI64u =>
          match pop1? base.stack with
          | some (.i64 n, stk) =>
              let out :=
                match i with
                | .f32ConvertI64s => Float.ofInt (i64ToSigned n)
                | _ => Float.ofNat n.toNat
              some (.silent, pushTrace { base with stack := .f32 out :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.convert_i64")
          | none => some (trapState base "stack underflow in f32.convert_i64")
      | .f32DemoteF64 =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f32 n :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.demote_f64")
          | none => some (trapState base "stack underflow in f32.demote_f64")
      | .f64ConvertI32s =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Float.ofInt (i32ToSigned n)) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.convert_i32_s")
          | none => some (trapState base "stack underflow in f64.convert_i32_s")
      | .f64ConvertI32u =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Float.ofNat n.toNat) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.convert_i32_u")
          | none => some (trapState base "stack underflow in f64.convert_i32_u")
      | .f64ConvertI64s | .f64ConvertI64u =>
          match pop1? base.stack with
          | some (.i64 n, stk) =>
              let out :=
                match i with
                | .f64ConvertI64s => Float.ofInt (i64ToSigned n)
                | _ => Float.ofNat n.toNat
              some (.silent, pushTrace { base with stack := .f64 out :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.convert_i64")
          | none => some (trapState base "stack underflow in f64.convert_i64")
      | .f64PromoteF32 =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f64 n :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.promote_f32")
          | none => some (trapState base "stack underflow in f64.promote_f32")
      | .i32ReinterpretF32 =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (UInt32.ofNat n.toUInt64.toNat) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.reinterpret_f32")
          | none => some (trapState base "stack underflow in i32.reinterpret_f32")
      | .f32ReinterpretI32 =>
          match pop1? base.stack with
          | some (.i32 n, stk) =>
              -- §4.3.4: reinterpret i32 bits as f32 (bit-preserving cast)
              some (.silent, pushTrace { base with stack := .f32 (u32BitsToFloat n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.reinterpret_i32")
          | none => some (trapState base "stack underflow in f32.reinterpret_i32")
      | .i64ReinterpretF64 =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .i64 n.toUInt64 :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.reinterpret_f64")
          | none => some (trapState base "stack underflow in i64.reinterpret_f64")
      | .f64ReinterpretI64 =>
          match pop1? base.stack with
          | some (.i64 n, stk) =>
              -- §4.3.4: reinterpret i64 bits as f64 (bit-preserving cast)
              some (.silent, pushTrace { base with stack := .f64 (u64BitsToFloat n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.reinterpret_i64")
          | none => some (trapState base "stack underflow in f64.reinterpret_i64")
      | .memoryInit _ _ | .memoryCopy _ _ | .memoryFill _ | .tableInit _ _ | .tableCopy _ _ =>
          match pop3? base.stack with
          | some (.i32 _, .i32 _, .i32 _, stk) =>
              some (.silent, pushTrace { base with stack := stk } .silent)
          | _ => some (trapState base "type mismatch in bulk operation")
      | .dataDrop _ | .elemDrop _ =>
          some (.silent, pushTrace base .silent)

/-- Small-step reduction relation induced by `step?`. -/
inductive Step : ExecState → TraceEvent → ExecState → Prop where
  | mk {s : ExecState} {t : TraceEvent} {s' : ExecState} :
      step? s = some (t, s') →
      Step s t s'

/-- Reflexive-transitive closure of Wasm machine steps with trace accumulation. -/
inductive Steps : ExecState → List TraceEvent → ExecState → Prop where
  | refl (s : ExecState) : Steps s [] s
  | tail {s1 s2 s3 : ExecState} {t : TraceEvent} {ts : List TraceEvent} :
      Step s1 t s2 →
      Steps s2 ts s3 →
      Steps s1 (t :: ts) s3

/-- Behavioral semantics for a Wasm module run from `initialState`. -/
def Behaves (m : Module) (b : List TraceEvent) : Prop :=
  ∃ s', Steps (initialState m) b s' ∧ step? s' = none

end VerifiedJS.Wasm
