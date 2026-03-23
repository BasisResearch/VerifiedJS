/-
  VerifiedJS — Wasm Execution Semantics
  Small-step reduction: store, stack, frames.
  SPEC: WebAssembly 1.0 §4.2, §4.4 (execution) and WasmCert-Coq `theories/operations.v`.
-/

import VerifiedJS.Wasm.Syntax
import VerifiedJS.Wasm.Numerics
import VerifiedJS.Wasm.IR
import VerifiedJS.Core.Semantics
import VerifiedJS.ANF.Semantics
import VerifiedJS.Wasm.Lower
import VerifiedJS.Wasm.Emit

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

/-- Wasm store (functions, tables, memories, globals).
    REF: WasmCert-Coq `store_record`, Wasm §4.5 -/
structure Store where
  types : Array FuncType   -- module type section, needed for call_indirect type check
  funcs : Array Func
  tables : Array (Array (Option Nat))
  tableLimits : Array Limits  -- declared table limits for table.grow bounds checking
  memories : Array ByteArray
  memLimits : Array Limits  -- declared memory limits for grow bounds checking
  globals : Array WasmValue
  datas : Array ByteArray   -- data segment payloads for memory.init
  elems : Array (Array (Option Nat))  -- element segment function indices for table.init
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
    types := m.types
    funcs := m.funcs
    tables := m.tables.map initTableSlots
    tableLimits := m.tables.map (·.lim)
    memories := m.memories.map initMemory
    memLimits := m.memories.map (·.lim)
    globals := initGlobals m
    datas := m.datas.map (·.init)
    elems := m.elems.map (fun seg => seg.funcIdxs.toArray.map some)
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

/-- Pop exactly `n` values from the stack, returning them in order (first popped = first in list).
    Returns `none` if the stack has fewer than `n` elements. -/
private def popN? (stack : List WasmValue) (n : Nat) : Option (List WasmValue × List WasmValue) :=
  if n == 0 then some ([], stack)
  else if stack.length < n then none
  else some (stack.take n, stack.drop n)

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
          -- SPEC §4.4.8.5: call invocation pops arguments from the stack.
          -- REF: WasmCert-Coq `r_invoke_native`
          if h : idx < base.store.funcs.size then
            let func := base.store.funcs[idx]
            -- Resolve function type to determine parameter count
            let nParams :=
              if hT : func.typeIdx < base.store.types.size then
                base.store.types[func.typeIdx].params.length
              else 0
            match popN? base.stack nParams with
            | some (args, remainingStack) =>
                let argLocals := args.reverse.toArray  -- reverse: first param is deepest on stack
                let extraLocals := (func.locals.map defaultValue).toArray
                let frame : Frame := { locals := argLocals ++ extraLocals, moduleInst := 0 }
                let s' := pushTrace { base with stack := remainingStack, frames := frame :: base.frames, code := func.body ++ rest } .silent
                some (.silent, s')
            | none => some (trapState base s!"stack underflow in call {idx}")
          else
            some (trapState base s!"unknown function index {idx}")
      | .callIndirect expectedTypeIdx tableIdx =>
          -- SPEC §4.4.8.7 call_indirect: type-checked indirect call.
          -- REF: WasmCert-Coq r_call_indirect_success/failure
          match pop1? base.stack with
          | some (.i32 elemIdx, stk) =>
              if hTbl : tableIdx < base.store.tables.size then
                let table := base.store.tables[tableIdx]
                if hElem : elemIdx.toNat < table.size then
                  match table[elemIdx.toNat] with
                  | some funcIdx =>
                      if hFunc : funcIdx < base.store.funcs.size then
                        let func := base.store.funcs[funcIdx]
                        -- Type check: the function's type must match the expected type index.
                        let typeOk :=
                          if hType : expectedTypeIdx < base.store.types.size then
                            let expectedType := base.store.types[expectedTypeIdx]
                            if hFuncType : func.typeIdx < base.store.types.size then
                              let actualType := base.store.types[func.typeIdx]
                              actualType == expectedType
                            else false
                          else true  -- If type section unavailable, skip check (permissive)
                        if typeOk then
                          let nParams :=
                            if hT : expectedTypeIdx < base.store.types.size then
                              base.store.types[expectedTypeIdx].params.length
                            else 0
                          match popN? stk nParams with
                          | some (args, remainingStack) =>
                              let argLocals := args.reverse.toArray
                              let extraLocals := (func.locals.map defaultValue).toArray
                              let frame : Frame := { locals := argLocals ++ extraLocals, moduleInst := 0 }
                              let s' := pushTrace
                                { base with stack := remainingStack, frames := frame :: base.frames, code := func.body ++ rest } .silent
                              some (.silent, s')
                          | none => some (trapState base "stack underflow in call_indirect")
                        else
                          some (trapState base "indirect call type mismatch")
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
          -- SPEC §4.4.7.2 memory.grow: attempt to grow memory by delta pages.
          -- Returns old size on success, -1 (0xFFFFFFFF) on failure.
          -- REF: WasmCert-Coq r_memory_grow_success/failure
          match pop1? base.stack with
          | some (.i32 delta, stk) =>
              if hMem : memIdx < base.store.memories.size then
                let mem := base.store.memories[memIdx]
                let oldPages := mem.size / 65536
                let newPages := oldPages + delta.toNat
                -- Check against declared maximum (Wasm spec §5.5.5)
                let maxOk : Bool :=
                  if hLim : memIdx < base.store.memLimits.size then
                    match base.store.memLimits[memIdx].max with
                    | some maxPages => newPages.ble maxPages
                    | none => newPages.ble 65536
                  else newPages.ble 65536
                if maxOk then
                  let grown := ByteArray.mk (mem.toList.toArray ++ Array.replicate (delta.toNat * 65536) 0)
                  let store' := { base.store with memories := base.store.memories.set! memIdx grown }
                  some (.silent, pushTrace { base with store := store', stack := .i32 (UInt32.ofNat oldPages) :: stk } .silent)
                else
                  -- Failure: return -1 (as i32, i.e. 0xFFFFFFFF), store unchanged
                  some (.silent, pushTrace { base with stack := .i32 (UInt32.ofNat 0xFFFFFFFF) :: stk } .silent)
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
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := boolToI32 (Numerics.i32Eqz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.eqz")
          | none => some (trapState base "stack underflow in i32.eqz")
      | .i32Eq => withI32Rel base Numerics.i32Eq "i32.eq"
      | .i32Ne => withI32Rel base Numerics.i32Ne "i32.ne"
      | .i32Lts => withI32Rel base Numerics.i32Lts "i32.lt_s"
      | .i32Ltu => withI32Rel base Numerics.i32Ltu "i32.lt_u"
      | .i32Gts => withI32Rel base Numerics.i32Gts "i32.gt_s"
      | .i32Gtu => withI32Rel base Numerics.i32Gtu "i32.gt_u"
      | .i32Les => withI32Rel base Numerics.i32Les "i32.le_s"
      | .i32Leu => withI32Rel base Numerics.i32Leu "i32.le_u"
      | .i32Ges => withI32Rel base Numerics.i32Ges "i32.ge_s"
      | .i32Geu => withI32Rel base Numerics.i32Geu "i32.ge_u"
      | .i32Clz =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (Numerics.i32Clz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.clz")
          | none => some (trapState base "stack underflow in i32.clz")
      | .i32Ctz =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (Numerics.i32Ctz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.ctz")
          | none => some (trapState base "stack underflow in i32.ctz")
      | .i32Popcnt =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (Numerics.i32Popcnt n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.popcnt")
          | none => some (trapState base "stack underflow in i32.popcnt")
      | .i32DivS => withI32Div base true "i32.div_s"
      | .i32DivU => withI32Div base false "i32.div_u"
      | .i32RemS => withI32Rem base true "i32.rem_s"
      | .i32RemU => withI32Rem base false "i32.rem_u"
      | .i32And => withI32Bin base Numerics.i32And "i32.and"
      | .i32Or => withI32Bin base Numerics.i32Or "i32.or"
      | .i32Xor => withI32Bin base Numerics.i32Xor "i32.xor"
      | .i32Shl => withI32Bin base Numerics.i32Shl "i32.shl"
      | .i32ShrS => withI32Bin base Numerics.i32ShrS "i32.shr_s"
      | .i32ShrU => withI32Bin base Numerics.i32ShrU "i32.shr_u"
      | .i32Rotl => withI32Bin base Numerics.i32Rotl "i32.rotl"
      | .i32Rotr => withI32Bin base Numerics.i32Rotr "i32.rotr"
      | .i64Eqz =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := boolToI32 (Numerics.i64Eqz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.eqz")
          | none => some (trapState base "stack underflow in i64.eqz")
      | .i64Eq => withI64Rel base Numerics.i64Eq "i64.eq"
      | .i64Ne => withI64Rel base Numerics.i64Ne "i64.ne"
      | .i64Lts => withI64Rel base Numerics.i64Lts "i64.lt_s"
      | .i64Ltu => withI64Rel base Numerics.i64Ltu "i64.lt_u"
      | .i64Gts => withI64Rel base Numerics.i64Gts "i64.gt_s"
      | .i64Gtu => withI64Rel base Numerics.i64Gtu "i64.gt_u"
      | .i64Les => withI64Rel base Numerics.i64Les "i64.le_s"
      | .i64Leu => withI64Rel base Numerics.i64Leu "i64.le_u"
      | .i64Ges => withI64Rel base Numerics.i64Ges "i64.ge_s"
      | .i64Geu => withI64Rel base Numerics.i64Geu "i64.ge_u"
      | .i64Clz =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i64 (Numerics.i64Clz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.clz")
          | none => some (trapState base "stack underflow in i64.clz")
      | .i64Ctz =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i64 (Numerics.i64Ctz n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.ctz")
          | none => some (trapState base "stack underflow in i64.ctz")
      | .i64Popcnt =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i64 (Numerics.i64Popcnt n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.popcnt")
          | none => some (trapState base "stack underflow in i64.popcnt")
      | .i64DivS => withI64Div base true "i64.div_s"
      | .i64DivU => withI64Div base false "i64.div_u"
      | .i64RemS => withI64Rem base true "i64.rem_s"
      | .i64RemU => withI64Rem base false "i64.rem_u"
      | .i64And => withI64Bin base Numerics.i64And "i64.and"
      | .i64Or => withI64Bin base Numerics.i64Or "i64.or"
      | .i64Xor => withI64Bin base Numerics.i64Xor "i64.xor"
      | .i64Shl => withI64Bin base Numerics.i64Shl "i64.shl"
      | .i64ShrS => withI64Bin base Numerics.i64ShrS "i64.shr_s"
      | .i64ShrU => withI64Bin base Numerics.i64ShrU "i64.shr_u"
      | .i64Rotl => withI64Bin base Numerics.i64Rotl "i64.rotl"
      | .i64Rotr => withI64Bin base Numerics.i64Rotr "i64.rotr"
      | .f32Eq => withF32Rel base Numerics.f32Eq "f32.eq"
      | .f32Ne => withF32Rel base Numerics.f32Ne "f32.ne"
      | .f32Lt => withF32Rel base Numerics.f32Lt "f32.lt"
      | .f32Gt => withF32Rel base Numerics.f32Gt "f32.gt"
      | .f32Le => withF32Rel base Numerics.f32Le "f32.le"
      | .f32Ge => withF32Rel base Numerics.f32Ge "f32.ge"
      | .f32Abs =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32Abs n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.abs")
          | none => some (trapState base "stack underflow in f32.abs")
      | .f32Ceil =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32Ceil n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.ceil")
          | none => some (trapState base "stack underflow in f32.ceil")
      | .f32Floor =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32Floor n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.floor")
          | none => some (trapState base "stack underflow in f32.floor")
      | .f32Trunc =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              some (.silent, pushTrace { base with stack := .f32 (Numerics.f32Trunc n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.trunc")
          | none => some (trapState base "stack underflow in f32.trunc")
      | .f32Nearest =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32Nearest n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.nearest")
          | none => some (trapState base "stack underflow in f32.nearest")
      | .f32Sqrt =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32Sqrt n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.sqrt")
          | none => some (trapState base "stack underflow in f32.sqrt")
      | .f32Neg =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32Neg n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.neg")
          | none => some (trapState base "stack underflow in f32.neg")
      | .f32Add => withF32Bin base Numerics.f32Add "f32.add"
      | .f32Sub => withF32Bin base Numerics.f32Sub "f32.sub"
      | .f32Mul => withF32Bin base Numerics.f32Mul "f32.mul"
      | .f32Div => withF32Bin base Numerics.f32Div "f32.div"
      | .f32Min => withF32Bin base Numerics.f32Min "f32.min"
      | .f32Max => withF32Bin base Numerics.f32Max "f32.max"
      | .f32Copysign => withF32Bin base Numerics.f32Copysign "f32.copysign"
      | .f64Eq => withF64Rel base Numerics.f64Eq "f64.eq"
      | .f64Ne => withF64Rel base Numerics.f64Ne "f64.ne"
      | .f64Lt => withF64Rel base Numerics.f64Lt "f64.lt"
      | .f64Gt => withF64Rel base Numerics.f64Gt "f64.gt"
      | .f64Le => withF64Rel base Numerics.f64Le "f64.le"
      | .f64Ge => withF64Rel base Numerics.f64Ge "f64.ge"
      | .f64Abs =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64Abs n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.abs")
          | none => some (trapState base "stack underflow in f64.abs")
      | .f64Ceil =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64Ceil n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.ceil")
          | none => some (trapState base "stack underflow in f64.ceil")
      | .f64Floor =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64Floor n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.floor")
          | none => some (trapState base "stack underflow in f64.floor")
      | .f64Trunc =>
          match pop1? base.stack with
          | some (.f64 n, stk) =>
              some (.silent, pushTrace { base with stack := .f64 (Numerics.f64Trunc n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.trunc")
          | none => some (trapState base "stack underflow in f64.trunc")
      | .f64Nearest =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64Nearest n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.nearest")
          | none => some (trapState base "stack underflow in f64.nearest")
      | .f64Sqrt =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64Sqrt n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.sqrt")
          | none => some (trapState base "stack underflow in f64.sqrt")
      | .f64Neg =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64Neg n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.neg")
          | none => some (trapState base "stack underflow in f64.neg")
      | .f64Min => withF64Bin base Numerics.f64Min "f64.min"
      | .f64Max => withF64Bin base Numerics.f64Max "f64.max"
      | .f64Copysign => withF64Bin base Numerics.f64Copysign "f64.copysign"
      | .i32WrapI64 =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .i32 (Numerics.i32WrapI64 n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.wrap_i64")
          | none => some (trapState base "stack underflow in i32.wrap_i64")
      | .i32TruncF32s | .i32TruncF64s =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match Numerics.i32TruncFS? n with
              | some v => some (.silent, pushTrace { base with stack := .i32 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i32.trunc_f*_s")
          | some (.f64 n, stk) =>
              match Numerics.i32TruncFS? n with
              | some v => some (.silent, pushTrace { base with stack := .i32 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i32.trunc_f*_s")
          | some _ => some (trapState base "type mismatch in i32.trunc_s")
          | none => some (trapState base "stack underflow in i32.trunc_s")
      | .i32TruncF32u | .i32TruncF64u =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match Numerics.i32TruncFU? n with
              | some v => some (.silent, pushTrace { base with stack := .i32 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i32.trunc_f*_u")
          | some (.f64 n, stk) =>
              match Numerics.i32TruncFU? n with
              | some v => some (.silent, pushTrace { base with stack := .i32 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i32.trunc_f*_u")
          | some _ => some (trapState base "type mismatch in i32.trunc_u")
          | none => some (trapState base "stack underflow in i32.trunc_u")
      | .i64ExtendI32s =>
          match pop1? base.stack with
          | some (.i32 n, stk) =>
              some (.silent, pushTrace { base with stack := .i64 (Numerics.i64ExtendI32s n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.extend_i32_s")
          | none => some (trapState base "stack underflow in i64.extend_i32_s")
      | .i64ExtendI32u =>
          match pop1? base.stack with
          | some (.i32 n, stk) =>
              some (.silent, pushTrace { base with stack := .i64 (Numerics.i64ExtendI32u n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.extend_i32_u")
          | none => some (trapState base "stack underflow in i64.extend_i32_u")
      | .i64TruncF32s | .i64TruncF64s =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match Numerics.i64TruncFS? n with
              | some v => some (.silent, pushTrace { base with stack := .i64 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i64.trunc_f*_s")
          | some (.f64 n, stk) =>
              match Numerics.i64TruncFS? n with
              | some v => some (.silent, pushTrace { base with stack := .i64 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i64.trunc_f*_s")
          | some _ => some (trapState base "type mismatch in i64.trunc_s")
          | none => some (trapState base "stack underflow in i64.trunc_s")
      | .i64TruncF32u | .i64TruncF64u =>
          match pop1? base.stack with
          | some (.f32 n, stk) =>
              match Numerics.i64TruncFU? n with
              | some v => some (.silent, pushTrace { base with stack := .i64 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i64.trunc_f*_u")
          | some (.f64 n, stk) =>
              match Numerics.i64TruncFU? n with
              | some v => some (.silent, pushTrace { base with stack := .i64 v :: stk } .silent)
              | none => some (trapState base "invalid conversion in i64.trunc_f*_u")
          | some _ => some (trapState base "type mismatch in i64.trunc_u")
          | none => some (trapState base "stack underflow in i64.trunc_u")
      | .f32ConvertI32s =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32ConvertI32s n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.convert_i32_s")
          | none => some (trapState base "stack underflow in f32.convert_i32_s")
      | .f32ConvertI32u =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32ConvertI32u n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.convert_i32_u")
          | none => some (trapState base "stack underflow in f32.convert_i32_u")
      | .f32ConvertI64s =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32ConvertI64s n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.convert_i64_s")
          | none => some (trapState base "stack underflow in f32.convert_i64_s")
      | .f32ConvertI64u =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32ConvertI64u n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.convert_i64_u")
          | none => some (trapState base "stack underflow in f32.convert_i64_u")
      | .f32DemoteF64 =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .f32 (Numerics.f32DemoteF64 n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.demote_f64")
          | none => some (trapState base "stack underflow in f32.demote_f64")
      | .f64ConvertI32s =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64ConvertI32s n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.convert_i32_s")
          | none => some (trapState base "stack underflow in f64.convert_i32_s")
      | .f64ConvertI32u =>
          match pop1? base.stack with
          | some (.i32 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64ConvertI32u n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.convert_i32_u")
          | none => some (trapState base "stack underflow in f64.convert_i32_u")
      | .f64ConvertI64s =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64ConvertI64s n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.convert_i64_s")
          | none => some (trapState base "stack underflow in f64.convert_i64_s")
      | .f64ConvertI64u =>
          match pop1? base.stack with
          | some (.i64 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64ConvertI64u n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.convert_i64_u")
          | none => some (trapState base "stack underflow in f64.convert_i64_u")
      | .f64PromoteF32 =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .f64 (Numerics.f64PromoteF32 n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.promote_f32")
          | none => some (trapState base "stack underflow in f64.promote_f32")
      | .i32ReinterpretF32 =>
          match pop1? base.stack with
          | some (.f32 n, stk) => some (.silent, pushTrace { base with stack := .i32 (Numerics.i32ReinterpretF32 n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i32.reinterpret_f32")
          | none => some (trapState base "stack underflow in i32.reinterpret_f32")
      | .f32ReinterpretI32 =>
          match pop1? base.stack with
          | some (.i32 n, stk) =>
              some (.silent, pushTrace { base with stack := .f32 (Numerics.f32ReinterpretI32 n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f32.reinterpret_i32")
          | none => some (trapState base "stack underflow in f32.reinterpret_i32")
      | .i64ReinterpretF64 =>
          match pop1? base.stack with
          | some (.f64 n, stk) => some (.silent, pushTrace { base with stack := .i64 (Numerics.i64ReinterpretF64 n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in i64.reinterpret_f64")
          | none => some (trapState base "stack underflow in i64.reinterpret_f64")
      | .f64ReinterpretI64 =>
          match pop1? base.stack with
          | some (.i64 n, stk) =>
              some (.silent, pushTrace { base with stack := .f64 (Numerics.f64ReinterpretI64 n) :: stk } .silent)
          | some _ => some (trapState base "type mismatch in f64.reinterpret_i64")
          | none => some (trapState base "stack underflow in f64.reinterpret_i64")
      -- SPEC §4.4.7.11 memory.copy: copy n bytes from src to dst within memory.
      -- REF: WasmCert-Coq r_memory_copy_forward / r_memory_copy_backward
      -- When regions overlap, copy direction depends on dst vs src to preserve correctness:
      --   dst ≤ src → forward copy (ascending indices)
      --   dst > src → backward copy (descending indices)
      | .memoryCopy dstMem srcMem =>
          match pop3? base.stack with
          | some (.i32 n, .i32 src, .i32 dst, stk) =>
              let memIdx := dstMem  -- MVP: dst and src must be memory 0
              match base.store.memories[memIdx]? with
              | some mem =>
                  let len := n.toNat
                  let srcOff := src.toNat
                  let dstOff := dst.toNat
                  if srcOff + len > mem.size || dstOff + len > mem.size then
                    some (trapState { base with stack := stk } "out of bounds memory access in memory.copy")
                  else
                    let copied := Id.run do
                      let mut m := mem
                      if dstOff <= srcOff then
                        -- Forward copy (ascending): safe when dst ≤ src
                        for i in List.range len do
                          let byte := if srcOff + i < m.size then m.get! (srcOff + i) else 0
                          if dstOff + i < m.size then
                            m := m.set! (dstOff + i) byte
                      else
                        -- Backward copy (descending): required when dst > src to avoid overwriting
                        for i in List.range len do
                          let j := len - 1 - i
                          let byte := if srcOff + j < m.size then m.get! (srcOff + j) else 0
                          if dstOff + j < m.size then
                            m := m.set! (dstOff + j) byte
                      return m
                    let store' := { base.store with memories := base.store.memories.set! memIdx copied }
                    some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none => some (trapState { base with stack := stk } s!"unknown memory index {memIdx}")
          | some _ => some (trapState base "type mismatch in memory.copy")
          | none => some (trapState base "stack underflow in memory.copy")
      -- SPEC §4.4.7.12 memory.fill: fill n bytes starting at dst with byte value.
      -- REF: WasmCert-Coq r_memory_fill
      | .memoryFill memIdx =>
          match pop3? base.stack with
          | some (.i32 n, .i32 val, .i32 dst, stk) =>
              match base.store.memories[memIdx]? with
              | some mem =>
                  let len := n.toNat
                  let dstOff := dst.toNat
                  let fillByte := UInt8.ofNat (val.toNat % 256)
                  if dstOff + len > mem.size then
                    some (trapState { base with stack := stk } "out of bounds memory access in memory.fill")
                  else
                    let filled := Id.run do
                      let mut m := mem
                      for i in List.range len do
                        if dstOff + i < m.size then
                          m := m.set! (dstOff + i) fillByte
                      return m
                    let store' := { base.store with memories := base.store.memories.set! memIdx filled }
                    some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none => some (trapState { base with stack := stk } s!"unknown memory index {memIdx}")
          | some _ => some (trapState base "type mismatch in memory.fill")
          | none => some (trapState base "stack underflow in memory.fill")
      -- SPEC §4.4.7.10 memory.init: copy from data segment into memory.
      -- REF: WasmCert-Coq r_memory_init
      | .memoryInit dataIdx memIdx =>
          match pop3? base.stack with
          | some (.i32 n, .i32 src, .i32 dst, stk) =>
              match base.store.memories[memIdx]?, base.store.datas[dataIdx]? with
              | some mem, some dataSeg =>
                  let len := n.toNat
                  let srcOff := src.toNat
                  let dstOff := dst.toNat
                  if srcOff + len > dataSeg.size then
                    some (trapState { base with stack := stk } "out of bounds data segment access in memory.init")
                  else if dstOff + len > mem.size then
                    some (trapState { base with stack := stk } "out of bounds memory access in memory.init")
                  else
                    let filled := Id.run do
                      let mut m := mem
                      for i in List.range len do
                        let byte := if srcOff + i < dataSeg.size then dataSeg.get! (srcOff + i) else 0
                        if dstOff + i < m.size then
                          m := m.set! (dstOff + i) byte
                      return m
                    let store' := { base.store with memories := base.store.memories.set! memIdx filled }
                    some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none, _ => some (trapState { base with stack := stk } s!"unknown memory index {memIdx}")
              | _, none => some (trapState { base with stack := stk } s!"unknown data segment index {dataIdx}")
          | some _ => some (trapState base "type mismatch in memory.init")
          | none => some (trapState base "stack underflow in memory.init")
      -- SPEC §4.4.7.14 table.init: copy from element segment into table.
      -- REF: WasmCert-Coq r_table_init
      | .tableInit elemIdx tableIdx =>
          match pop3? base.stack with
          | some (.i32 n, .i32 src, .i32 dst, stk) =>
              match base.store.tables[tableIdx]?, base.store.elems[elemIdx]? with
              | some tbl, some elemSeg =>
                  let len := n.toNat
                  let srcOff := src.toNat
                  let dstOff := dst.toNat
                  if srcOff + len > elemSeg.size then
                    some (trapState { base with stack := stk } "out of bounds element segment access in table.init")
                  else if dstOff + len > tbl.size then
                    some (trapState { base with stack := stk } "out of bounds table access in table.init")
                  else
                    let newTbl := Id.run do
                      let mut t := tbl
                      for i in List.range len do
                        if srcOff + i < elemSeg.size && dstOff + i < t.size then
                          t := t.set! (dstOff + i) (elemSeg.getD (srcOff + i) none)
                      return t
                    let store' := { base.store with tables := base.store.tables.set! tableIdx newTbl }
                    some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | none, _ => some (trapState { base with stack := stk } s!"unknown table index {tableIdx}")
              | _, none => some (trapState { base with stack := stk } s!"unknown element segment index {elemIdx}")
          | some _ => some (trapState base "type mismatch in table.init")
          | none => some (trapState base "stack underflow in table.init")
      -- SPEC §4.4.7.15 table.copy: copy elements between tables.
      -- REF: WasmCert-Coq r_table_copy_forward / r_table_copy_backward
      | .tableCopy dstIdx srcIdx =>
          match pop3? base.stack with
          | some (.i32 n, .i32 src, .i32 dst, stk) =>
              match base.store.tables[dstIdx]?, base.store.tables[srcIdx]? with
              | some dstTbl, some srcTbl =>
                  let len := n.toNat
                  let srcOff := src.toNat
                  let dstOff := dst.toNat
                  if srcOff + len > srcTbl.size || dstOff + len > dstTbl.size then
                    some (trapState { base with stack := stk } "out of bounds table access in table.copy")
                  else
                    let newTbl := Id.run do
                      let mut t := dstTbl
                      if dstOff <= srcOff then
                        for i in List.range len do
                          if srcOff + i < srcTbl.size && dstOff + i < t.size then
                            t := t.set! (dstOff + i) (srcTbl.getD (srcOff + i) none)
                      else
                        for i in List.range len do
                          let j := len - 1 - i
                          if srcOff + j < srcTbl.size && dstOff + j < t.size then
                            t := t.set! (dstOff + j) (srcTbl.getD (srcOff + j) none)
                      return t
                    let store' := { base.store with tables := base.store.tables.set! dstIdx newTbl }
                    some (.silent, pushTrace { base with store := store', stack := stk } .silent)
              | _, _ => some (trapState { base with stack := stk } "unknown table index in table.copy")
          | some _ => some (trapState base "type mismatch in table.copy")
          | none => some (trapState base "stack underflow in table.copy")
      -- SPEC §4.4.7.13 data.drop / §4.4.7.16 elem.drop: drop segment contents.
      -- REF: WasmCert-Coq r_data_drop / r_elem_drop
      | .dataDrop dataIdx =>
          let store' := { base.store with
            datas := if dataIdx < base.store.datas.size
                     then base.store.datas.set! dataIdx ByteArray.empty
                     else base.store.datas }
          some (.silent, pushTrace { base with store := store' } .silent)
      | .elemDrop elemIdx =>
          let store' := { base.store with
            elems := if elemIdx < base.store.elems.size
                     then base.store.elems.set! elemIdx #[]
                     else base.store.elems }
          some (.silent, pushTrace { base with store := store' } .silent)

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

/-- Empty code with no labels halts. -/
@[simp]
theorem step?_halt (s : ExecState) (h : s.code = [] ∧ s.labels = []) :
    step? s = none := by
  simp [step?, h.1, h.2]

/-- Step relation is equivalent to step? returning some. -/
theorem Step_iff (s : ExecState) (t : TraceEvent) (s' : ExecState) :
    Step s t s' ↔ step? s = some (t, s') :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- Steps.refl is the only way to produce an empty trace. -/
theorem Steps_nil_iff (s s' : ExecState) :
    Steps s [] s' ↔ s = s' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ Steps.refl s⟩

/-! ## @[simp] equation lemmas for step?

    These allow the proof agent to reason about individual instructions
    by unfolding step? to its result for specific instruction patterns. -/

/-- i32.const pushes a value onto the stack. -/
@[simp]
theorem step?_i32Const (s : ExecState) (n : UInt32) (rest : List Instr) :
    step? { s with code := .i32Const n :: rest } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 n :: s.stack } .silent) := by
  unfold step?; rfl

/-- i64.const pushes a value onto the stack. -/
@[simp]
theorem step?_i64Const (s : ExecState) (n : UInt64) (rest : List Instr) :
    step? { s with code := .i64Const n :: rest } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 n :: s.stack } .silent) := by
  unfold step?; rfl

/-- f64.const pushes a value onto the stack. -/
@[simp]
theorem step?_f64Const (s : ExecState) (n : Float) (rest : List Instr) :
    step? { s with code := .f64Const n :: rest } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 n :: s.stack } .silent) := by
  unfold step?; rfl

/-- nop is a no-op. -/
@[simp]
theorem step?_nop (s : ExecState) (rest : List Instr) :
    step? { s with code := .nop :: rest } =
      some (.silent, pushTrace { s with code := rest } .silent) := by
  unfold step?; rfl

/-- drop pops one value from the stack. -/
@[simp]
theorem step?_drop (s : ExecState) (v : WasmValue) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .drop :: rest, stack := v :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := stk } .silent) := by
  unfold step?; simp [pop1?]

/-- unreachable always traps. -/
@[simp]
theorem step?_unreachable (s : ExecState) (rest : List Instr) :
    step? { s with code := .unreachable :: rest } =
      some (trapState { s with code := rest } "unreachable executed") := by
  unfold step?; rfl

/-- local.get with valid index does not get stuck. -/
theorem step?_localGet_some (s : ExecState) (idx : Nat) (fr : Frame) (frs : List Frame)
    (rest : List Instr) (h : idx < fr.locals.size) :
    ∃ t s', step? { s with code := .localGet idx :: rest, frames := fr :: frs } = some (t, s') := by
  unfold step?; simp [h]

/-- dataDrop does not get stuck. -/
theorem step?_dataDrop_some (s : ExecState) (idx : DataIdx) (rest : List Instr) :
    ∃ t s', step? { s with code := .dataDrop idx :: rest } = some (t, s') := by
  unfold step?; exact ⟨_, _, rfl⟩

/-- elemDrop does not get stuck. -/
theorem step?_elemDrop_some (s : ExecState) (idx : ElemIdx) (rest : List Instr) :
    ∃ t s', step? { s with code := .elemDrop idx :: rest } = some (t, s') := by
  unfold step?; exact ⟨_, _, rfl⟩

/-- select with i32 condition does not get stuck. -/
theorem step?_select_some (s : ExecState) (n : UInt32) (v1 v2 : WasmValue)
    (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .select :: rest, stack := .i32 n :: v2 :: v1 :: stk } = some (t, s') := by
  unfold step?; simp [pop2?, pop1?, i32Truth]
  cases h : (n != 0) <;> exact ⟨_, _, rfl⟩

/-- An empty Store for use in lemmas and examples. -/
def Store.empty : Store :=
  { types := #[], funcs := #[], tables := #[], tableLimits := #[],
    memories := #[], memLimits := #[], globals := #[], datas := #[], elems := #[] }

/-- initialStore preserves the module's data segment payloads. -/
@[simp]
theorem initialStore_datas (m : Module) :
    (initialStore m).datas = m.datas.map (·.init) := by
  simp [initialStore]

/-- initialStore preserves the module's element segments as optional function indices. -/
@[simp]
theorem initialStore_elems (m : Module) :
    (initialStore m).elems = m.elems.map (fun seg => seg.funcIdxs.toArray.map some) := by
  simp [initialStore]

/-- initialStore preserves the module's type section. -/
@[simp]
theorem initialStore_types (m : Module) :
    (initialStore m).types = m.types := by
  simp [initialStore]

/-- initialStore preserves the module's function section. -/
@[simp]
theorem initialStore_funcs (m : Module) :
    (initialStore m).funcs = m.funcs := by
  simp [initialStore]

/-! ## Inhabitedness examples for Wasm.Step

    These construct concrete evaluation traces proving the Step inductive
    relation is inhabited. The proof agent can use these to establish that
    the semantics is non-trivially satisfiable. -/

/-- Witness: i32.const 42 pushes 42 onto the stack. -/
private def exState0 : ExecState :=
  { store := { types := #[], funcs := #[], tables := #[], tableLimits := #[], memories := #[], memLimits := #[], globals := #[], datas := #[], elems := #[] }
    stack := []
    frames := [{ locals := #[], moduleInst := 0 }]
    labels := []
    code := [.i32Const 42]
    trace := [] }

example : Step exState0 .silent (pushTrace { exState0 with code := [], stack := [.i32 42] } .silent) :=
  Step.mk (by unfold step?; rfl)

/-- Witness: i32.add on stack [3, 5] produces [8]. -/
private def exStateAdd : ExecState :=
  { store := { types := #[], funcs := #[], tables := #[], tableLimits := #[], memories := #[], memLimits := #[], globals := #[], datas := #[], elems := #[] }
    stack := [.i32 3, .i32 5]
    frames := [{ locals := #[], moduleInst := 0 }]
    labels := []
    code := [.i32Add]
    trace := [] }

example : Step exStateAdd .silent
    (pushTrace { exStateAdd with code := [], stack := [.i32 8] } .silent) :=
  Step.mk (by unfold step?; rfl)

/-- Witness: nop followed by i32.const — a two-step trace. -/
private def exStateNopConst : ExecState :=
  { store := { types := #[], funcs := #[], tables := #[], tableLimits := #[], memories := #[], memLimits := #[], globals := #[], datas := #[], elems := #[] }
    stack := []
    frames := [{ locals := #[], moduleInst := 0 }]
    labels := []
    code := [.nop, .i32Const 7]
    trace := [] }

example : Steps exStateNopConst [.silent, .silent]
    (pushTrace (pushTrace { exStateNopConst with code := [], stack := [.i32 7] } .silent) .silent) := by
  apply Steps.tail
  · exact Step.mk (by unfold step?; rfl)
  · apply Steps.tail
    · exact Step.mk (by unfold step?; rfl)
    · exact Steps.refl _

/-- Witness: unreachable traps. -/
private def exStateTrap : ExecState :=
  { store := { types := #[], funcs := #[], tables := #[], tableLimits := #[], memories := #[], memLimits := #[], globals := #[], datas := #[], elems := #[] }
    stack := []
    frames := [{ locals := #[], moduleInst := 0 }]
    labels := []
    code := [.unreachable]
    trace := [] }

example : Step exStateTrap (.trap "unreachable executed")
    (pushTrace { exStateTrap with code := [] } (.trap "unreachable executed")) :=
  Step.mk (by unfold step?; rfl)

/-! ## Structural theorems for Step/Steps -/

/-- Step is deterministic: the same state can only step to one successor. -/
theorem Step_deterministic {s : ExecState} {t1 t2 : TraceEvent} {s1 s2 : ExecState} :
    Step s t1 s1 → Step s t2 s2 → t1 = t2 ∧ s1 = s2 := by
  intro ⟨h1⟩ ⟨h2⟩; rw [h1] at h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2; exact h2

/-- Steps is transitive: concatenating two multi-step derivations. -/
theorem Steps_trans {s1 s2 s3 : ExecState} {t1 t2 : List TraceEvent} :
    Steps s1 t1 s2 → Steps s2 t2 s3 → Steps s1 (t1 ++ t2) s3 := by
  intro h1 h2
  induction h1 with
  | refl _ => exact h2
  | tail hstep _ ih => exact Steps.tail hstep (ih h2)

/-- If step? returns none, no Step can be taken. -/
theorem step?_none_no_step {s : ExecState} (h : step? s = none) :
    ∀ t s', ¬ Step s t s' := by
  intro t s' ⟨hs⟩; rw [hs] at h; exact absurd h (by simp)

/-! ## Additional @[simp] equation lemmas -/

/-- f32.const pushes a value onto the stack. -/
@[simp]
theorem step?_f32Const (s : ExecState) (n : Float) (rest : List Instr) :
    step? { s with code := .f32Const n :: rest } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 n :: s.stack } .silent) := by
  unfold step?; rfl

/-- i32.add on two i32 values. -/
@[simp]
theorem step?_i32Add (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Add :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Add a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.sub on two i32 values. -/
@[simp]
theorem step?_i32Sub (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Sub :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Sub a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.mul on two i32 values. -/
@[simp]
theorem step?_i32Mul (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Mul :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Mul a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i64.add on two i64 values. -/
@[simp]
theorem step?_i64Add (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Add :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Add a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- f64.add on two f64 values. -/
@[simp]
theorem step?_f64Add (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Add :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Add a b) :: stk } .silent) := by
  unfold step?; simp [withF64Bin, pop2?]

/-- f64.sub on two f64 values. -/
@[simp]
theorem step?_f64Sub (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Sub :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Sub a b) :: stk } .silent) := by
  unfold step?; simp [withF64Bin, pop2?]

/-- f64.mul on two f64 values. -/
@[simp]
theorem step?_f64Mul (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Mul :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Mul a b) :: stk } .silent) := by
  unfold step?; simp [withF64Bin, pop2?]

/-- global.get with valid index pushes the global's value. -/
@[simp]
theorem step?_globalGet (s : ExecState) (idx : Nat) (rest : List Instr)
    (h : idx < s.store.globals.size) :
    step? { s with code := .globalGet idx :: rest } =
      some (.silent, pushTrace { s with code := rest, stack := s.store.globals[idx] :: s.stack } .silent) := by
  unfold step?; simp [h]

/-- return clears labels and code. -/
@[simp]
theorem step?_return (s : ExecState) (rest : List Instr) :
    step? { s with code := .return_ :: rest } =
      some (.silent, pushTrace { s with code := [], labels := [] } .silent) := by
  unfold step?; rfl

/-- block pushes a label frame and enters the body. -/
@[simp]
theorem step?_block (s : ExecState) (bt : BlockType) (body rest : List Instr) :
    step? { s with code := .block bt body :: rest } =
      let lbl : LabelFrame := { onBranch := rest, onExit := rest, isLoop := false }
      some (.silent, pushTrace { s with code := body, labels := lbl :: s.labels } .silent) := by
  unfold step?; rfl

/-- loop pushes a label frame with onBranch = body and enters the body. -/
@[simp]
theorem step?_loop (s : ExecState) (bt : BlockType) (body rest : List Instr) :
    step? { s with code := .loop bt body :: rest } =
      let lbl : LabelFrame := { onBranch := body, onExit := rest, isLoop := true }
      some (.silent, pushTrace { s with code := body, labels := lbl :: s.labels } .silent) := by
  unfold step?; rfl

/-- i32.eqz on an i32 value. -/
@[simp]
theorem step?_i32Eqz (s : ExecState) (n : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Eqz :: rest, stack := .i32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Eqz n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- local.get with valid index and non-empty frames. -/
@[simp]
theorem step?_localGet (s : ExecState) (idx : Nat) (fr : Frame) (frs : List Frame)
    (rest : List Instr) (h : idx < fr.locals.size) :
    step? { s with code := .localGet idx :: rest, frames := fr :: frs } =
      some (.silent, pushTrace { s with code := rest, frames := fr :: frs, stack := fr.locals[idx] :: s.stack } .silent) := by
  unfold step?; simp [h]

/-! ## More inhabitedness examples -/

/-- Witness: local.get 0 from frame with one local. -/
private def exStateLocalGet : ExecState :=
  { store := Store.empty
    stack := []
    frames := [{ locals := #[.i32 99], moduleInst := 0 }]
    labels := []
    code := [.localGet 0]
    trace := [] }

example : Step exStateLocalGet .silent
    (pushTrace { exStateLocalGet with code := [], stack := [.i32 99] } .silent) :=
  Step.mk (by unfold step?; rfl)

/-- Witness: block enters body and pushes label. -/
private def exStateBlock : ExecState :=
  { store := Store.empty
    stack := []
    frames := [{ locals := #[], moduleInst := 0 }]
    labels := []
    code := [.block (.valType .i32) [.i32Const 10]]
    trace := [] }

example : Step exStateBlock .silent
    (pushTrace
      (let lbl : LabelFrame := ⟨[], [], false⟩
       { exStateBlock with code := [.i32Const 10], labels := [lbl] })
      .silent) :=
  Step.mk (by unfold step?; rfl)

/-- Witness: global.get 0 from store with one global. -/
private def exStateGlobalGet : ExecState :=
  { store := { Store.empty with globals := #[.i64 42] }
    stack := []
    frames := [{ locals := #[], moduleInst := 0 }]
    labels := []
    code := [.globalGet 0]
    trace := [] }

example : Step exStateGlobalGet .silent
    (pushTrace { exStateGlobalGet with code := [], stack := [.i64 42] } .silent) :=
  Step.mk (by unfold step?; rfl)

/-! ## Additional @[simp] lemmas for compiler-emitted instructions -/

/-- local.set with valid index updates the frame. -/
@[simp]
theorem step?_localSet (s : ExecState) (idx : Nat) (v : WasmValue) (stk : List WasmValue)
    (fr : Frame) (frs : List Frame) (rest : List Instr) (h : idx < fr.locals.size) :
    step? { s with code := .localSet idx :: rest, stack := v :: stk, frames := fr :: frs } =
      let fr' := { fr with locals := fr.locals.set! idx v }
      some (.silent, pushTrace { s with code := rest, stack := stk, frames := fr' :: frs } .silent) := by
  unfold step?; simp [pop1?, h, updateHeadFrame]

/-- global.set with valid index updates the store. -/
@[simp]
theorem step?_globalSet (s : ExecState) (idx : Nat) (v : WasmValue) (stk : List WasmValue)
    (rest : List Instr) (h : idx < s.store.globals.size) :
    step? { s with code := .globalSet idx :: rest, stack := v :: stk } =
      let globals' := s.store.globals.set! idx v
      some (.silent, pushTrace { s with code := rest, stack := stk, store := { s.store with globals := globals' } } .silent) := by
  unfold step?; simp [pop1?, h]

/-- br_if with false condition (0) continues to next instruction. -/
@[simp]
theorem step?_brIf_false (s : ExecState) (depth : Nat) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .brIf depth :: rest, stack := .i32 0 :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := stk } .silent) := by
  unfold step?; simp [pop1?, i32Truth]

/-- i32.eq comparison. -/
@[simp]
theorem step?_i32Eq (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Eq :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Eq a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.ne comparison. -/
@[simp]
theorem step?_i32Ne (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Ne :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Ne a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- f64.div on two f64 values. -/
@[simp]
theorem step?_f64Div (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Div :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Div a b) :: stk } .silent) := by
  unfold step?; simp [withF64Bin, pop2?]

/-- i32.wrap_i64 conversion. -/
@[simp]
theorem step?_i32WrapI64 (s : ExecState) (n : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32WrapI64 :: rest, stack := .i64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32WrapI64 n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- i64.extend_i32_s conversion. -/
@[simp]
theorem step?_i64ExtendI32s (s : ExecState) (n : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64ExtendI32s :: rest, stack := .i32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64ExtendI32s n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- i64.extend_i32_u conversion. -/
@[simp]
theorem step?_i64ExtendI32u (s : ExecState) (n : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64ExtendI32u :: rest, stack := .i32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64ExtendI32u n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.convert_i32_s conversion. -/
@[simp]
theorem step?_f64ConvertI32s (s : ExecState) (n : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64ConvertI32s :: rest, stack := .i32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64ConvertI32s n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.convert_i32_u conversion. -/
@[simp]
theorem step?_f64ConvertI32u (s : ExecState) (n : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64ConvertI32u :: rest, stack := .i32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64ConvertI32u n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.reinterpret_i64 conversion. -/
@[simp]
theorem step?_f64ReinterpretI64 (s : ExecState) (n : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64ReinterpretI64 :: rest, stack := .i64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64ReinterpretI64 n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- i32.lt_s comparison. -/
@[simp]
theorem step?_i32Lts (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Lts :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Lts a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.and bitwise operation. -/
@[simp]
theorem step?_i32And (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32And :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32And a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.or bitwise operation. -/
@[simp]
theorem step?_i32Or (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Or :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Or a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.shl shift operation. -/
@[simp]
theorem step?_i32Shl (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Shl :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Shl a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.shr_u shift operation. -/
@[simp]
theorem step?_i32ShrU (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32ShrU :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32ShrU a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.shr_s shift operation. -/
@[simp]
theorem step?_i32ShrS (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32ShrS :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32ShrS a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-! ## @[simp] lemmas: if_, br, brIf_true, localTee, remaining comparisons -/

/-- if with true condition (nonzero i32) enters the then branch. -/
@[simp]
theorem step?_if_true (s : ExecState) (bt : BlockType) (then_ else_ rest : List Instr)
    (n : UInt32) (stk : List WasmValue) (hn : n ≠ 0) :
    step? { s with code := .if_ bt then_ else_ :: rest, stack := .i32 n :: stk } =
      let lbl : LabelFrame := { onBranch := rest, onExit := rest, isLoop := false }
      some (.silent, pushTrace { s with stack := stk, labels := lbl :: s.labels, code := then_ } .silent) := by
  unfold step?; simp [pop1?, i32Truth]
  have : (n != 0) = true := by simp [bne_iff_ne, hn]
  simp [this]

/-- if with false condition (zero) enters the else branch. -/
@[simp]
theorem step?_if_false (s : ExecState) (bt : BlockType) (then_ else_ rest : List Instr)
    (stk : List WasmValue) :
    step? { s with code := .if_ bt then_ else_ :: rest, stack := .i32 0 :: stk } =
      let lbl : LabelFrame := { onBranch := rest, onExit := rest, isLoop := false }
      some (.silent, pushTrace { s with stack := stk, labels := lbl :: s.labels, code := else_ } .silent) := by
  unfold step?; simp [pop1?, i32Truth]

/-- br with depth 0 and a label frame resolves to onBranch. -/
@[simp]
theorem step?_br_zero (s : ExecState) (lbl : LabelFrame) (lbls : List LabelFrame) (rest : List Instr) :
    step? { s with code := .br 0 :: rest, labels := lbl :: lbls } =
      let kept := if lbl.isLoop then lbl :: lbls else lbls
      some (.silent, pushTrace { s with labels := kept, code := lbl.onBranch } .silent) := by
  unfold step?; simp [resolveBranch?]; unfold resolveBranch?.go; simp_all [pushTrace]

/-- br_if with true condition (nonzero) and depth 0 branches. -/
@[simp]
theorem step?_brIf_true (s : ExecState) (n : UInt32) (stk : List WasmValue)
    (lbl : LabelFrame) (lbls : List LabelFrame) (rest : List Instr) (hn : n ≠ 0) :
    step? { s with code := .brIf 0 :: rest, stack := .i32 n :: stk, labels := lbl :: lbls } =
      let kept := if lbl.isLoop then lbl :: lbls else lbls
      some (.silent, pushTrace { s with stack := stk, labels := kept, code := lbl.onBranch } .silent) := by
  unfold step?; simp [pop1?, i32Truth]
  have : (n != 0) = true := by simp [bne_iff_ne, hn]
  simp [this, resolveBranch?]; unfold resolveBranch?.go; simp_all [pushTrace]

/-- local.tee with valid index updates the frame but keeps the value on the stack. -/
@[simp]
theorem step?_localTee (s : ExecState) (idx : Nat) (v : WasmValue) (stk : List WasmValue)
    (fr : Frame) (frs : List Frame) (rest : List Instr) (h : idx < fr.locals.size) :
    step? { s with code := .localTee idx :: rest, stack := v :: stk, frames := fr :: frs } =
      let fr' := { fr with locals := fr.locals.set! idx v }
      some (.silent, pushTrace { s with code := rest, stack := v :: stk, frames := fr' :: frs } .silent) := by
  unfold step?; simp [pop1?, h, updateHeadFrame]

/-- i32.xor bitwise operation. -/
@[simp]
theorem step?_i32Xor (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Xor :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Xor a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.rotl rotation operation. -/
@[simp]
theorem step?_i32Rotl (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Rotl :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Rotl a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.rotr rotation operation. -/
@[simp]
theorem step?_i32Rotr (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Rotr :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32Rotr a b) :: stk } .silent) := by
  unfold step?; simp [withI32Bin, pop2?]

/-- i32.lt_u comparison. -/
@[simp]
theorem step?_i32Ltu (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Ltu :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Ltu a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.gt_s comparison. -/
@[simp]
theorem step?_i32Gts (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Gts :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Gts a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.gt_u comparison. -/
@[simp]
theorem step?_i32Gtu (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Gtu :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Gtu a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.le_s comparison. -/
@[simp]
theorem step?_i32Les (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Les :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Les a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.le_u comparison. -/
@[simp]
theorem step?_i32Leu (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Leu :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Leu a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.ge_s comparison. -/
@[simp]
theorem step?_i32Ges (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Ges :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Ges a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i32.ge_u comparison. -/
@[simp]
theorem step?_i32Geu (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32Geu :: rest, stack := .i32 b :: .i32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i32Geu a b) :: stk } .silent) := by
  unfold step?; simp [withI32Rel, pop2?]

/-- i64.sub on two i64 values. -/
@[simp]
theorem step?_i64Sub (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Sub :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Sub a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.mul on two i64 values. -/
@[simp]
theorem step?_i64Mul (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Mul :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Mul a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- f64.eq comparison. -/
@[simp]
theorem step?_f64Eq (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Eq :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f64Eq a b) :: stk } .silent) := by
  unfold step?; simp [withF64Rel, pop2?]

/-- f64.ne comparison. -/
@[simp]
theorem step?_f64Ne (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Ne :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f64Ne a b) :: stk } .silent) := by
  unfold step?; simp [withF64Rel, pop2?]

/-- f64.lt comparison. -/
@[simp]
theorem step?_f64Lt (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Lt :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f64Lt a b) :: stk } .silent) := by
  unfold step?; simp [withF64Rel, pop2?]

/-- f64.gt comparison. -/
@[simp]
theorem step?_f64Gt (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Gt :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f64Gt a b) :: stk } .silent) := by
  unfold step?; simp [withF64Rel, pop2?]

/-- f64.le comparison. -/
@[simp]
theorem step?_f64Le (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Le :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f64Le a b) :: stk } .silent) := by
  unfold step?; simp [withF64Rel, pop2?]

/-- f64.ge comparison. -/
@[simp]
theorem step?_f64Ge (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Ge :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f64Ge a b) :: stk } .silent) := by
  unfold step?; simp [withF64Rel, pop2?]

/-- f64.min on two f64 values. -/
@[simp]
theorem step?_f64Min (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Min :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Min a b) :: stk } .silent) := by
  unfold step?; simp [withF64Bin, pop2?]

/-- f64.max on two f64 values. -/
@[simp]
theorem step?_f64Max (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Max :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Max a b) :: stk } .silent) := by
  unfold step?; simp [withF64Bin, pop2?]

/-- f64.abs on an f64 value. -/
@[simp]
theorem step?_f64Abs (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Abs :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Abs n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.neg on an f64 value. -/
@[simp]
theorem step?_f64Neg (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Neg :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Neg n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.sqrt on an f64 value. -/
@[simp]
theorem step?_f64Sqrt (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Sqrt :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Sqrt n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.ceil on an f64 value. -/
@[simp]
theorem step?_f64Ceil (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Ceil :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Ceil n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.floor on an f64 value. -/
@[simp]
theorem step?_f64Floor (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Floor :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Floor n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.trunc on an f64 value. -/
@[simp]
theorem step?_f64Trunc (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Trunc :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Trunc n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.nearest on an f64 value. -/
@[simp]
theorem step?_f64Nearest (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Nearest :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Nearest n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- memory.size pushes current page count. -/
@[simp]
theorem step?_memorySize (s : ExecState) (memIdx : MemIdx) (rest : List Instr)
    (h : memIdx < s.store.memories.size) :
    step? { s with code := .memorySize memIdx :: rest } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (UInt32.ofNat (s.store.memories[memIdx].size / 65536)) :: s.stack } .silent) := by
  unfold step?; simp [h]

/-- select with true condition (nonzero i32) picks v1. -/
@[simp]
theorem step?_select_true (s : ExecState) (n : UInt32) (v1 v2 : WasmValue)
    (stk : List WasmValue) (rest : List Instr) (hn : n ≠ 0) :
    step? { s with code := .select :: rest, stack := .i32 n :: v2 :: v1 :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := v1 :: stk } .silent) := by
  unfold step?; simp [pop2?, pop1?, i32Truth]
  have : (n != 0) = true := by simp [bne_iff_ne, hn]
  simp [this]

/-- select with false condition (0) picks v2. -/
@[simp]
theorem step?_select_false (s : ExecState) (v1 v2 : WasmValue)
    (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .select :: rest, stack := .i32 0 :: v2 :: v1 :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := v2 :: stk } .silent) := by
  unfold step?; simp [pop2?, pop1?, i32Truth]

/-- Label scope completion: empty code pops the innermost label. -/
@[simp]
theorem step?_labelExit (s : ExecState) (lbl : LabelFrame) (lbls : List LabelFrame) :
    step? { s with code := [], labels := lbl :: lbls } =
      some (.silent, pushTrace { s with labels := lbls, code := lbl.onExit } .silent) := by
  unfold step?; rfl

/-- i64.eqz on an i64 value. -/
@[simp]
theorem step?_i64Eqz (s : ExecState) (n : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Eqz :: rest, stack := .i64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Eqz n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f64.copysign on two f64 values. -/
@[simp]
theorem step?_f64Copysign (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64Copysign :: rest, stack := .f64 b :: .f64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64Copysign a b) :: stk } .silent) := by
  unfold step?; simp [withF64Bin, pop2?]

/-- f64.promote_f32 conversion. -/
@[simp]
theorem step?_f64PromoteF32 (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f64PromoteF32 :: rest, stack := .f32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (Numerics.f64PromoteF32 n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f32.demote_f64 conversion. -/
@[simp]
theorem step?_f32DemoteF64 (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32DemoteF64 :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32DemoteF64 n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- i32.reinterpret_f32 conversion. -/
@[simp]
theorem step?_i32ReinterpretF32 (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i32ReinterpretF32 :: rest, stack := .f32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (Numerics.i32ReinterpretF32 n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- i64.reinterpret_f64 conversion. -/
@[simp]
theorem step?_i64ReinterpretF64 (s : ExecState) (n : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64ReinterpretF64 :: rest, stack := .f64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64ReinterpretF64 n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- f32.reinterpret_i32 conversion. -/
@[simp]
theorem step?_f32ReinterpretI32 (s : ExecState) (n : UInt32) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32ReinterpretI32 :: rest, stack := .i32 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32ReinterpretI32 n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-! ## Memory load/store @[simp] lemmas

    These lemmas cover the most common memory access patterns used by the compiler.
    They require concrete memory and successful read/write conditions. -/

/-- i32.load with successful memory read. -/
theorem step?_i32Load_some (s : ExecState) (ma : MemArg) (addr : UInt32) (stk : List WasmValue)
    (rest : List Instr) (mem : ByteArray) (raw : UInt64)
    (hmem0 : s.store.memories[0]? = some mem)
    (hread : readLE? mem (addr.toNat + ma.offset) 4 = some raw) :
    step? { s with code := .i32Load ma :: rest, stack := .i32 addr :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (UInt32.ofNat raw.toNat) :: stk } .silent) := by
  unfold step?; simp [pop1?, hmem0, hread]

/-- i64.load with successful memory read. -/
theorem step?_i64Load_some (s : ExecState) (ma : MemArg) (addr : UInt32) (stk : List WasmValue)
    (rest : List Instr) (mem : ByteArray) (raw : UInt64)
    (hmem0 : s.store.memories[0]? = some mem)
    (hread : readLE? mem (addr.toNat + ma.offset) 8 = some raw) :
    step? { s with code := .i64Load ma :: rest, stack := .i32 addr :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 raw :: stk } .silent) := by
  unfold step?; simp [pop1?, hmem0, hread]

/-- f64.load with successful memory read. -/
theorem step?_f64Load_some (s : ExecState) (ma : MemArg) (addr : UInt32) (stk : List WasmValue)
    (rest : List Instr) (mem : ByteArray) (raw : UInt64)
    (hmem0 : s.store.memories[0]? = some mem)
    (hread : readLE? mem (addr.toNat + ma.offset) 8 = some raw) :
    step? { s with code := .f64Load ma :: rest, stack := .i32 addr :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f64 (u64BitsToFloat raw) :: stk } .silent) := by
  unfold step?; simp [pop1?, hmem0, hread]

/-- f32.load with successful memory read. -/
theorem step?_f32Load_some (s : ExecState) (ma : MemArg) (addr : UInt32) (stk : List WasmValue)
    (rest : List Instr) (mem : ByteArray) (raw : UInt64)
    (hmem0 : s.store.memories[0]? = some mem)
    (hread : readLE? mem (addr.toNat + ma.offset) 4 = some raw) :
    step? { s with code := .f32Load ma :: rest, stack := .i32 addr :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (u32BitsToFloat (UInt32.ofNat raw.toNat)) :: stk } .silent) := by
  unfold step?; simp [pop1?, hmem0, hread]

/-- i32.load8_u with successful memory read. -/
theorem step?_i32Load8u_some (s : ExecState) (ma : MemArg) (addr : UInt32) (stk : List WasmValue)
    (rest : List Instr) (mem : ByteArray) (raw : UInt64)
    (hmem0 : s.store.memories[0]? = some mem)
    (hread : readLE? mem (addr.toNat + ma.offset) 1 = some raw) :
    step? { s with code := .i32Load8u ma :: rest, stack := .i32 addr :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i32 (UInt32.ofNat raw.toNat) :: stk } .silent) := by
  unfold step?; simp [pop1?, hmem0, hread]

/-- i32.store with successful memory write (4 bytes). -/
theorem step?_i32Store_some (s : ExecState) (ma : MemArg) (val : UInt32) (addr : UInt32)
    (stk : List WasmValue) (rest : List Instr) (mem mem' : ByteArray)
    (hmem0 : s.store.memories[0]? = some mem)
    (hwrite : writeLE? mem (addr.toNat + ma.offset) 4 val.toUInt64 = some mem') :
    step? { s with code := .i32Store ma :: rest, stack := .i32 val :: .i32 addr :: stk } =
      let store' := { s.store with memories := s.store.memories.set! 0 mem' }
      some (.silent, pushTrace { s with code := rest, stack := stk, store := store' } .silent) := by
  unfold step?; simp [pop2?, hmem0, hwrite]

/-- f64.store with successful memory write (8 bytes). -/
theorem step?_f64Store_some (s : ExecState) (ma : MemArg) (v : Float) (addr : UInt32)
    (stk : List WasmValue) (rest : List Instr) (mem mem' : ByteArray)
    (hmem0 : s.store.memories[0]? = some mem)
    (hwrite : writeLE? mem (addr.toNat + ma.offset) 8 (floatToU64Bits v) = some mem') :
    step? { s with code := .f64Store ma :: rest, stack := .f64 v :: .i32 addr :: stk } =
      let store' := { s.store with memories := s.store.memories.set! 0 mem' }
      some (.silent, pushTrace { s with code := rest, stack := stk, store := store' } .silent) := by
  unfold step?; simp [pop2?, hmem0, hwrite]

/-- i32.store8 with successful memory write (1 byte). -/
theorem step?_i32Store8_some (s : ExecState) (ma : MemArg) (val : UInt32) (addr : UInt32)
    (stk : List WasmValue) (rest : List Instr) (mem mem' : ByteArray)
    (hmem0 : s.store.memories[0]? = some mem)
    (hwrite : writeLE? mem (addr.toNat + ma.offset) 1 val.toUInt64 = some mem') :
    step? { s with code := .i32Store8 ma :: rest, stack := .i32 val :: .i32 addr :: stk } =
      let store' := { s.store with memories := s.store.memories.set! 0 mem' }
      some (.silent, pushTrace { s with code := rest, stack := stk, store := store' } .silent) := by
  unfold step?; simp [pop2?, hmem0, hwrite]

/-! ## Division/remainder lemmas (require nonzero divisor) -/

/-- i32.div_u always produces a result (either success or trap). -/
theorem step?_i32DivU_some (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i32DivU :: rest, stack := .i32 b :: .i32 a :: stk } = some (t, s') := by
  unfold step?; simp [withI32Div, pop2?]
  split <;> exact ⟨_, _, rfl⟩

/-- i32.rem_u always produces a result (either success or trap). -/
theorem step?_i32RemU_some (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i32RemU :: rest, stack := .i32 b :: .i32 a :: stk } = some (t, s') := by
  unfold step?; simp [withI32Rem, pop2?]
  split <;> exact ⟨_, _, rfl⟩

/-- i32.div_s always produces a result. -/
theorem step?_i32DivS_some (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i32DivS :: rest, stack := .i32 b :: .i32 a :: stk } = some (t, s') := by
  unfold step?; simp [withI32Div, pop2?]
  split <;> (try split) <;> (try split) <;> exact ⟨_, _, rfl⟩

/-- i32.rem_s always produces a result. -/
theorem step?_i32RemS_some (s : ExecState) (a b : UInt32) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i32RemS :: rest, stack := .i32 b :: .i32 a :: stk } = some (t, s') := by
  unfold step?; simp [withI32Rem, pop2?]
  split <;> (try split) <;> exact ⟨_, _, rfl⟩

/-! ## i64 store @[simp] lemma -/

/-- i64.store with successful memory write (8 bytes). -/
theorem step?_i64Store_some (s : ExecState) (ma : MemArg) (val : UInt64) (addr : UInt32)
    (stk : List WasmValue) (rest : List Instr) (mem mem' : ByteArray)
    (hmem0 : s.store.memories[0]? = some mem)
    (hwrite : writeLE? mem (addr.toNat + ma.offset) 8 val = some mem') :
    step? { s with code := .i64Store ma :: rest, stack := .i64 val :: .i32 addr :: stk } =
      let store' := { s.store with memories := s.store.memories.set! 0 mem' }
      some (.silent, pushTrace { s with code := rest, stack := stk, store := store' } .silent) := by
  unfold step?; simp [pop2?, hmem0, hwrite]

/-! ### Hypothesis-form equation lemmas for step?
    These take code/stack hypotheses instead of requiring { s with ... } form.
    Useful for simulation proofs where we know the state structure from invariants. -/

/-- Exact step? result for drop with hypothesis-form arguments. -/
theorem step?_eq_drop (s : ExecState) (rest : List Instr)
    (v : WasmValue) (stk : List WasmValue)
    (hcode : s.code = Instr.drop :: rest)
    (hstack : s.stack = v :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.drop :: rest, stack := v :: stk } = s := by
    cases s; simp_all
  rw [← this]
  simp [step?_drop, pushTrace]

/-- Exact step? result for drop with empty stack (trap). -/
theorem step?_eq_drop_empty (s : ExecState) (rest : List Instr)
    (hcode : s.code = Instr.drop :: rest)
    (hstack : s.stack = []) :
    step? s = some (.trap "stack underflow in drop",
      { s with
        code := []
        stack := []
        trace := s.trace ++ [.trap "stack underflow in drop"] }) := by
  simp [step?, hcode, hstack, pop1?, trapState, pushTrace]

/-- Exact step? result for i32.const with hypothesis-form arguments. -/
theorem step?_eq_i32Const (s : ExecState) (n : UInt32) (rest : List Instr)
    (hcode : s.code = Instr.i32Const n :: rest) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i32 n :: s.stack
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Const n :: rest } = s := by
    cases s; simp_all
  rw [← this]
  simp [step?_i32Const, pushTrace]

/-- Exact step? result for i64.const with hypothesis-form arguments. -/
theorem step?_eq_i64Const (s : ExecState) (n : UInt64) (rest : List Instr)
    (hcode : s.code = Instr.i64Const n :: rest) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i64 n :: s.stack
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i64Const n :: rest } = s := by
    cases s; simp_all
  rw [← this]
  simp [step?_i64Const, pushTrace]

/-- Exact step? result for f64.const with hypothesis-form arguments. -/
theorem step?_eq_f64Const (s : ExecState) (f : Float) (rest : List Instr)
    (hcode : s.code = Instr.f64Const f :: rest) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .f64 f :: s.stack
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.f64Const f :: rest } = s := by
    cases s; simp_all
  rw [← this]
  simp [step?_f64Const, pushTrace]

/-- Exact step? result for return with hypothesis-form arguments. -/
theorem step?_eq_return (s : ExecState) (rest : List Instr)
    (hcode : s.code = Instr.return_ :: rest) :
    step? s = some (.silent,
      { s with
        code := []
        labels := []
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.return_ :: rest } = s := by
    cases s; simp_all
  rw [← this]
  simp [step?_return, pushTrace]

/-! ## Behavioral semantics theorems -/

/-- Deterministic execution: Steps from the same state yield the same trace and final state. -/
theorem Steps_deterministic {s : ExecState} {t1 t2 : List TraceEvent} {s1 s2 : ExecState} :
    Steps s t1 s1 → step? s1 = none →
    Steps s t2 s2 → step? s2 = none →
    t1 = t2 ∧ s1 = s2 := by
  intro hsteps1 hhalt1 hsteps2 hhalt2
  induction hsteps1 generalizing t2 s2 with
  | refl _ =>
    cases hsteps2 with
    | refl _ => exact ⟨rfl, rfl⟩
    | tail hstep _ =>
      obtain ⟨h⟩ := hstep
      rw [hhalt1] at h; exact absurd h (by simp)
  | tail hstep _ ih =>
    cases hsteps2 with
    | refl _ =>
      obtain ⟨h⟩ := hstep
      rw [hhalt2] at h; exact absurd h (by simp)
    | tail hstep2 hsteps2' =>
      obtain ⟨h1⟩ := hstep
      obtain ⟨h2⟩ := hstep2
      rw [h1] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨ht, hs⟩ := h2
      subst ht; subst hs
      have ⟨htl, hsl⟩ := ih hhalt1 hsteps2' hhalt2
      exact ⟨by rw [htl], hsl⟩

/-- Behavioral equivalence is deterministic: a module can only produce one trace. -/
theorem Behaves_deterministic {m : Module} {b1 b2 : List TraceEvent} :
    Behaves m b1 → Behaves m b2 → b1 = b2 := by
  intro ⟨s1, hsteps1, hhalt1⟩ ⟨s2, hsteps2, hhalt2⟩
  exact (Steps_deterministic hsteps1 hhalt1 hsteps2 hhalt2).1

/-- If a module exhibits behavior b via Steps, then Behaves holds. -/
theorem Behaves_of_Steps {m : Module} {sFinal : ExecState} {b : List TraceEvent}
    (hsteps : Steps (initialState m) b sFinal)
    (hhalt : step? sFinal = none) :
    Behaves m b :=
  ⟨sFinal, hsteps, hhalt⟩

/-- Steps can be extended by one step at the end. -/
theorem Steps_snoc {s1 s2 s3 : ExecState} {ts : List TraceEvent} {t : TraceEvent} :
    Steps s1 ts s2 → Step s2 t s3 → Steps s1 (ts ++ [t]) s3 := by
  intro hsteps hstep
  exact Steps_trans hsteps (Steps.tail hstep (Steps.refl _))

/-- A single step is a one-element Steps trace. -/
theorem Steps_single {s1 s2 : ExecState} {t : TraceEvent} :
    Step s1 t s2 → Steps s1 [t] s2 :=
  fun h => Steps.tail h (Steps.refl _)

/-- If step? returns some, there is a Step. -/
theorem step?_some_Step {s : ExecState} {t : TraceEvent} {s' : ExecState}
    (h : step? s = some (t, s')) : Step s t s' :=
  Step.mk h

/-! ## call instruction: does not get stuck with valid index and sufficient stack -/

/-- call with valid function index always produces a result (success or trap). -/
theorem step?_call_some (s : ExecState) (idx : Nat) (rest : List Instr)
    (hFunc : idx < s.store.funcs.size) :
    ∃ t s', step? { s with code := .call idx :: rest } = some (t, s') := by
  simp only [step?]
  simp [hFunc]
  split <;> (try split) <;> exact ⟨_, _, rfl⟩

/-! ## i64 division/remainder lemmas -/

/-- i64.div_u always produces a result (success or trap). -/
theorem step?_i64DivU_some (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i64DivU :: rest, stack := .i64 b :: .i64 a :: stk } = some (t, s') := by
  unfold step?; simp [withI64Div, pop2?]
  split <;> exact ⟨_, _, rfl⟩

/-- i64.div_s always produces a result. -/
theorem step?_i64DivS_some (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i64DivS :: rest, stack := .i64 b :: .i64 a :: stk } = some (t, s') := by
  unfold step?; simp [withI64Div, pop2?]
  split <;> (try split) <;> (try split) <;> exact ⟨_, _, rfl⟩

/-- i64.rem_u always produces a result. -/
theorem step?_i64RemU_some (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i64RemU :: rest, stack := .i64 b :: .i64 a :: stk } = some (t, s') := by
  unfold step?; simp [withI64Rem, pop2?]
  split <;> exact ⟨_, _, rfl⟩

/-- i64.rem_s always produces a result. -/
theorem step?_i64RemS_some (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    ∃ t s', step? { s with code := .i64RemS :: rest, stack := .i64 b :: .i64 a :: stk } = some (t, s') := by
  unfold step?; simp [withI64Rem, pop2?]
  split <;> (try split) <;> exact ⟨_, _, rfl⟩

/-! ## State classification and progress -/

/-- A state has halted when there is no code left and no labels to pop. -/
def ExecState.halted (s : ExecState) : Prop :=
  s.code = [] ∧ s.labels = []

/-- Halted states have step? = none. -/
@[simp]
theorem step?_halted {s : ExecState} (h : s.halted) : step? s = none := by
  simp [step?, h.1, h.2]

/-- Non-halted states with code = [] but labels ≠ [] always step (label exit). -/
theorem step?_label_nonempty {s : ExecState} (hcode : s.code = []) (l : LabelFrame)
    (ls : List LabelFrame) (hlabels : s.labels = l :: ls) :
    ∃ t s', step? s = some (t, s') := by
  simp [step?, hcode, hlabels]

/-- Helper function progress: withI32Bin always returns some. -/
private theorem withI32Bin_some (s : ExecState) (op : UInt32 → UInt32 → UInt32) (name : String) :
    ∃ t s', withI32Bin s op name = some (t, s') := by
  simp [withI32Bin]
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- Helper function progress: withI32Rel always returns some when given i32 operands. -/
private theorem withI32Rel_some (s : ExecState) (op : UInt32 → UInt32 → Bool) (name : String)
    (a b : UInt32) (stk : List WasmValue) (hstk : s.stack = .i32 b :: .i32 a :: stk) :
    ∃ t s', withI32Rel s op name = some (t, s') := by
  simp [withI32Rel, pop2?, hstk]

/-! ## i64 bitwise @[simp] lemmas (used by Emit.lean) -/

/-- i64.and on two i64 values. -/
@[simp]
theorem step?_i64And (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64And :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64And a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.or on two i64 values. -/
@[simp]
theorem step?_i64Or (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Or :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Or a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.xor on two i64 values. -/
@[simp]
theorem step?_i64Xor (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Xor :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Xor a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.shl on two i64 values. -/
@[simp]
theorem step?_i64Shl (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Shl :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Shl a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.shr_s on two i64 values. -/
@[simp]
theorem step?_i64ShrS (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64ShrS :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64ShrS a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.shr_u on two i64 values. -/
@[simp]
theorem step?_i64ShrU (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64ShrU :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64ShrU a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-! ## i64 relational @[simp] lemmas (used by Emit.lean) -/

/-- i64.eq comparison. -/
@[simp]
theorem step?_i64Eq (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Eq :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Eq a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.ne comparison. -/
@[simp]
theorem step?_i64Ne (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Ne :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Ne a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.lt_s comparison. -/
@[simp]
theorem step?_i64Lts (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Lts :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Lts a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.gt_s comparison. -/
@[simp]
theorem step?_i64Gts (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Gts :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Gts a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.le_s comparison. -/
@[simp]
theorem step?_i64Les (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Les :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Les a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.ge_s comparison. -/
@[simp]
theorem step?_i64Ges (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Ges :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Ges a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.lt_u comparison. -/
@[simp]
theorem step?_i64Ltu (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Ltu :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Ltu a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.gt_u comparison. -/
@[simp]
theorem step?_i64Gtu (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Gtu :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Gtu a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.le_u comparison. -/
@[simp]
theorem step?_i64Leu (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Leu :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Leu a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-- i64.ge_u comparison. -/
@[simp]
theorem step?_i64Geu (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Geu :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.i64Geu a b) :: stk } .silent) := by
  unfold step?; simp [withI64Rel, pop2?]

/-! ## i64 conversion @[simp] lemmas -/

/-- i64.rotl on two i64 values. -/
@[simp]
theorem step?_i64Rotl (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Rotl :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Rotl a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.rotr on two i64 values. -/
@[simp]
theorem step?_i64Rotr (s : ExecState) (a b : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Rotr :: rest, stack := .i64 b :: .i64 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Rotr a b) :: stk } .silent) := by
  unfold step?; simp [withI64Bin, pop2?]

/-- i64.clz on an i64 value. -/
@[simp]
theorem step?_i64Clz (s : ExecState) (n : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Clz :: rest, stack := .i64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Clz n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- i64.ctz on an i64 value. -/
@[simp]
theorem step?_i64Ctz (s : ExecState) (n : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Ctz :: rest, stack := .i64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Ctz n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-- i64.popcnt on an i64 value. -/
@[simp]
theorem step?_i64Popcnt (s : ExecState) (n : UInt64) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .i64Popcnt :: rest, stack := .i64 n :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .i64 (Numerics.i64Popcnt n) :: stk } .silent) := by
  unfold step?; simp [pop1?]

/-! ## f32 binary @[simp] lemmas -/

/-- f32.eq comparison. -/
@[simp]
theorem step?_f32Eq (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Eq :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f32Eq a b) :: stk } .silent) := by
  unfold step?; simp [withF32Rel, pop2?]

/-- f32.ne comparison. -/
@[simp]
theorem step?_f32Ne (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Ne :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f32Ne a b) :: stk } .silent) := by
  unfold step?; simp [withF32Rel, pop2?]

/-- f32.lt comparison. -/
@[simp]
theorem step?_f32Lt (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Lt :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f32Lt a b) :: stk } .silent) := by
  unfold step?; simp [withF32Rel, pop2?]

/-- f32.gt comparison. -/
@[simp]
theorem step?_f32Gt (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Gt :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f32Gt a b) :: stk } .silent) := by
  unfold step?; simp [withF32Rel, pop2?]

/-- f32.le comparison. -/
@[simp]
theorem step?_f32Le (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Le :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f32Le a b) :: stk } .silent) := by
  unfold step?; simp [withF32Rel, pop2?]

/-- f32.ge comparison. -/
@[simp]
theorem step?_f32Ge (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Ge :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := boolToI32 (Numerics.f32Ge a b) :: stk } .silent) := by
  unfold step?; simp [withF32Rel, pop2?]

/-- f32.add on two f32 values. -/
@[simp]
theorem step?_f32Add (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Add :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32Add a b) :: stk } .silent) := by
  unfold step?; simp [withF32Bin, pop2?]

/-- f32.sub on two f32 values. -/
@[simp]
theorem step?_f32Sub (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Sub :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32Sub a b) :: stk } .silent) := by
  unfold step?; simp [withF32Bin, pop2?]

/-- f32.mul on two f32 values. -/
@[simp]
theorem step?_f32Mul (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Mul :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32Mul a b) :: stk } .silent) := by
  unfold step?; simp [withF32Bin, pop2?]

/-- f32.div on two f32 values. -/
@[simp]
theorem step?_f32Div (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Div :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32Div a b) :: stk } .silent) := by
  unfold step?; simp [withF32Bin, pop2?]

/-- f32.min on two f32 values. -/
@[simp]
theorem step?_f32Min (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Min :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32Min a b) :: stk } .silent) := by
  unfold step?; simp [withF32Bin, pop2?]

/-- f32.max on two f32 values. -/
@[simp]
theorem step?_f32Max (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Max :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32Max a b) :: stk } .silent) := by
  unfold step?; simp [withF32Bin, pop2?]

/-- f32.copysign on two f32 values. -/
@[simp]
theorem step?_f32Copysign (s : ExecState) (a b : Float) (stk : List WasmValue) (rest : List Instr) :
    step? { s with code := .f32Copysign :: rest, stack := .f32 b :: .f32 a :: stk } =
      some (.silent, pushTrace { s with code := rest, stack := .f32 (Numerics.f32Copysign a b) :: stk } .silent) := by
  unfold step?; simp [withF32Bin, pop2?]

/-! ## Wasm step? Progress (type soundness analog)

    Every non-halted Wasm state can take a step.
    This is the Wasm-level analog of irStep?_progress. -/

/-- Every Wasm state with non-empty code can take a step (produces some or traps).
    SPEC: Wasm §4 — every instruction either reduces or traps. -/
theorem step?_code_nonempty (s : ExecState) (instr : Instr) (rest : List Instr)
    (hc : s.code = instr :: rest) :
    ∃ t s', step? s = some (t, s') := by
  -- Proof: unfold step?, case-split on instr, each case is either directly
  -- ⟨_, _, rfl⟩ or requires unfolding helper functions and splitting.
  unfold step?; rw [hc]
  cases instr <;> simp_all only [] <;>
    first
    | exact ⟨_, _, rfl⟩
    | (try simp only [withI32Bin, withI64Bin, withF32Bin, withF64Bin,
                       withI32Rel, withI64Rel, withF32Rel, withF64Rel,
                       withI32Div, withI32Rem, withI64Div, withI64Rem,
                       pop2?, pop1?, pop3?]
       repeat (first | exact ⟨_, _, rfl⟩ | split))

/-- Every Wasm state is either halted or can take a step (full progress theorem).
    SPEC: Wasm type soundness analog — well-formed states always make progress.
    REF: WasmCert-Coq progress theorem for reduce. -/
theorem step?_progress (s : ExecState) :
    s.halted ∨ ∃ t s', step? s = some (t, s') := by
  match hc : s.code with
  | instr :: rest => exact Or.inr (step?_code_nonempty s instr rest hc)
  | [] =>
    match hl : s.labels with
    | l :: ls =>
      right; simp [step?, hc, hl, pushTrace]
    | [] =>
      left; exact ⟨hc, hl⟩

/-- Corollary: step? returns none if and only if the state is halted. -/
theorem step?_none_iff_halted (s : ExecState) :
    step? s = none ↔ s.halted := by
  constructor
  · intro h
    rcases step?_progress s with hh | ⟨t, s', hs⟩
    · exact hh
    · rw [h] at hs; exact absurd hs (by simp)
  · intro h; exact step?_halted h

/-! ### Observable Wasm Events -/

/-- Observable events at the Wasm level: filter out `.silent`, keep `.trap`. -/
def observableWasmEvents : List TraceEvent → List TraceEvent
  | [] => []
  | .silent :: ts => observableWasmEvents ts
  | t :: ts => t :: observableWasmEvents ts

@[simp] theorem observableWasmEvents_nil :
    observableWasmEvents ([] : List TraceEvent) = [] := rfl

@[simp] theorem observableWasmEvents_cons_silent (ts : List TraceEvent) :
    observableWasmEvents (.silent :: ts) = observableWasmEvents ts := rfl

@[simp] theorem observableWasmEvents_cons_trap (s : String) (ts : List TraceEvent) :
    observableWasmEvents (.trap s :: ts) = .trap s :: observableWasmEvents ts := rfl

@[simp] theorem observableWasmEvents_append (ts1 ts2 : List TraceEvent) :
    observableWasmEvents (ts1 ++ ts2) = observableWasmEvents ts1 ++ observableWasmEvents ts2 := by
  induction ts1 with
  | nil => simp [observableWasmEvents]
  | cons t ts1 ih =>
    cases t with
    | silent => simp [observableWasmEvents, ih]
    | trap msg => simp [observableWasmEvents, ih]

/-- observableWasmEvents of a singleton: only traps are observable. -/
@[simp] theorem observableWasmEvents_singleton_silent :
    observableWasmEvents [TraceEvent.silent] = [] := rfl

@[simp] theorem observableWasmEvents_singleton_trap (msg : String) :
    observableWasmEvents [TraceEvent.trap msg] = [.trap msg] := rfl

/-- Behavioral equivalence up to silent events at the Wasm level.
    The Wasm module produces a trace whose observable events match `obs`. -/
def BehavesObs (m : Module) (obs : List TraceEvent) : Prop :=
  ∃ (sFinal : ExecState) (w_trace : List TraceEvent),
    Steps (initialState m) w_trace sFinal ∧
    step? sFinal = none ∧
    observableWasmEvents w_trace = obs

end VerifiedJS.Wasm

/-! ----------------------------------------------------------------
  ## Wasm IR Behavioral Semantics
  Small-step reduction and behavioral semantics for the structured IR.
  SPEC: Bridges ANF.Behaves (Core.TraceEvent) to Wasm.Behaves (Wasm.TraceEvent).

  The IR is a structured control-flow stack machine that is:
  - The output of lowering (ANF → IR)
  - The input of emission (IR → Wasm AST)

  These definitions enable:
  - LowerCorrect: ∀ trace, ANF.Behaves s trace → IR.Behaves t trace
  - EmitCorrect:  ∀ trace, IR.Behaves s trace → Wasm.Behaves t trace
  ---------------------------------------------------------------- -/

namespace VerifiedJS.Wasm.IR

/-! ### IR Trace Events -/

/-- Observable trace events for IR execution.
    Superset of both Core.TraceEvent (log/error/silent) and Wasm.TraceEvent (silent/trap).
    This enables the proof chain to map between trace types at pass boundaries. -/
inductive TraceEvent where
  | silent
  | trap (msg : String)
  | log (s : String)
  | error (s : String)
  deriving Repr, BEq

/-! ### IR Runtime Values -/

/-- Typed runtime values for the IR stack machine. -/
inductive IRValue where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  | f64 (n : Float)
  deriving Repr, BEq

/-- Default value for an IR type. -/
def IRValue.default : IRType → IRValue
  | .i32 => .i32 0
  | .i64 => .i64 0
  | .f64 => .f64 0.0
  | .ptr => .i32 0  -- ptrs are i32 in Wasm MVP

/-! ### IR Execution State -/

/-- Control label for structured branching in the IR. -/
structure IRLabel where
  name : String
  isLoop : Bool
  onBranch : List IRInstr   -- branch target code (loop head for loops)
  onExit : List IRInstr     -- continuation after this scope
  deriving Repr

/-- Call frame for the IR stack machine.
    Saves the caller's continuation so that function return can restore execution.
    REF: WasmCert-Coq `frame` / Wasm §4.4.6 (activation frames). -/
structure IRFrame where
  locals : Array IRValue
  returnArity : Nat
  /-- Caller's remaining code to resume after return. -/
  savedCode : List IRInstr
  /-- Caller's label stack to restore after return. -/
  savedLabels : List IRLabel
  deriving Repr

/-- IR execution state. -/
structure IRExecState where
  module : IRModule
  stack : List IRValue
  frames : List IRFrame
  labels : List IRLabel
  globals : Array IRValue
  memory : ByteArray
  code : List IRInstr
  trace : List TraceEvent
  deriving Repr

/-! ### Initial State -/

/-- Initialize globals from module declaration. -/
private def initIRGlobals (m : IRModule) : Array IRValue :=
  m.globals.map fun (t, _, _) => IRValue.default t

/-- Initialize linear memory from module memories (first memory only in MVP). -/
private def initIRMemory (m : IRModule) : ByteArray :=
  match m.memories[0]? with
  | some mem => ByteArray.mk (Array.replicate (mem.lim.min * 65536) 0)
  | none => ByteArray.empty

/-- Build the initial execution state for an IR module. -/
def irInitialState (m : IRModule) : IRExecState :=
  let entryCode := match m.startFunc with
    | some idx => [IRInstr.call idx]
    | none => []
  { module := m
    stack := []
    frames := [{ locals := #[], returnArity := 0, savedCode := [], savedLabels := [] }]
    labels := []
    globals := initIRGlobals m
    memory := initIRMemory m
    code := entryCode
    trace := [] }

/-! ### IR Helpers -/

private def irPop1? (stack : List IRValue) : Option (IRValue × List IRValue) :=
  match stack with
  | v :: rest => some (v, rest)
  | [] => none

private def irPop2? (stack : List IRValue) : Option (IRValue × IRValue × List IRValue) :=
  match stack with
  | v1 :: v2 :: rest => some (v1, v2, rest)
  | _ => none

private def irPopN? (stack : List IRValue) (n : Nat) : Option (List IRValue × List IRValue) :=
  if stack.length < n then none
  else some (stack.take n, stack.drop n)

private def irPushTrace (s : IRExecState) (t : TraceEvent) : IRExecState :=
  { s with trace := s.trace ++ [t] }

private def irTrapState (s : IRExecState) (msg : String) : TraceEvent × IRExecState :=
  let s' := irPushTrace { s with code := [] } (.trap msg)
  (.trap msg, s')

private def irBoolToI32 (b : Bool) : IRValue :=
  .i32 (if b then 1 else 0)

/-- Resolve a branch label by name, returning its index in the label stack. -/
private def irFindLabel? (labels : List IRLabel) (name : String) : Option (Nat × IRLabel) :=
  let rec go (ls : List IRLabel) (idx : Nat) : Option (Nat × IRLabel) :=
    match ls with
    | [] => none
    | l :: rest => if l.name == name then some (idx, l) else go rest (idx + 1)
  go labels 0

/-! ### IR Single-Step Function -/

/-- One step of IR execution. Returns `none` when halted (no code, no labels).
    SPEC: Each case mirrors a Wasm instruction adapted for IR's structured control flow. -/
def irStep? (s : IRExecState) : Option (TraceEvent × IRExecState) :=
  match s.code with
  | [] =>
      match s.labels with
      | label :: rest =>
          -- Label scope completed: pop label and continue with onExit code
          some (.silent, irPushTrace { s with code := label.onExit, labels := rest } .silent)
      | [] =>
          -- No code, no labels. Check if we need to return from a function call.
          match s.frames with
          | [] => none  -- no frames at all (shouldn't happen)
          | [_] => none  -- only top-level frame: halted
          | calleeFrame :: callerFrame :: frest =>
              -- Function body completed: pop frame, take returnArity values from stack,
              -- restore caller's saved code/labels. Return values stay on the stack.
              -- REF: WasmCert-Coq r_return / Wasm §4.4.6
              let retVals := s.stack.take calleeFrame.returnArity
              some (.silent, irPushTrace {
                s with
                stack := retVals  -- only return values visible to caller
                frames := callerFrame :: frest
                code := calleeFrame.savedCode
                labels := calleeFrame.savedLabels
              } .silent)
  | instr :: rest =>
      let base := { s with code := rest }
      match instr with
      -- Constants
      | .const_ .i32 v =>
          match v.toNat? with
          | some n => some (.silent, irPushTrace { base with stack := .i32 n.toUInt32 :: base.stack } .silent)
          | none => some (irTrapState base s!"invalid i32 const: {v}")
      | .const_ .i64 v =>
          match v.toNat? with
          | some n => some (.silent, irPushTrace { base with stack := .i64 n.toUInt64 :: base.stack } .silent)
          | none => some (irTrapState base s!"invalid i64 const: {v}")
      | .const_ .f64 v =>
          let f := v.toNat?.map (fun n => Float.ofNat n) |>.getD 0.0
          some (.silent, irPushTrace { base with stack := .f64 f :: base.stack } .silent)
      | .const_ .ptr v =>
          match v.toNat? with
          | some n => some (.silent, irPushTrace { base with stack := .i32 n.toUInt32 :: base.stack } .silent)
          | none => some (irTrapState base s!"invalid ptr const: {v}")

      -- Local variables
      | .localGet idx =>
          match s.frames with
          | [] => some (irTrapState base "no active frame")
          | frame :: _ =>
              match frame.locals[idx]? with
              | some v => some (.silent, irPushTrace { base with stack := v :: base.stack } .silent)
              | none => some (irTrapState base s!"local.get out of bounds: {idx}")
      | .localSet idx =>
          match irPop1? base.stack, s.frames with
          | some (v, stk), frame :: frest =>
              if idx < frame.locals.size then
                let frame' := { frame with locals := frame.locals.set! idx v }
                some (.silent, irPushTrace { base with stack := stk, frames := frame' :: frest } .silent)
              else some (irTrapState base s!"local.set out of bounds: {idx}")
          | _, [] => some (irTrapState base "no active frame for local.set")
          | none, _ => some (irTrapState base "stack underflow in local.set")

      -- Global variables
      | .globalGet idx =>
          match base.globals[idx]? with
          | some v => some (.silent, irPushTrace { base with stack := v :: base.stack } .silent)
          | none => some (irTrapState base s!"global.get out of bounds: {idx}")
      | .globalSet idx =>
          match irPop1? base.stack with
          | some (v, stk) =>
              if idx < base.globals.size then
                some (.silent, irPushTrace { base with stack := stk, globals := base.globals.set! idx v } .silent)
              else some (irTrapState base s!"global.set out of bounds: {idx}")
          | none => some (irTrapState base "stack underflow in global.set")

      -- Binary operations (i32)
      | .binOp .i32 op =>
          match irPop2? base.stack with
          | some (.i32 rhs, .i32 lhs, stk) =>
              -- Trapping ops (div/rem by zero) — REF: Wasm §4.3.2
              match op with
              | "div_s" =>
                  match Numerics.i32DivS? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i32 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | "div_u" =>
                  match Numerics.i32DivU? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i32 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | "rem_s" =>
                  match Numerics.i32RemS? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i32 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | "rem_u" =>
                  match Numerics.i32RemU? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i32 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | _ =>
              -- Total ops (always succeed)
              let result := match op with
                | "add" => IRValue.i32 (Numerics.i32Add lhs rhs)
                | "sub" => IRValue.i32 (Numerics.i32Sub lhs rhs)
                | "mul" => IRValue.i32 (Numerics.i32Mul lhs rhs)
                | "and" => IRValue.i32 (Numerics.i32And lhs rhs)
                | "or"  => IRValue.i32 (Numerics.i32Or lhs rhs)
                | "xor" => IRValue.i32 (Numerics.i32Xor lhs rhs)
                | "shl" => IRValue.i32 (Numerics.i32Shl lhs rhs)
                | "shr_s" => IRValue.i32 (Numerics.i32ShrS lhs rhs)
                | "shr_u" => IRValue.i32 (Numerics.i32ShrU lhs rhs)
                | "rotl" => IRValue.i32 (Numerics.i32Rotl lhs rhs)
                | "rotr" => IRValue.i32 (Numerics.i32Rotr lhs rhs)
                | "eq"  => irBoolToI32 (Numerics.i32Eq lhs rhs)
                | "ne"  => irBoolToI32 (Numerics.i32Ne lhs rhs)
                | "lt_s" => irBoolToI32 (Numerics.i32Lts lhs rhs)
                | "lt_u" => irBoolToI32 (Numerics.i32Ltu lhs rhs)
                | "gt_s" => irBoolToI32 (Numerics.i32Gts lhs rhs)
                | "gt_u" => irBoolToI32 (Numerics.i32Gtu lhs rhs)
                | "le_s" => irBoolToI32 (Numerics.i32Les lhs rhs)
                | "le_u" => irBoolToI32 (Numerics.i32Leu lhs rhs)
                | "ge_s" => irBoolToI32 (Numerics.i32Ges lhs rhs)
                | "ge_u" => irBoolToI32 (Numerics.i32Geu lhs rhs)
                | _ => IRValue.i32 0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          | some _ => some (irTrapState base s!"type mismatch in i32.{op}")
          | none => some (irTrapState base s!"stack underflow in i32.{op}")
      -- Binary operations (i64)
      | .binOp .i64 op =>
          match irPop2? base.stack with
          | some (.i64 rhs, .i64 lhs, stk) =>
              -- Trapping ops (div/rem by zero) — REF: Wasm §4.3.2
              match op with
              | "div_s" =>
                  match Numerics.i64DivS? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i64 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | "div_u" =>
                  match Numerics.i64DivU? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i64 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | "rem_s" =>
                  match Numerics.i64RemS? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i64 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | "rem_u" =>
                  match Numerics.i64RemU? lhs rhs with
                  | some r => some (.silent, irPushTrace { base with stack := .i64 r :: stk } .silent)
                  | none => some (irTrapState base "integer divide by zero")
              | _ =>
              -- Total ops (always succeed)
              let result := match op with
                | "add" => IRValue.i64 (Numerics.i64Add lhs rhs)
                | "sub" => IRValue.i64 (Numerics.i64Sub lhs rhs)
                | "mul" => IRValue.i64 (Numerics.i64Mul lhs rhs)
                | "and" => IRValue.i64 (Numerics.i64And lhs rhs)
                | "or"  => IRValue.i64 (Numerics.i64Or lhs rhs)
                | "xor" => IRValue.i64 (Numerics.i64Xor lhs rhs)
                | "shl" => IRValue.i64 (Numerics.i64Shl lhs rhs)
                | "shr_s" => IRValue.i64 (Numerics.i64ShrS lhs rhs)
                | "shr_u" => IRValue.i64 (Numerics.i64ShrU lhs rhs)
                | "rotl" => IRValue.i64 (Numerics.i64Rotl lhs rhs)
                | "rotr" => IRValue.i64 (Numerics.i64Rotr lhs rhs)
                | "eq"  => irBoolToI32 (Numerics.i64Eq lhs rhs)
                | "ne"  => irBoolToI32 (Numerics.i64Ne lhs rhs)
                | "lt_s" => irBoolToI32 (Numerics.i64Lts lhs rhs)
                | "lt_u" => irBoolToI32 (Numerics.i64Ltu lhs rhs)
                | "gt_s" => irBoolToI32 (Numerics.i64Gts lhs rhs)
                | "gt_u" => irBoolToI32 (Numerics.i64Gtu lhs rhs)
                | "le_s" => irBoolToI32 (Numerics.i64Les lhs rhs)
                | "le_u" => irBoolToI32 (Numerics.i64Leu lhs rhs)
                | "ge_s" => irBoolToI32 (Numerics.i64Ges lhs rhs)
                | "ge_u" => irBoolToI32 (Numerics.i64Geu lhs rhs)
                | _ => IRValue.i64 0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          | some _ => some (irTrapState base s!"type mismatch in i64.{op}")
          | none => some (irTrapState base s!"stack underflow in i64.{op}")
      -- Binary operations (f64)
      | .binOp .f64 op =>
          match irPop2? base.stack with
          | some (.f64 rhs, .f64 lhs, stk) =>
              let result := match op with
                | "add" => IRValue.f64 (Numerics.f64Add lhs rhs)
                | "sub" => IRValue.f64 (Numerics.f64Sub lhs rhs)
                | "mul" => IRValue.f64 (Numerics.f64Mul lhs rhs)
                | "div" => IRValue.f64 (Numerics.f64Div lhs rhs)
                | "min" => IRValue.f64 (Numerics.f64Min lhs rhs)
                | "max" => IRValue.f64 (Numerics.f64Max lhs rhs)
                | "copysign" => IRValue.f64 (Numerics.f64Copysign lhs rhs)
                | "eq"  => irBoolToI32 (Numerics.f64Eq lhs rhs)
                | "ne"  => irBoolToI32 (Numerics.f64Ne lhs rhs)
                | "lt"  => irBoolToI32 (Numerics.f64Lt lhs rhs)
                | "gt"  => irBoolToI32 (Numerics.f64Gt lhs rhs)
                | "le"  => irBoolToI32 (Numerics.f64Le lhs rhs)
                | "ge"  => irBoolToI32 (Numerics.f64Ge lhs rhs)
                | _ => IRValue.f64 0.0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          | some _ => some (irTrapState base s!"type mismatch in f64.{op}")
          | none => some (irTrapState base s!"stack underflow in f64.{op}")
      -- Binary operations (ptr = i32)
      | .binOp .ptr op =>
          match irPop2? base.stack with
          | some (.i32 rhs, .i32 lhs, stk) =>
              let result := match op with
                | "add" => IRValue.i32 (Numerics.i32Add lhs rhs)
                | "sub" => IRValue.i32 (Numerics.i32Sub lhs rhs)
                | _ => IRValue.i32 0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          | some _ => some (irTrapState base s!"type mismatch in ptr.{op}")
          | none => some (irTrapState base s!"stack underflow in ptr.{op}")

      -- Unary operations (i32)
      -- REF: Wasm §4.4.3.1 (i32 unary), §4.4.5.1 (i32.wrap_i64)
      | .unOp .i32 op =>
          match irPop1? base.stack with
          | some (.i32 v, stk) =>
              let result := match op with
                | "eqz" => irBoolToI32 (Numerics.i32Eqz v)
                | "clz" => IRValue.i32 (Numerics.i32Clz v)
                | "ctz" => IRValue.i32 (Numerics.i32Ctz v)
                | "popcnt" => IRValue.i32 (Numerics.i32Popcnt v)
                | _ => IRValue.i32 0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          -- Cross-type: wrap_i64 takes i64 → i32
          | some (.i64 v, stk) =>
              match op with
              | "wrap_i64" => some (.silent, irPushTrace { base with stack := .i32 (Numerics.i32WrapI64 v) :: stk } .silent)
              | _ => some (irTrapState base s!"type mismatch in unary i32.{op} (got i64)")
          | some _ => some (irTrapState base s!"type mismatch in unary i32.{op}")
          | none => some (irTrapState base s!"stack underflow in unary i32.{op}")
      -- Unary operations (i64)
      -- REF: Wasm §4.4.3.1 (i64 unary), §4.4.5.2-3 (extends, reinterpret)
      | .unOp .i64 op =>
          match irPop1? base.stack with
          | some (.i64 v, stk) =>
              let result := match op with
                | "eqz" => irBoolToI32 (Numerics.i64Eqz v)
                | "clz" => IRValue.i64 (Numerics.i64Clz v)
                | "ctz" => IRValue.i64 (Numerics.i64Ctz v)
                | "popcnt" => IRValue.i64 (Numerics.i64Popcnt v)
                | _ => IRValue.i64 0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          -- Cross-type: extend_i32_s/u takes i32 → i64
          | some (.i32 v, stk) =>
              match op with
              | "extend_i32_s" => some (.silent, irPushTrace { base with stack := .i64 (Numerics.i64ExtendI32s v) :: stk } .silent)
              | "extend_i32_u" => some (.silent, irPushTrace { base with stack := .i64 (Numerics.i64ExtendI32u v) :: stk } .silent)
              | _ => some (irTrapState base s!"type mismatch in unary i64.{op} (got i32)")
          -- Cross-type: reinterpret_f64 takes f64 → i64
          | some (.f64 v, stk) =>
              match op with
              | "reinterpret_f64" => some (.silent, irPushTrace { base with stack := .i64 (Numerics.i64ReinterpretF64 v) :: stk } .silent)
              | _ => some (irTrapState base s!"type mismatch in unary i64.{op} (got f64)")
          | none => some (irTrapState base s!"stack underflow in unary i64.{op}")
      -- Unary operations (f64)
      -- REF: Wasm §4.4.3.1 (f64 unary), §4.4.5.4-5 (converts, reinterpret)
      | .unOp .f64 op =>
          match irPop1? base.stack with
          | some (.f64 v, stk) =>
              let result := match op with
                | "abs" => IRValue.f64 (Numerics.f64Abs v)
                | "neg" => IRValue.f64 (Numerics.f64Neg v)
                | "ceil" => IRValue.f64 (Numerics.f64Ceil v)
                | "floor" => IRValue.f64 (Numerics.f64Floor v)
                | "trunc" => IRValue.f64 (Numerics.f64Trunc v)
                | "nearest" => IRValue.f64 (Numerics.f64Nearest v)
                | "sqrt" => IRValue.f64 (Numerics.f64Sqrt v)
                | _ => IRValue.f64 0.0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          -- Cross-type: convert_i32_s/u takes i32 → f64
          | some (.i32 v, stk) =>
              match op with
              | "convert_i32_s" => some (.silent, irPushTrace { base with stack := .f64 (Numerics.f64ConvertI32s v) :: stk } .silent)
              | "convert_i32_u" => some (.silent, irPushTrace { base with stack := .f64 (Numerics.f64ConvertI32u v) :: stk } .silent)
              | _ => some (irTrapState base s!"type mismatch in unary f64.{op} (got i32)")
          -- Cross-type: reinterpret_i64 takes i64 → f64
          | some (.i64 v, stk) =>
              match op with
              | "reinterpret_i64" => some (.silent, irPushTrace { base with stack := .f64 (Numerics.f64ReinterpretI64 v) :: stk } .silent)
              | _ => some (irTrapState base s!"type mismatch in unary f64.{op} (got i64)")
          | none => some (irTrapState base s!"stack underflow in unary f64.{op}")
      -- Unary operations (ptr = i32)
      | .unOp .ptr op =>
          match irPop1? base.stack with
          | some (.i32 v, stk) =>
              let result := match op with
                | "eqz" => irBoolToI32 (Numerics.i32Eqz v)
                | _ => IRValue.i32 0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          | some _ => some (irTrapState base s!"type mismatch in unary ptr.{op}")
          | none => some (irTrapState base s!"stack underflow in unary ptr.{op}")

      -- Memory: load (4-byte little-endian i32)
      | .load _t offset =>
          match irPop1? base.stack with
          | some (.i32 addr, stk) =>
              let byteAddr := addr.toNat + offset
              if byteAddr + 4 ≤ base.memory.size then
                let b0 := base.memory.get! byteAddr
                let b1 := base.memory.get! (byteAddr + 1)
                let b2 := base.memory.get! (byteAddr + 2)
                let b3 := base.memory.get! (byteAddr + 3)
                let val : UInt32 := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
                some (.silent, irPushTrace { base with stack := .i32 val :: stk } .silent)
              else some (irTrapState base s!"memory access out of bounds: {byteAddr}")
          | some _ => some (irTrapState base "type mismatch in load")
          | none => some (irTrapState base "stack underflow in load")
      -- Memory: store (4-byte little-endian i32)
      | .store _t offset =>
          match irPop2? base.stack with
          | some (.i32 val, .i32 addr, stk) =>
              let byteAddr := addr.toNat + offset
              if byteAddr + 4 ≤ base.memory.size then
                let mem := base.memory
                  |>.set! byteAddr (val.toUInt8)
                  |>.set! (byteAddr + 1) ((val >>> 8).toUInt8)
                  |>.set! (byteAddr + 2) ((val >>> 16).toUInt8)
                  |>.set! (byteAddr + 3) ((val >>> 24).toUInt8)
                some (.silent, irPushTrace { base with stack := stk, memory := mem } .silent)
              else some (irTrapState base s!"memory store out of bounds: {byteAddr}")
          | some _ => some (irTrapState base "type mismatch in store")
          | none => some (irTrapState base "stack underflow in store")
      -- Memory: store8
      | .store8 offset =>
          match irPop2? base.stack with
          | some (.i32 val, .i32 addr, stk) =>
              let byteAddr := addr.toNat + offset
              if byteAddr < base.memory.size then
                let mem := base.memory.set! byteAddr val.toUInt8
                some (.silent, irPushTrace { base with stack := stk, memory := mem } .silent)
              else some (irTrapState base s!"memory store8 out of bounds: {byteAddr}")
          | some _ => some (irTrapState base "type mismatch in store8")
          | none => some (irTrapState base "stack underflow in store8")

      -- Control flow: block
      | .block label body =>
          let lbl : IRLabel := {
            name := label, isLoop := false
            onBranch := rest, onExit := rest }
          some (.silent, irPushTrace { base with code := body, labels := lbl :: base.labels } .silent)
      -- Control flow: loop
      | .loop label body =>
          let lbl : IRLabel := {
            name := label, isLoop := true
            onBranch := [IRInstr.loop label body] ++ rest
            onExit := rest }
          some (.silent, irPushTrace { base with code := body, labels := lbl :: base.labels } .silent)
      -- Control flow: if
      | .if_ _result then_ else_ =>
          match irPop1? base.stack with
          | some (.i32 cond, stk) =>
              let branch := if cond != 0 then then_ else else_
              some (.silent, irPushTrace { base with stack := stk, code := branch ++ rest } .silent)
          | some _ => some (irTrapState base "type mismatch in if (expected i32)")
          | none => some (irTrapState base "stack underflow in if")
      -- Control flow: br
      | .br label =>
          match irFindLabel? s.labels label with
          | some (idx, lbl) =>
              let labels' := s.labels.drop (idx + 1)
              some (.silent, irPushTrace { base with code := lbl.onBranch, labels := labels' } .silent)
          | none => some (irTrapState base s!"br: unknown label '{label}'")
      -- Control flow: br_if
      | .brIf label =>
          match irPop1? base.stack with
          | some (.i32 cond, stk) =>
              if cond != 0 then
                match irFindLabel? s.labels label with
                | some (idx, lbl) =>
                    let labels' := s.labels.drop (idx + 1)
                    some (.silent, irPushTrace { base with stack := stk, code := lbl.onBranch, labels := labels' } .silent)
                | none => some (irTrapState base s!"br_if: unknown label '{label}'")
              else
                some (.silent, irPushTrace { base with stack := stk } .silent)
          | some _ => some (irTrapState base "type mismatch in br_if (expected i32)")
          | none => some (irTrapState base "stack underflow in br_if")
      -- Control flow: return
      -- REF: WasmCert-Coq r_return / Wasm §4.4.7.4
      | .return_ =>
          match s.frames with
          | [] => some (irTrapState base "return with no frame")
          | [_] =>
              -- Top-level frame: clear code/labels to halt
              some (.silent, irPushTrace { base with code := [], labels := [] } .silent)
          | calleeFrame :: callerFrame :: frest =>
              -- Pop callee frame, take return values, restore caller context
              let retVals := base.stack.take calleeFrame.returnArity
              some (.silent, irPushTrace {
                base with
                stack := retVals
                frames := callerFrame :: frest
                code := calleeFrame.savedCode
                labels := calleeFrame.savedLabels
              } .silent)
      -- Stack: drop
      | .drop =>
          match irPop1? base.stack with
          | some (_, stk) => some (.silent, irPushTrace { base with stack := stk } .silent)
          | none => some (irTrapState base "stack underflow in drop")
      -- Function call
      -- REF: WasmCert-Coq r_invoke_native / Wasm §4.4.6
      | .call funcIdx =>
          match base.module.functions[funcIdx]? with
          | none => some (irTrapState base s!"call: unknown function {funcIdx}")
          | some fn =>
              let nParams := fn.params.length
              match irPopN? base.stack nParams with
              | none => some (irTrapState base s!"stack underflow in call {funcIdx}")
              | some (args, callerStack) =>
                  let localDefaults := fn.locals.map IRValue.default
                  let calleeLocals := (args ++ localDefaults).toArray
                  let calleeFrame : IRFrame := {
                    locals := calleeLocals
                    returnArity := fn.results.length
                    savedCode := rest          -- caller's remaining code
                    savedLabels := base.labels -- caller's label stack
                  }
                  some (.silent, irPushTrace {
                    base with
                    stack := callerStack  -- caller's stack below return values
                    frames := calleeFrame :: base.frames
                    code := fn.body
                    labels := []  -- callee starts with fresh label stack
                  } .silent)
      -- Indirect call (resolve function index from stack)
      -- REF: WasmCert-Coq r_call_indirect_success / Wasm §4.4.8.7
      | .callIndirect _typeIdx =>
          match irPop1? base.stack with
          | some (.i32 funcIdx, stk) =>
              match base.module.functions[funcIdx.toNat]? with
              | none => some (irTrapState { base with stack := stk } s!"call_indirect: unknown function {funcIdx}")
              | some fn =>
                  let nParams := fn.params.length
                  match irPopN? stk nParams with
                  | none => some (irTrapState { base with stack := stk } s!"stack underflow in call_indirect")
                  | some (args, callerStack) =>
                      let localDefaults := fn.locals.map IRValue.default
                      let calleeLocals := (args ++ localDefaults).toArray
                      let calleeFrame : IRFrame := {
                        locals := calleeLocals
                        returnArity := fn.results.length
                        savedCode := rest
                        savedLabels := base.labels
                      }
                      some (.silent, irPushTrace {
                        base with
                        stack := callerStack
                        frames := calleeFrame :: base.frames
                        code := fn.body
                        labels := []  -- callee starts with fresh label stack
                      } .silent)
          | some _ => some (irTrapState base "type mismatch in call_indirect (expected i32 index)")
          | none => some (irTrapState base "stack underflow in call_indirect")
      -- Memory grow
      | .memoryGrow =>
          match irPop1? base.stack with
          | some (.i32 pages, stk) =>
              let oldPages := base.memory.size / 65536
              let newSize := base.memory.size + pages.toNat * 65536
              if newSize ≤ 65536 * 65536 then
                let grown := ByteArray.mk (base.memory.toList.toArray ++ Array.replicate (pages.toNat * 65536) 0)
                some (.silent, irPushTrace { base with stack := .i32 oldPages.toUInt32 :: stk, memory := grown } .silent)
              else
                some (.silent, irPushTrace { base with stack := .i32 (0xFFFFFFFF : UInt32) :: stk } .silent)
          | some _ => some (irTrapState base "type mismatch in memory.grow")
          | none => some (irTrapState base "stack underflow in memory.grow")

/-! ### IR Inductive Relations -/

/-- Small-step reduction relation induced by `irStep?`. -/
inductive IRStep : IRExecState → TraceEvent → IRExecState → Prop where
  | mk {s : IRExecState} {t : TraceEvent} {s' : IRExecState} :
      irStep? s = some (t, s') →
      IRStep s t s'

/-- Reflexive-transitive closure of IR steps with trace accumulation.
    REF: Mirrors Wasm.Steps and ANF.Steps for proof chain compatibility. -/
inductive IRSteps : IRExecState → List TraceEvent → IRExecState → Prop where
  | refl (s : IRExecState) : IRSteps s [] s
  | tail {s1 s2 s3 : IRExecState} {t : TraceEvent} {ts : List TraceEvent} :
      IRStep s1 t s2 →
      IRSteps s2 ts s3 →
      IRSteps s1 (t :: ts) s3

/-- Behavioral semantics for an IR module.
    A module `m` exhibits behavior `b` when execution from the initial state
    reaches a halted state after producing trace `b`.
    REF: Mirrors Wasm.Behaves for the emit correctness theorem. -/
def IRBehaves (m : IRModule) (b : List TraceEvent) : Prop :=
  ∃ sFinal, IRSteps (irInitialState m) b sFinal ∧ irStep? sFinal = none

/-! ### IR State Classification -/

/-- A state has halted when there is no code left, no labels to pop,
    and only the top-level frame remains (no callers to return to). -/
def IRExecState.halted (s : IRExecState) : Prop :=
  s.code = [] ∧ s.labels = [] ∧ s.frames.length ≤ 1

/-- Halted states have irStep? = none. -/
@[simp]
theorem irStep?_halted {s : IRExecState} (h : s.halted) : irStep? s = none := by
  obtain ⟨hc, hl, hf⟩ := h
  simp [irStep?, hc, hl]
  match s.frames, hf with
  | [], _ => rfl
  | [_], _ => rfl

/-! ### IR Basic Properties -/

/-- IRStep relation is equivalent to irStep? returning some. -/
theorem IRStep_iff (s : IRExecState) (t : TraceEvent) (s' : IRExecState) :
    IRStep s t s' ↔ irStep? s = some (t, s') :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- IR.Step is deterministic. -/
theorem IRStep_deterministic {s : IRExecState} {t1 t2 : TraceEvent} {s1 s2 : IRExecState} :
    IRStep s t1 s1 → IRStep s t2 s2 → t1 = t2 ∧ s1 = s2 := by
  intro ⟨h1⟩ ⟨h2⟩
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2

/-- IR.Steps is transitive. -/
theorem IRSteps_trans {s1 s2 s3 : IRExecState} {t1 t2 : List TraceEvent} :
    IRSteps s1 t1 s2 → IRSteps s2 t2 s3 → IRSteps s1 (t1 ++ t2) s3 := by
  intro h1 h2
  induction h1 with
  | refl _ => exact h2
  | tail hstep _ ih => exact .tail hstep (ih h2)

/-- If a module exhibits behavior b via IRSteps, then IRBehaves holds. -/
theorem IRBehaves_of_Steps {m : IRModule} {sFinal : IRExecState} {b : List TraceEvent}
    (hsteps : IRSteps (irInitialState m) b sFinal)
    (hhalt : irStep? sFinal = none) :
    IRBehaves m b :=
  ⟨sFinal, hsteps, hhalt⟩

/-- IRSteps determinism: if the same start state leads to two halted states, the traces match. -/
theorem IRSteps_deterministic {s : IRExecState} {b1 b2 : List TraceEvent}
    {s1 s2 : IRExecState}
    (h1 : IRSteps s b1 s1) (hhalt1 : irStep? s1 = none)
    (h2 : IRSteps s b2 s2) (hhalt2 : irStep? s2 = none) :
    b1 = b2 ∧ s1 = s2 := by
  induction h1 generalizing b2 s2 with
  | refl _ =>
      cases h2 with
      | refl _ => exact ⟨rfl, rfl⟩
      | tail hstep _ =>
          obtain ⟨h⟩ := hstep
          rw [hhalt1] at h; exact absurd h (by simp)
  | tail hstep1 _ ih =>
      cases h2 with
      | refl _ =>
          obtain ⟨h⟩ := hstep1
          rw [hhalt2] at h; exact absurd h (by simp)
      | tail hstep2 hsteps2' =>
          obtain ⟨h1e⟩ := hstep1
          obtain ⟨h2e⟩ := hstep2
          rw [h1e] at h2e
          simp only [Option.some.injEq, Prod.mk.injEq] at h2e
          obtain ⟨ht, hs⟩ := h2e
          subst ht; subst hs
          have ⟨htl, hsl⟩ := ih hhalt1 hsteps2' hhalt2
          exact ⟨by rw [htl], hsl⟩

/-- IR behavioral semantics is deterministic: a module can only produce one trace. -/
theorem IRBehaves_deterministic {m : IRModule} {b1 b2 : List TraceEvent} :
    IRBehaves m b1 → IRBehaves m b2 → b1 = b2 := by
  intro ⟨s1, hsteps1, hhalt1⟩ ⟨s2, hsteps2, hhalt2⟩
  exact (IRSteps_deterministic hsteps1 hhalt1 hsteps2 hhalt2).1

/-! ### Trace Event Mappings (for proof chain) -/

/-- Map IR trace events to Wasm trace events.
    Used by EmitCorrect to relate IR traces to Wasm traces.
    Observable events (log/error) become silent at the Wasm level
    because they are implemented via host calls (fd_write). -/
def traceToWasm : TraceEvent → Wasm.TraceEvent
  | .silent => .silent
  | .trap msg => .trap msg
  | .log _ => .silent
  | .error _ => .silent

/-- Map a full IR trace to a Wasm trace. -/
def traceListToWasm : List TraceEvent → List Wasm.TraceEvent :=
  List.map traceToWasm

/-! ### @[simp] Equation Lemmas for irStep? -/

/-- irStep? with no code, no labels, and ≤ 1 frame is none (halted). -/
@[simp]
theorem irStep?_nil_nil (s : IRExecState) (h1 : s.code = []) (h2 : s.labels = [])
    (hf : s.frames.length ≤ 1) :
    irStep? s = none := by
  simp [irStep?, h1, h2]
  match s.frames, hf with
  | [], _ => rfl
  | [_], _ => rfl

/-- irStep? with no code but labels pops the label scope. -/
@[simp]
theorem irStep?_nil_label (s : IRExecState) (l : IRLabel) (ls : List IRLabel)
    (h1 : s.code = []) (h2 : s.labels = l :: ls) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, h1, h2]

/-- IRSteps can be extended by one step at the end. -/
theorem IRSteps_snoc {s1 s2 s3 : IRExecState} {ts : List TraceEvent} {t : TraceEvent} :
    IRSteps s1 ts s2 → IRStep s2 t s3 → IRSteps s1 (ts ++ [t]) s3 := by
  intro hsteps hstep
  induction hsteps with
  | refl _ => exact .tail hstep (.refl _)
  | tail h _ ih => exact .tail h (ih hstep)

/-! ### Trace Mapping Lemmas -/

@[simp] theorem traceToWasm_silent : traceToWasm .silent = .silent := rfl
@[simp] theorem traceToWasm_trap (msg : String) : traceToWasm (.trap msg) = .trap msg := rfl
@[simp] theorem traceToWasm_log (s : String) : traceToWasm (.log s) = .silent := rfl
@[simp] theorem traceToWasm_error (s : String) : traceToWasm (.error s) = .silent := rfl

@[simp] theorem traceListToWasm_nil : traceListToWasm [] = [] := rfl
@[simp] theorem traceListToWasm_cons (t : TraceEvent) (ts : List TraceEvent) :
    traceListToWasm (t :: ts) = traceToWasm t :: traceListToWasm ts := rfl

@[simp] theorem traceListToWasm_append (t1 t2 : List TraceEvent) :
    traceListToWasm (t1 ++ t2) = traceListToWasm t1 ++ traceListToWasm t2 := by
  simp [traceListToWasm, List.map_append]

/-! ### observableWasmEvents ∘ traceToWasm composition lemmas -/

/-- observableWasmEvents of a single traceToWasm application. -/
@[simp] theorem observableWasmEvents_traceToWasm_silent :
    Wasm.observableWasmEvents [traceToWasm .silent] = [] := rfl
@[simp] theorem observableWasmEvents_traceToWasm_trap (msg : String) :
    Wasm.observableWasmEvents [traceToWasm (.trap msg)] = [.trap msg] := rfl
@[simp] theorem observableWasmEvents_traceToWasm_log (s : String) :
    Wasm.observableWasmEvents [traceToWasm (.log s)] = [] := rfl
@[simp] theorem observableWasmEvents_traceToWasm_error (s : String) :
    Wasm.observableWasmEvents [traceToWasm (.error s)] = [] := rfl

/-- observableWasmEvents distributes through traceListToWasm. -/
@[simp] theorem observableWasmEvents_traceListToWasm_nil :
    Wasm.observableWasmEvents (traceListToWasm []) = [] := rfl

@[simp] theorem observableWasmEvents_traceListToWasm_cons (t : TraceEvent) (ts : List TraceEvent) :
    Wasm.observableWasmEvents (traceListToWasm (t :: ts)) =
      Wasm.observableWasmEvents [traceToWasm t] ++ Wasm.observableWasmEvents (traceListToWasm ts) := by
  rw [show traceListToWasm (t :: ts) = [traceToWasm t] ++ traceListToWasm ts from rfl]
  exact Wasm.observableWasmEvents_append _ _

/-- observableWasmEvents of traceListToWasm only keeps traps. -/
theorem observableWasmEvents_traceListToWasm (ts : List TraceEvent) :
    Wasm.observableWasmEvents (traceListToWasm ts) =
      (ts.filter (fun t => match t with | .trap _ => true | _ => false)).map traceToWasm := by
  induction ts with
  | nil => simp [traceListToWasm]
  | cons t ts ih =>
    simp only [traceListToWasm, List.map] at ih ⊢
    cases t with
    | silent => simp [traceToWasm, Wasm.observableWasmEvents, List.filter, ih]
    | trap msg => simp [traceToWasm, Wasm.observableWasmEvents, List.filter, ih]
    | log msg => simp [traceToWasm, Wasm.observableWasmEvents, List.filter, ih]
    | error msg => simp [traceToWasm, Wasm.observableWasmEvents, List.filter, ih]

/-! ### Core ↔ IR Trace Event Mappings (for LowerCorrect proof chain)

The lowering pass bridges ANF (which uses Core.TraceEvent) to IR (which uses IR.TraceEvent).
These mappings allow LowerCorrect to relate the two trace types. -/

/-- Map a Core.TraceEvent to an IR.TraceEvent.
    Used by LowerCorrect: ∀ trace, ANF.Behaves s trace → IR.Behaves t (map traceFromCore trace).
    REF: Core.TraceEvent has log/error/silent; IR.TraceEvent adds trap. -/
def traceFromCore : Core.TraceEvent → TraceEvent
  | .log s => .log s
  | .error s => .error s
  | .silent => .silent

/-- Map an IR.TraceEvent back to a Core.TraceEvent (lossy: trap maps to error).
    Used when relating IR traces back to source-level traces. -/
def traceToCore : TraceEvent → Core.TraceEvent
  | .silent => .silent
  | .trap msg => .error msg
  | .log s => .log s
  | .error s => .error s

/-- Map a full Core trace to an IR trace. -/
def traceListFromCore : List Core.TraceEvent → List TraceEvent :=
  List.map traceFromCore

/-- Map a full IR trace to a Core trace (lossy). -/
def traceListToCore : List TraceEvent → List Core.TraceEvent :=
  List.map traceToCore

/-! #### Core ↔ IR Trace Mapping Lemmas -/

@[simp] theorem traceFromCore_silent : traceFromCore .silent = .silent := rfl
@[simp] theorem traceFromCore_log (s : String) : traceFromCore (.log s) = .log s := rfl
@[simp] theorem traceFromCore_error (s : String) : traceFromCore (.error s) = .error s := rfl

@[simp] theorem traceToCore_silent : traceToCore .silent = .silent := rfl
@[simp] theorem traceToCore_trap (msg : String) : traceToCore (.trap msg) = .error msg := rfl
@[simp] theorem traceToCore_log (s : String) : traceToCore (.log s) = .log s := rfl
@[simp] theorem traceToCore_error (s : String) : traceToCore (.error s) = .error s := rfl

@[simp] theorem traceListFromCore_nil : traceListFromCore [] = [] := rfl
@[simp] theorem traceListFromCore_cons (t : Core.TraceEvent) (ts : List Core.TraceEvent) :
    traceListFromCore (t :: ts) = traceFromCore t :: traceListFromCore ts := rfl

@[simp] theorem traceListFromCore_append (t1 t2 : List Core.TraceEvent) :
    traceListFromCore (t1 ++ t2) = traceListFromCore t1 ++ traceListFromCore t2 := by
  simp [traceListFromCore, List.map_append]

@[simp] theorem traceListToCore_nil : traceListToCore [] = [] := rfl
@[simp] theorem traceListToCore_cons (t : TraceEvent) (ts : List TraceEvent) :
    traceListToCore (t :: ts) = traceToCore t :: traceListToCore ts := rfl

@[simp] theorem traceListToCore_append (t1 t2 : List TraceEvent) :
    traceListToCore (t1 ++ t2) = traceListToCore t1 ++ traceListToCore t2 := by
  simp [traceListToCore, List.map_append]

/-- Round-trip: Core → IR → Core is identity (no traps introduced by conversion). -/
@[simp] theorem traceToCore_traceFromCore (t : Core.TraceEvent) :
    traceToCore (traceFromCore t) = t := by
  cases t <;> rfl

/-- Round-trip for lists: Core → IR → Core is identity. -/
@[simp] theorem traceListToCore_traceListFromCore (ts : List Core.TraceEvent) :
    traceListToCore (traceListFromCore ts) = ts := by
  simp only [traceListToCore, traceListFromCore, List.map_map]
  have : (traceToCore ∘ traceFromCore) = id := by
    funext t; exact traceToCore_traceFromCore t
  rw [this, List.map_id]

/-- Composing Core→IR→Wasm trace maps: silent Core events map to silent Wasm events. -/
@[simp] theorem traceToWasm_traceFromCore_silent :
    traceToWasm (traceFromCore .silent) = Wasm.TraceEvent.silent := rfl

@[simp] theorem traceToWasm_traceFromCore_log (s : String) :
    traceToWasm (traceFromCore (.log s)) = Wasm.TraceEvent.silent := rfl

@[simp] theorem traceToWasm_traceFromCore_error (s : String) :
    traceToWasm (traceFromCore (.error s)) = Wasm.TraceEvent.silent := rfl

/-! ### Simulation Framework for Proof Chain

These definitions provide the template for stating semantic preservation theorems.
The proof agent should instantiate these for LowerCorrect and EmitCorrect. -/

/-- A forward simulation: if source and target are related and source steps,
    then target can step with the same trace event and stay related.
    Use this to prove semantic preservation for each compiler pass. -/
structure IRForwardSim {S : Type} (R : S → IRExecState → Prop)
    (step_src : S → Option (TraceEvent × S)) where
  /-- Simulation step: source step implies target step with same event. -/
  step_sim : ∀ (s1 : S) (s2 : IRExecState) (t : TraceEvent) (s1' : S),
    R s1 s2 → step_src s1 = some (t, s1') →
    ∃ s2', irStep? s2 = some (t, s2') ∧ R s1' s2'
  /-- Halting preservation: source halts implies target halts. -/
  halt_sim : ∀ (s1 : S) (s2 : IRExecState),
    R s1 s2 → step_src s1 = none → irStep? s2 = none

/-! ### Additional @[simp] Equation Lemmas for irStep? -/

/-- irStep? for i32.const pushes value onto stack. -/
@[simp]
theorem irStep?_ir_i32Const (s : IRExecState) (v : String) (n : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .i32 v :: rest) (hv : v.toNat? = some n) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hv, irPushTrace]

/-- irStep? for f64.const pushes value onto stack. -/
@[simp]
theorem irStep?_ir_f64Const (s : IRExecState) (v : String) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .f64 v :: rest) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode]

/-- irStep? for local.get with valid index. -/
@[simp]
theorem irStep?_ir_localGet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (frame : IRFrame) (frest : List IRFrame) (val : IRValue)
    (hcode : s.code = IRInstr.localGet idx :: rest)
    (hframes : s.frames = frame :: frest)
    (hlocal : frame.locals[idx]? = some val) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hframes, hlocal, irPushTrace]

/-- irStep? for local.set with valid index and non-empty stack. -/
@[simp]
theorem irStep?_ir_localSet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (frame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = IRInstr.localSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hframes : s.frames = frame :: frest)
    (hbounds : idx < frame.locals.size) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, hframes, irPop1?, irPushTrace, hbounds]

/-- irStep? for global.get with valid index. -/
@[simp]
theorem irStep?_ir_globalGet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (val : IRValue)
    (hcode : s.code = IRInstr.globalGet idx :: rest)
    (hglobal : s.globals[idx]? = some val) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hglobal, irPushTrace]

/-- irStep? for global.set with valid index and non-empty stack. -/
@[simp]
theorem irStep?_ir_globalSet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (hcode : s.code = IRInstr.globalSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hbounds : idx < s.globals.size) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hbounds]

/-- irStep? for drop with non-empty stack. -/
@[simp]
theorem irStep?_ir_drop (s : IRExecState) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (hcode : s.code = IRInstr.drop :: rest)
    (hstack : s.stack = v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for block pushes label and enters body. -/
@[simp]
theorem irStep?_ir_block (s : IRExecState) (label : String) (body rest : List IRInstr)
    (hcode : s.code = IRInstr.block label body :: rest) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, irPushTrace]

/-- irStep? for loop pushes label and enters body. -/
@[simp]
theorem irStep?_ir_loop (s : IRExecState) (label : String) (body rest : List IRInstr)
    (hcode : s.code = IRInstr.loop label body :: rest) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, irPushTrace]

/-- irStep? for if with i32 condition on stack always succeeds. -/
@[simp]
theorem irStep?_ir_if (s : IRExecState) (result : Option IRType)
    (then_ else_ rest : List IRInstr) (cond : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.if_ result then_ else_ :: rest)
    (hstack : s.stack = .i32 cond :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for i32 binop with valid operands always produces a result
    (either a value or a trap for div/rem by zero). -/
@[simp]
theorem irStep?_ir_i32BinOp (s : IRExecState) (op : String) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 op :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp only [irStep?, hcode, hstack, irPop2?]
  -- The outer match on op splits into trapping (div/rem) and total branches
  split <;> (try (split <;> exact ⟨_, _, rfl⟩)) <;> exact ⟨_, _, rfl⟩

/-- irStep? for f64 binop with valid operands always succeeds. -/
@[simp]
theorem irStep?_ir_f64BinOp (s : IRExecState) (op : String) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 op :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace]

/-- irStep? for i32 eqz always succeeds with i32 on stack. -/
@[simp]
theorem irStep?_ir_i32Eqz (s : IRExecState) (rest : List IRInstr)
    (v : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .i32 "eqz" :: rest)
    (hstack : s.stack = .i32 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for call with valid function index and enough stack args. -/
@[simp]
theorem irStep?_ir_call (s : IRExecState) (funcIdx : Nat) (rest : List IRInstr)
    (fn : IRFunc)
    (hcode : s.code = IRInstr.call funcIdx :: rest)
    (hfunc : s.module.functions[funcIdx]? = some fn)
    (hstack : fn.params.length ≤ s.stack.length) :
    ∃ t s', irStep? s = some (t, s') := by
  simp only [irStep?, hcode, hfunc]
  simp only [irPopN?]
  have : ¬ (s.stack.length < fn.params.length) := by omega
  simp [this, irPushTrace]

/-- irStep? for return_ with multiple frames pops the callee frame. -/
@[simp]
theorem irStep?_ir_return_callee (s : IRExecState) (rest : List IRInstr)
    (calleeFrame callerFrame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = IRInstr.return_ :: rest)
    (hframes : s.frames = calleeFrame :: callerFrame :: frest) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hframes, irPushTrace]

/-- irStep? for return_ at top level clears code and labels. -/
@[simp]
theorem irStep?_ir_return_toplevel (s : IRExecState) (rest : List IRInstr)
    (frame : IRFrame)
    (hcode : s.code = IRInstr.return_ :: rest)
    (hframes : s.frames = [frame]) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hframes, irPushTrace]

/-- irStep? for memoryGrow with i32 on stack always succeeds. -/
@[simp]
theorem irStep?_ir_memoryGrow (s : IRExecState) (rest : List IRInstr)
    (pages : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.memoryGrow :: rest)
    (hstack : s.stack = .i32 pages :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]
  split <;> exact ⟨_, _, rfl⟩

/-- irStep? for code exhaustion with multiple frames performs function return. -/
@[simp]
theorem irStep?_ir_frameReturn (s : IRExecState)
    (calleeFrame callerFrame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = []) (hlabels : s.labels = [])
    (hframes : s.frames = calleeFrame :: callerFrame :: frest) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hlabels, hframes, irPushTrace]

/-- irStep? for i64 binop with valid operands always produces a result. -/
@[simp]
theorem irStep?_ir_i64BinOp (s : IRExecState) (op : String) (rest : List IRInstr)
    (lhs rhs : UInt64) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i64 op :: rest)
    (hstack : s.stack = .i64 rhs :: .i64 lhs :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp only [irStep?, hcode, hstack, irPop2?]
  split <;> (try (split <;> exact ⟨_, _, rfl⟩)) <;> exact ⟨_, _, rfl⟩

/-- irStep? for f64 unary op with valid operand always succeeds. -/
@[simp]
theorem irStep?_ir_f64UnOp (s : IRExecState) (op : String) (rest : List IRInstr)
    (v : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .f64 op :: rest)
    (hstack : s.stack = .f64 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for br with a matching label always succeeds. -/
@[simp]
theorem irStep?_ir_br (s : IRExecState) (label : String) (rest : List IRInstr)
    (idx : Nat) (lbl : IRLabel)
    (hcode : s.code = IRInstr.br label :: rest)
    (hfind : irFindLabel? s.labels label = some (idx, lbl)) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hfind, irPushTrace]

/-- irStep? for br_if with i32 condition on stack always succeeds. -/
@[simp]
theorem irStep?_ir_brIf (s : IRExecState) (label : String) (rest : List IRInstr)
    (cond : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.brIf label :: rest)
    (hstack : s.stack = .i32 cond :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp only [irStep?, hcode, hstack, irPop1?]
  split
  · -- cond ≠ 0: branch taken
    split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · -- cond = 0: fall through
    exact ⟨_, _, rfl⟩

/-- irStep? for i32.wrap_i64 with i64 on stack succeeds. -/
@[simp]
theorem irStep?_ir_wrap_i64 (s : IRExecState) (rest : List IRInstr)
    (v : UInt64) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .i32 "wrap_i64" :: rest)
    (hstack : s.stack = .i64 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for i64.extend_i32_u with i32 on stack succeeds. -/
@[simp]
theorem irStep?_ir_extend_i32_u (s : IRExecState) (rest : List IRInstr)
    (v : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .i64 "extend_i32_u" :: rest)
    (hstack : s.stack = .i32 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for i64.extend_i32_s with i32 on stack succeeds. -/
@[simp]
theorem irStep?_ir_extend_i32_s (s : IRExecState) (rest : List IRInstr)
    (v : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .i64 "extend_i32_s" :: rest)
    (hstack : s.stack = .i32 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for i64.reinterpret_f64 with f64 on stack succeeds. -/
@[simp]
theorem irStep?_ir_reinterpret_f64 (s : IRExecState) (rest : List IRInstr)
    (v : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .i64 "reinterpret_f64" :: rest)
    (hstack : s.stack = .f64 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for f64.reinterpret_i64 with i64 on stack succeeds. -/
@[simp]
theorem irStep?_ir_reinterpret_i64 (s : IRExecState) (rest : List IRInstr)
    (v : UInt64) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .f64 "reinterpret_i64" :: rest)
    (hstack : s.stack = .i64 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for f64.convert_i32_s with i32 on stack succeeds. -/
@[simp]
theorem irStep?_ir_convert_i32_s (s : IRExecState) (rest : List IRInstr)
    (v : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .f64 "convert_i32_s" :: rest)
    (hstack : s.stack = .i32 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for f64.convert_i32_u with i32 on stack succeeds. -/
@[simp]
theorem irStep?_ir_convert_i32_u (s : IRExecState) (rest : List IRInstr)
    (v : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .f64 "convert_i32_u" :: rest)
    (hstack : s.stack = .i32 v :: stk) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- irStep? for load with i32 address on stack and in-bounds access succeeds.
    REF: Wasm §4.4.7.1 (memory.load) -/
@[simp]
theorem irStep?_ir_load (s : IRExecState) (rest : List IRInstr) (t : IRType)
    (offset : Nat) (addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.load t offset :: rest)
    (hstack : s.stack = .i32 addr :: stk)
    (hbounds : addr.toNat + offset + 4 ≤ s.memory.size) :
    ∃ te s', irStep? s = some (te, s') := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hbounds]

/-- irStep? for store with i32 value and i32 address on stack and in-bounds succeeds.
    REF: Wasm §4.4.7.2 (memory.store) -/
@[simp]
theorem irStep?_ir_store (s : IRExecState) (rest : List IRInstr) (t : IRType)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.store t offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hbounds : addr.toNat + offset + 4 ≤ s.memory.size) :
    ∃ te s', irStep? s = some (te, s') := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hbounds]

/-- irStep? for store8 with i32 value and i32 address on stack and in-bounds succeeds.
    REF: Wasm §4.4.7.2 (memory.store, 1-byte variant) -/
@[simp]
theorem irStep?_ir_store8 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.store8 offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hbounds : addr.toNat + offset < s.memory.size) :
    ∃ te s', irStep? s = some (te, s') := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hbounds]

/-- irStep? for callIndirect with i32 func index on stack and valid function succeeds.
    REF: Wasm §4.4.8.7 (call_indirect) / WasmCert-Coq r_call_indirect_success -/
@[simp]
theorem irStep?_ir_callIndirect (s : IRExecState) (rest : List IRInstr)
    (typeIdx : Nat) (funcIdx : UInt32) (stk : List IRValue) (fn : IRFunc)
    (hcode : s.code = IRInstr.callIndirect typeIdx :: rest)
    (hstack : s.stack = .i32 funcIdx :: stk)
    (hfunc : s.module.functions[funcIdx.toNat]? = some fn)
    (hargs : fn.params.length ≤ stk.length) :
    ∃ te s', irStep? s = some (te, s') := by
  simp only [irStep?, hcode, hstack, irPop1?, hfunc]
  unfold irPopN?
  have hlt : ¬ (stk.length < fn.params.length) := by omega
  rw [if_neg hlt]
  exact ⟨.silent, _, rfl⟩

/-! ### Exact-Value Equation Lemmas for Forward Simulation

These lemmas give the EXACT resulting state (not just existence), which the proof
agent needs for forward simulation proofs in LowerCorrect and EmitCorrect.
Each returns `irStep? s = some (.silent, s')` with s' fully specified. -/

/-- Exact state after i32.const: pushes i32 value, advances code. -/
theorem irStep?_eq_i32Const (s : IRExecState) (v : String) (n : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .i32 v :: rest) (hv : v.toNat? = some n) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 n.toUInt32 :: s.stack
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hv, irPushTrace]

/-- Exact state after f64.const: pushes f64 value, advances code. -/
theorem irStep?_eq_f64Const (s : IRExecState) (v : String) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .f64 v :: rest) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (v.toNat?.map (fun n => Float.ofNat n) |>.getD 0.0) :: s.stack
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, irPushTrace]

/-- Exact state after local.get: pushes local value, advances code. -/
theorem irStep?_eq_localGet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (frame : IRFrame) (frest : List IRFrame) (val : IRValue)
    (hcode : s.code = IRInstr.localGet idx :: rest)
    (hframes : s.frames = frame :: frest)
    (hlocal : frame.locals[idx]? = some val) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := val :: s.stack
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hframes, hlocal, irPushTrace]

/-- Exact state after local.set: pops stack, updates local, advances code. -/
theorem irStep?_eq_localSet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (frame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = IRInstr.localSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hframes : s.frames = frame :: frest)
    (hbounds : idx < frame.locals.size) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        frames := { frame with locals := frame.locals.set! idx v } :: frest
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, hframes, irPop1?, irPushTrace, hbounds]

/-- Exact state after drop: pops top of stack, advances code. -/
theorem irStep?_eq_drop (s : IRExecState) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (hcode : s.code = IRInstr.drop :: rest)
    (hstack : s.stack = v :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- Exact state after drop with empty stack: traps. -/
theorem irStep?_eq_drop_empty (s : IRExecState) (rest : List IRInstr)
    (hcode : s.code = IRInstr.drop :: rest)
    (hstack : s.stack = []) :
    irStep? s = some (.trap "stack underflow in drop",
      { s with
        code := []
        stack := []
        trace := s.trace ++ [.trap "stack underflow in drop"] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irTrapState, irPushTrace]

/-- Exact state after block: pushes label (onBranch=rest, onExit=rest), enters body. -/
theorem irStep?_eq_block (s : IRExecState) (label : String) (body rest : List IRInstr)
    (hcode : s.code = IRInstr.block label body :: rest) :
    irStep? s = some (.silent,
      { s with
        code := body
        labels := { name := label, onBranch := rest, onExit := rest, isLoop := false } :: s.labels
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, irPushTrace]

/-- Exact state after loop: pushes loop label (onBranch=loop+rest, onExit=rest), enters body. -/
theorem irStep?_eq_loop (s : IRExecState) (label : String) (body rest : List IRInstr)
    (hcode : s.code = IRInstr.loop label body :: rest) :
    irStep? s = some (.silent,
      { s with
        code := body
        labels := { name := label, onBranch := [IRInstr.loop label body] ++ rest,
                     onExit := rest, isLoop := true } :: s.labels
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, irPushTrace]

/-- Exact state after if_ with true condition (cond ≠ 0): enters then branch. -/
theorem irStep?_eq_if_true (s : IRExecState) (result : Option IRType)
    (then_ else_ rest : List IRInstr) (cond : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.if_ result then_ else_ :: rest)
    (hstack : s.stack = .i32 cond :: stk)
    (hcond : cond ≠ 0) :
    irStep? s = some (.silent,
      { s with
        code := then_ ++ rest
        stack := stk
        trace := s.trace ++ [.silent] }) := by
  simp only [irStep?, hcode, hstack, irPop1?, irPushTrace]
  simp [hcond]

/-- Exact state after if_ with false condition (cond = 0): enters else branch. -/
theorem irStep?_eq_if_false (s : IRExecState) (result : Option IRType)
    (then_ else_ rest : List IRInstr) (stk : List IRValue)
    (hcode : s.code = IRInstr.if_ result then_ else_ :: rest)
    (hstack : s.stack = .i32 0 :: stk) :
    irStep? s = some (.silent,
      { s with
        code := else_ ++ rest
        stack := stk
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- Exact state after global.get: pushes global value, advances code. -/
theorem irStep?_eq_globalGet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (val : IRValue)
    (hcode : s.code = IRInstr.globalGet idx :: rest)
    (hglobal : s.globals[idx]? = some val) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := val :: s.stack
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hglobal, irPushTrace]

/-- Exact state after global.set: pops stack, updates global, advances code. -/
theorem irStep?_eq_globalSet (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (hcode : s.code = IRInstr.globalSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hbounds : idx < s.globals.size) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        globals := s.globals.set! idx v
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hbounds]

/-- Exact state after return_ with callee frame: pops frame, restores caller. -/
theorem irStep?_eq_return_callee (s : IRExecState) (rest : List IRInstr)
    (calleeFrame callerFrame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = IRInstr.return_ :: rest)
    (hframes : s.frames = calleeFrame :: callerFrame :: frest) :
    irStep? s = some (.silent,
      { s with
        code := calleeFrame.savedCode
        stack := s.stack.take calleeFrame.returnArity
        frames := callerFrame :: frest
        labels := calleeFrame.savedLabels
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hframes, irPushTrace]

/-- Exact state after label completion: pops label, continues with onExit code. -/
theorem irStep?_eq_labelDone (s : IRExecState) (label : IRLabel) (rest : List IRLabel)
    (hcode : s.code = []) (hlabels : s.labels = label :: rest) :
    irStep? s = some (.silent,
      { s with
        code := label.onExit
        labels := rest
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hlabels, irPushTrace]

/-- Exact state after return_ at top level: clears code and labels to halt. -/
theorem irStep?_eq_return_toplevel (s : IRExecState) (rest : List IRInstr)
    (frame : IRFrame)
    (hcode : s.code = IRInstr.return_ :: rest)
    (hframes : s.frames = [frame]) :
    irStep? s = some (.silent,
      { s with
        code := []
        labels := []
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hframes, irPushTrace]

/-- Exact state after br: jumps to label's onBranch code, pops labels above.
    REF: Wasm §4.4.8.1 (br label) -/
theorem irStep?_eq_br (s : IRExecState) (label : String) (rest : List IRInstr)
    (idx : Nat) (lbl : IRLabel)
    (hcode : s.code = IRInstr.br label :: rest)
    (hfind : irFindLabel? s.labels label = some (idx, lbl)) :
    irStep? s = some (.silent,
      { s with
        code := lbl.onBranch
        labels := s.labels.drop (idx + 1)
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hfind, irPushTrace]

/-- Exact state after br_if with true condition (cond ≠ 0): branches to label. -/
theorem irStep?_eq_brIf_true (s : IRExecState) (label : String) (rest : List IRInstr)
    (cond : UInt32) (stk : List IRValue) (idx : Nat) (lbl : IRLabel)
    (hcode : s.code = IRInstr.brIf label :: rest)
    (hstack : s.stack = .i32 cond :: stk)
    (hcond : cond ≠ 0)
    (hfind : irFindLabel? s.labels label = some (idx, lbl)) :
    irStep? s = some (.silent,
      { s with
        code := lbl.onBranch
        stack := stk
        labels := s.labels.drop (idx + 1)
        trace := s.trace ++ [.silent] }) := by
  simp only [irStep?, hcode, hstack, irPop1?, irPushTrace]
  have : (cond != 0) = true := by simp [bne_iff_ne, hcond]
  simp [this, hfind]

/-- Exact state after br_if with false condition (cond = 0): falls through. -/
theorem irStep?_eq_brIf_false (s : IRExecState) (label : String) (rest : List IRInstr)
    (stk : List IRValue)
    (hcode : s.code = IRInstr.brIf label :: rest)
    (hstack : s.stack = .i32 0 :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace]

/-- Exact state after call: creates callee frame, enters function body.
    REF: Wasm §4.4.6 / WasmCert-Coq r_invoke_native -/
theorem irStep?_eq_call (s : IRExecState) (funcIdx : Nat) (rest : List IRInstr)
    (fn : IRFunc) (args callerStack : List IRValue)
    (hcode : s.code = IRInstr.call funcIdx :: rest)
    (hfunc : s.module.functions[funcIdx]? = some fn)
    (hpopn : irPopN? s.stack fn.params.length = some (args, callerStack)) :
    irStep? s = some (.silent,
      { s with
        stack := callerStack
        frames := { locals := (args ++ fn.locals.map IRValue.default).toArray
                    returnArity := fn.results.length
                    savedCode := rest
                    savedLabels := s.labels } :: s.frames
        code := fn.body
        labels := []
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hfunc, hpopn, irPushTrace]

/-- Exact state after frame return (no code, no labels, multi-frame):
    pops callee frame, restores caller context. -/
theorem irStep?_eq_frameReturn (s : IRExecState)
    (calleeFrame callerFrame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = []) (hlabels : s.labels = [])
    (hframes : s.frames = calleeFrame :: callerFrame :: frest) :
    irStep? s = some (.silent,
      { s with
        stack := s.stack.take calleeFrame.returnArity
        frames := callerFrame :: frest
        code := calleeFrame.savedCode
        labels := calleeFrame.savedLabels
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hlabels, hframes, irPushTrace]

/-! ### IRSteps Composition Helpers -/

/-- Build a single-step IRSteps. -/
theorem IRSteps_single {s1 s2 : IRExecState} {t : TraceEvent}
    (h : IRStep s1 t s2) : IRSteps s1 [t] s2 :=
  .tail h (.refl _)

/-- Compose two single IR steps into a two-step IRSteps. -/
theorem IRSteps_two {s1 s2 s3 : IRExecState} {t1 t2 : TraceEvent}
    (h1 : IRStep s1 t1 s2) (h2 : IRStep s2 t2 s3) : IRSteps s1 [t1, t2] s3 :=
  .tail h1 (IRSteps_single h2)

/-- Compose three single IR steps. -/
theorem IRSteps_three {s1 s2 s3 s4 : IRExecState} {t1 t2 t3 : TraceEvent}
    (h1 : IRStep s1 t1 s2) (h2 : IRStep s2 t2 s3) (h3 : IRStep s3 t3 s4) :
    IRSteps s1 [t1, t2, t3] s4 :=
  .tail h1 (IRSteps_two h2 h3)

/-- Prepend a step to an IRSteps sequence (cons variant of IRSteps_snoc). -/
theorem IRSteps_cons {s1 s2 s3 : IRExecState} {t : TraceEvent} {ts : List TraceEvent}
    (h1 : IRStep s1 t s2) (h2 : IRSteps s2 ts s3) : IRSteps s1 (t :: ts) s3 :=
  .tail h1 h2

/-- Convert irStep? = some to an IRStep proposition. -/
theorem IRStep_of_irStep? {s : IRExecState} {t : TraceEvent} {s' : IRExecState}
    (h : irStep? s = some (t, s')) : IRStep s t s' :=
  (IRStep_iff s t s').mpr h

/-- If irStep? returns some, we can build IRSteps with that single step. -/
theorem IRSteps_of_irStep? {s : IRExecState} {t : TraceEvent} {s' : IRExecState}
    (h : irStep? s = some (t, s')) : IRSteps s [t] s' :=
  IRSteps_single (IRStep_of_irStep? h)

/-! ### Inhabitedness Examples -/

/-- A module with no start function and no functions halts immediately with empty trace. -/
example : IRBehaves
    { functions := #[], memories := #[], globals := #[], exports := #[],
      dataSegments := #[], startFunc := none, tableEntries := #[] }
    [] := by
  refine ⟨_, IRSteps.refl _, ?_⟩
  native_decide

/-- A module calling function 0 (i32.const 42 + return) completes successfully.
    This demonstrates call entry, const push, and return with frame restore. -/
private def exCallModule : IRModule :=
  { functions := #[{
      name := "f"
      params := []
      results := [.i32]
      locals := []
      body := [IRInstr.const_ .i32 "42", IRInstr.return_]
    }]
    memories := #[]
    globals := #[]
    exports := #[]
    dataSegments := #[]
    startFunc := some 0
    tableEntries := #[] }

/-- irStep? on the initial state of exCallModule is not none (not stuck). -/
example : (irStep? (irInitialState exCallModule)).isSome = true := by native_decide

/-- Run IR execution for up to `fuel` steps, collecting the trace. -/
private def irRun (fuel : Nat) (s : IRExecState) : List TraceEvent × IRExecState :=
  match fuel with
  | 0 => ([], s)
  | fuel' + 1 =>
    match irStep? s with
    | none => ([], s)
    | some (t, s') =>
      let (ts, sf) := irRun fuel' s'
      (t :: ts, sf)

/-- The call module halts within 10 steps (call + const + return + frame-pop). -/
example : (irRun 10 (irInitialState exCallModule)).2.code = [] := by native_decide

/-- After execution, the stack has [i32 42] (the returned value). -/
example : (irRun 10 (irInitialState exCallModule)).2.stack == [.i32 42] := by native_decide

/-- A module demonstrating NaN-boxing conversion ops: f64 → i64 → i32 (tag extraction).
    This is the pattern the compiler generates for runtime type checks. -/
private def exNanBoxModule : IRModule :=
  { functions := #[{
      name := "getTag"
      params := [.f64]    -- f64 NaN-boxed value as parameter
      results := [.i32]
      locals := []
      body := [
        IRInstr.localGet 0,                    -- push f64 param
        IRInstr.unOp .i64 "reinterpret_f64",   -- f64 → i64 (raw bits)
        IRInstr.const_ .i64 "281474976710656",  -- 0x0001_0000_0000_0000 (tag mask shift)
        IRInstr.binOp .i64 "and",               -- mask tag bits
        IRInstr.unOp .i32 "wrap_i64",           -- i64 → i32 (take low 32 bits)
        IRInstr.return_
      ]
    }]
    memories := #[]
    globals := #[]
    exports := #[]
    dataSegments := #[]
    startFunc := some 0
    tableEntries := #[] }

/-- The NaN-box module executes without getting stuck. -/
example : (irRun 20 (irInitialState exNanBoxModule)).2.code = [] := by native_decide

/-- A module demonstrating i32 → i64 → f64 conversion (number encoding path).
    This is the pattern for encoding an i32 integer as a NaN-boxed f64. -/
private def exEncodeModule : IRModule :=
  { functions := #[{
      name := "encodeInt"
      params := [.i32]    -- i32 value to encode
      results := [.f64]
      locals := []
      body := [
        IRInstr.localGet 0,                    -- push i32 param
        IRInstr.unOp .i64 "extend_i32_u",      -- i32 → i64 (zero-extend)
        IRInstr.const_ .i64 "281474976710656",  -- tag bits
        IRInstr.binOp .i64 "or",                -- apply tag
        IRInstr.unOp .f64 "reinterpret_i64",    -- i64 → f64 (reinterpret as NaN-boxed)
        IRInstr.return_
      ]
    }]
    memories := #[]
    globals := #[]
    exports := #[]
    dataSegments := #[]
    startFunc := some 0
    tableEntries := #[] }

/-- The encode module executes without getting stuck. -/
example : (irRun 20 (irInitialState exEncodeModule)).2.code = [] := by native_decide

/-- A module with i32 division that does NOT trap (non-zero divisor). -/
private def exDivModule : IRModule :=
  { functions := #[{
      name := "div"
      params := []
      results := [.i32]
      locals := []
      body := [
        IRInstr.const_ .i32 "42",
        IRInstr.const_ .i32 "7",
        IRInstr.binOp .i32 "div_u",
        IRInstr.return_
      ]
    }]
    memories := #[]
    globals := #[]
    exports := #[]
    dataSegments := #[]
    startFunc := some 0
    tableEntries := #[] }

/-- 42 / 7 = 6 -/
example : (irRun 20 (irInitialState exDivModule)).2.stack == [.i32 6] := by native_decide

/-- A module demonstrating memory store + load round-trip.
    Stores i32 value 99 at address 0, then loads it back. -/
private def exMemModule : IRModule :=
  { functions := #[{
      name := "memRoundTrip"
      params := []
      results := [.i32]
      locals := []
      body := [
        IRInstr.const_ .i32 "0",      -- address
        IRInstr.const_ .i32 "99",     -- value to store
        IRInstr.store .i32 0,          -- store 99 at addr 0
        IRInstr.const_ .i32 "0",      -- address to load from
        IRInstr.load .i32 0,           -- load from addr 0
        IRInstr.return_
      ]
    }]
    memories := #[{ lim := { min := 1, max := none } }]  -- 1 page (64KB)
    globals := #[]
    exports := #[]
    dataSegments := #[]
    startFunc := some 0
    tableEntries := #[] }

/-- Memory store + load round-trip: store 99 at offset 0, load back yields 99. -/
example : (irRun 20 (irInitialState exMemModule)).2.stack == [.i32 99] := by native_decide

/-! ### Exact-Value Equation Lemmas for i64/ptr Constants

Lower.lean emits `const_ .i64` and `const_ .ptr` instructions (NaN-boxing).
The proof agent needs exact-value lemmas to build forward simulations. -/

/-- Exact state after i64.const: pushes i64 value, advances code.
    REF: Wasm §4.4.1.1 (i64.const) -/
theorem irStep?_eq_i64Const (s : IRExecState) (v : String) (n : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .i64 v :: rest) (hv : v.toNat? = some n) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i64 n.toUInt64 :: s.stack
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hv, irPushTrace]

/-- Exact state after ptr.const: pushes i32 value (ptr = i32), advances code.
    Lower.lean uses `const_ .ptr` for string references and memory offsets. -/
theorem irStep?_eq_ptrConst (s : IRExecState) (v : String) (n : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .ptr v :: rest) (hv : v.toNat? = some n) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 n.toUInt32 :: s.stack
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hv, irPushTrace]

/-- i64 const @[simp] lemma: with valid numeric string, step always succeeds. -/
@[simp]
theorem irStep?_ir_i64Const (s : IRExecState) (v : String) (n : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .i64 v :: rest) (hv : v.toNat? = some n) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hv, irPushTrace]

/-- ptr const @[simp] lemma: with valid numeric string, step always succeeds. -/
@[simp]
theorem irStep?_ir_ptrConst (s : IRExecState) (v : String) (n : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.const_ .ptr v :: rest) (hv : v.toNat? = some n) :
    ∃ t s', irStep? s = some (t, s') := by
  simp [irStep?, hcode, hv, irPushTrace]

/-! ### Exact-Value Equation Lemmas for Memory Operations

Lower.lean emits load/store/store8 for heap access. The proof agent needs
exact resulting states for forward simulation. -/

/-- Exact state after load: reads 4 bytes little-endian from memory, pushes i32.
    REF: Wasm §4.4.7.1 (memory.load) -/
theorem irStep?_eq_load (s : IRExecState) (rest : List IRInstr) (t : IRType)
    (offset : Nat) (addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.load t offset :: rest)
    (hstack : s.stack = .i32 addr :: stk)
    (hbounds : addr.toNat + offset + 4 ≤ s.memory.size) :
    let byteAddr := addr.toNat + offset
    let b0 := s.memory.get! byteAddr
    let b1 := s.memory.get! (byteAddr + 1)
    let b2 := s.memory.get! (byteAddr + 2)
    let b3 := s.memory.get! (byteAddr + 3)
    let val : UInt32 := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 val :: stk
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hbounds]

/-- Exact state after store: writes 4 bytes little-endian to memory.
    REF: Wasm §4.4.7.2 (memory.store) -/
theorem irStep?_eq_store (s : IRExecState) (rest : List IRInstr) (t : IRType)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.store t offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hbounds : addr.toNat + offset + 4 ≤ s.memory.size) :
    let byteAddr := addr.toNat + offset
    let mem := s.memory
      |>.set! byteAddr (val.toUInt8)
      |>.set! (byteAddr + 1) ((val >>> 8).toUInt8)
      |>.set! (byteAddr + 2) ((val >>> 16).toUInt8)
      |>.set! (byteAddr + 3) ((val >>> 24).toUInt8)
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        memory := mem
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hbounds]

/-- Exact state after store8: writes 1 byte to memory.
    REF: Wasm §4.4.7.2 (memory.store, 1-byte variant) -/
theorem irStep?_eq_store8 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.store8 offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hbounds : addr.toNat + offset < s.memory.size) :
    let byteAddr := addr.toNat + offset
    let mem := s.memory.set! byteAddr val.toUInt8
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        memory := mem
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hbounds]

/-- Exact state after callIndirect: creates callee frame, enters function body.
    REF: Wasm §4.4.8.7 / WasmCert-Coq r_call_indirect_success -/
theorem irStep?_eq_callIndirect (s : IRExecState) (rest : List IRInstr)
    (typeIdx : Nat) (funcIdx : UInt32) (stk : List IRValue) (fn : IRFunc)
    (args callerStack : List IRValue)
    (hcode : s.code = IRInstr.callIndirect typeIdx :: rest)
    (hstack : s.stack = .i32 funcIdx :: stk)
    (hfunc : s.module.functions[funcIdx.toNat]? = some fn)
    (hpopn : irPopN? stk fn.params.length = some (args, callerStack)) :
    irStep? s = some (.silent,
      { s with
        stack := callerStack
        frames := { locals := (args ++ fn.locals.map IRValue.default).toArray
                    returnArity := fn.results.length
                    savedCode := rest
                    savedLabels := s.labels } :: s.frames
        code := fn.body
        labels := []
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, hfunc, hpopn, irPushTrace]

/-- Exact state after memoryGrow (success): grows memory, pushes old page count.
    REF: Wasm §4.4.7.6 (memory.grow) -/
theorem irStep?_eq_memoryGrow_ok (s : IRExecState) (rest : List IRInstr)
    (pages : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.memoryGrow :: rest)
    (hstack : s.stack = .i32 pages :: stk)
    (hsize : s.memory.size + pages.toNat * 65536 ≤ 65536 * 65536) :
    let oldPages := s.memory.size / 65536
    let grown := ByteArray.mk (s.memory.toList.toArray ++ Array.replicate (pages.toNat * 65536) 0)
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 oldPages.toUInt32 :: stk
        memory := grown
        trace := s.trace ++ [.silent] }) := by
  simp only [irStep?, hcode, hstack, irPop1?, irPushTrace]
  have hle : ¬ (65536 * 65536 < s.memory.size + pages.toNat * 65536) := by omega
  simp [hle]

/-! ### IR Step? Equation Lemmas: Binary Operations -/

/-- i32 total binary op equation lemma. Covers add, sub, mul, and, or, xor, shl, shr_u, shr_s, rotl, rotr.
    For trapping ops (div_s, div_u, rem_s, rem_u), use specific lemmas below.
    REF: Wasm §4.3.2 (i32 binop) -/
theorem irStep?_eq_i32BinOp_total (s : IRExecState) (op : String) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 op :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk)
    (hnondiv : op ≠ "div_s" ∧ op ≠ "div_u" ∧ op ≠ "rem_s" ∧ op ≠ "rem_u") :
    ∃ result, irStep? s = some (.silent,
      { s with
        code := rest
        stack := result :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]
  simp only [irPop2?, irPushTrace]
  obtain ⟨hnd1, hnd2, hnd3, hnd4⟩ := hnondiv
  simp only [hnd1, hnd2, hnd3, hnd4]
  exact ⟨_, rfl⟩

/-- i32 add equation lemma. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Add (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "add" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Add lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- i32 sub equation lemma. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Sub (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "sub" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Sub lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- i32 mul equation lemma. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Mul (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "mul" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Mul lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- i32 and equation lemma. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32And (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "and" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32And lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- i32 or equation lemma. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Or (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "or" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Or lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- f64 total binary op equation lemma. Covers add, sub, mul, div, min, max, copysign.
    REF: Wasm §4.3.3 (f64 binop) -/
theorem irStep?_eq_f64BinOp_total (s : IRExecState) (op : String) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 op :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    ∃ result, irStep? s = some (.silent,
      { s with
        code := rest
        stack := result :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]
  simp only [irPop2?, irPushTrace]
  exact ⟨_, rfl⟩

/-- f64 add equation lemma. REF: Wasm §4.3.3 -/
@[simp] theorem irStep?_eq_f64Add (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 "add" :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Add lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- f64 sub equation lemma. REF: Wasm §4.3.3 -/
@[simp] theorem irStep?_eq_f64Sub (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 "sub" :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Sub lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- f64 mul equation lemma. REF: Wasm §4.3.3 -/
@[simp] theorem irStep?_eq_f64Mul (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 "mul" :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Mul lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- f64 div equation lemma. REF: Wasm §4.3.3 -/
@[simp] theorem irStep?_eq_f64Div (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 "div" :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Div lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-! ### IR Step? Equation Lemmas: Unary Operations -/

/-- i32 eqz equation lemma. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Eqz (s : IRExecState) (rest : List IRInstr)
    (v : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .i32 "eqz" :: rest)
    (hstack : s.stack = .i32 v :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.i32Eqz v) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop1?, irPushTrace]

/-- i32 wrap_i64 equation lemma (cross-type unary). REF: Wasm §4.3.4 -/
@[simp] theorem irStep?_eq_i32WrapI64 (s : IRExecState) (rest : List IRInstr)
    (v : UInt64) (stk : List IRValue)
    (hcode : s.code = IRInstr.unOp .i32 "wrap_i64" :: rest)
    (hstack : s.stack = .i64 v :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32WrapI64 v) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop1?, irPushTrace]

/-! ### IR Step? Equation Lemmas: Comparison Operations -/

/-- f64 comparison ops produce i32 results. REF: Wasm §4.3.3 -/
@[simp] theorem irStep?_eq_f64Eq (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 "eq" :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.f64Eq lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

@[simp] theorem irStep?_eq_f64Lt (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 "lt" :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.f64Lt lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

@[simp] theorem irStep?_eq_f64Le (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : Float) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .f64 "le" :: rest)
    (hstack : s.stack = .f64 rhs :: .f64 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.f64Le lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-! ### IR Step? Equation Lemmas: i32 Comparison Operations -/

/-- i32 eq comparison. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Eq (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "eq" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.i32Eq lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- i32 ne comparison. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Ne (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "ne" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.i32Ne lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- i32 lt_s comparison. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Lts (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "lt_s" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.i32Lts lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-- i32 gt_s comparison. REF: Wasm §4.3.2 -/
@[simp] theorem irStep?_eq_i32Gts (s : IRExecState) (rest : List IRInstr)
    (lhs rhs : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.binOp .i32 "gt_s" :: rest)
    (hstack : s.stack = .i32 rhs :: .i32 lhs :: stk) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := irBoolToI32 (Numerics.i32Gts lhs rhs) :: stk
        trace := s.trace ++ [.silent] }) := by
  unfold irStep?; rw [hcode, hstack]; simp [irPop2?, irPushTrace]

/-! ### IR Step? Totality (Progress Theorem)

Key property for the proof chain: every non-halted IR state can step.
This is the IR-level analogue of Wasm type soundness. -/

/-- Every IR state with non-empty code can take a step.
    Every instruction in irStep? either executes successfully or produces a trap;
    no instruction path returns none. This is the fundamental progress property.
    SPEC: Wasm §4 — every well-formed instruction reduces or traps. -/
theorem irStep?_code_nonempty (s : IRExecState) (instr : IRInstr) (rest : List IRInstr)
    (hc : s.code = instr :: rest) :
    ∃ t s', irStep? s = some (t, s') := by
  -- irStep? always returns some when code is non-empty: every instruction
  -- either computes a value (pushTrace) or produces a trap (trapState).
  -- Both are `some`. The only `none` paths are when code=[] ∧ labels=[] ∧ frames≤1.
  unfold irStep?
  rw [hc]
  cases instr <;> simp_all only [] <;> (
    first
    | exact ⟨_, _, rfl⟩
    | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> (first | exact ⟨_, _, rfl⟩ | (split <;> exact ⟨_, _, rfl⟩))))))))))))))))))

/-- Every IR state is either halted or can take a step (full progress theorem). -/
theorem irStep?_progress (s : IRExecState) :
    s.halted ∨ ∃ t s', irStep? s = some (t, s') := by
  match hc : s.code with
  | instr :: rest => exact Or.inr (irStep?_code_nonempty s instr rest hc)
  | [] =>
    match hl : s.labels with
    | label :: lrest =>
      right; simp [irStep?, hc, hl, irPushTrace]
    | [] =>
      match hf : s.frames with
      | [] => left; exact ⟨hc, hl, by simp [hf]⟩
      | [_] => left; exact ⟨hc, hl, by simp [hf]⟩
      | _ :: _ :: _ =>
        right; simp [irStep?, hc, hl, hf, irPushTrace]

/-- Corollary: irStep? returns none if and only if the state is halted. -/
theorem irStep?_none_iff_halted (s : IRExecState) :
    irStep? s = none ↔ s.halted := by
  constructor
  · intro h
    rcases irStep?_progress s with hh | ⟨t, s', hs⟩
    · exact hh
    · rw [h] at hs; exact absurd hs (by simp)
  · intro h; exact irStep?_halted h

/-! ### Forward Simulation ⟹ Behavioral Preservation

The key metatheorem: if an `IRForwardSim` instance exists between a source semantics
and the IR target, then behavioral preservation follows. This directly enables the
proof agent to prove `lower_behavioral_correct` and `emit_behavioral_correct`. -/

/-- Multi-step execution of a deterministic step function. -/
inductive StepStar {S : Type} (step : S → Option (TraceEvent × S)) : S → List TraceEvent → S → Prop where
  | refl (s : S) : StepStar step s [] s
  | step {s s' s'' : S} {t : TraceEvent} {ts : List TraceEvent} :
      step s = some (t, s') → StepStar step s' ts s'' → StepStar step s (t :: ts) s''

/-- A deterministic source semantics behaves with trace `ts` when it runs from initial
    state to a halted state producing exactly `ts`. -/
def DetBehaves {S : Type} (step : S → Option (TraceEvent × S)) (init : S) (ts : List TraceEvent) : Prop :=
  ∃ final, StepStar step init ts final ∧ step final = none

/-- Helper: forward simulation lifts a single source step to a single IR step. -/
private theorem IRForwardSim_step_one {S : Type} {R : S → IRExecState → Prop}
    {step_src : S → Option (TraceEvent × S)}
    (sim : IRForwardSim R step_src)
    {s1 : S} {s2 : IRExecState} {t : TraceEvent} {s1' : S}
    (hR : R s1 s2)
    (hstep : step_src s1 = some (t, s1')) :
    ∃ s2', IRStep s2 t s2' ∧ R s1' s2' := by
  obtain ⟨s2', h2, hR'⟩ := sim.step_sim s1 s2 t s1' hR hstep
  exact ⟨s2', ⟨⟨h2⟩, hR'⟩⟩

/-- Forward simulation lifts multi-step source execution to multi-step IR execution.
    If we have a forward simulation R and the source takes multiple steps producing
    trace `ts`, then the IR target takes matching steps producing the same trace `ts`.
    This is proved by induction on the number of source steps. -/
theorem IRForwardSim_steps {S : Type} {R : S → IRExecState → Prop}
    {step_src : S → Option (TraceEvent × S)}
    (sim : IRForwardSim R step_src)
    {s1_init : S} {s2_init : IRExecState}
    {ts : List TraceEvent} {s1_final : S}
    (hR_init : R s1_init s2_init)
    (hExec : StepStar step_src s1_init ts s1_final) :
    ∃ s2_final, IRSteps s2_init ts s2_final ∧ R s1_final s2_final := by
  induction hExec generalizing s2_init with
  | refl =>
    exact ⟨s2_init, IRSteps.refl _, hR_init⟩
  | step hstep _hrest ih =>
    obtain ⟨s2_mid, hIRstep, hR_mid⟩ := IRForwardSim_step_one sim hR_init hstep
    obtain ⟨s2_final, hIRsteps, hR_final⟩ := ih hR_mid
    exact ⟨s2_final, IRSteps.tail hIRstep hIRsteps, hR_final⟩

/-- THE KEY THEOREM: Forward simulation lifts behavioral preservation.
    Given:
    - A forward simulation R between source and IR
    - Initial states related by R
    - Source behaves with trace `ts`
    Then: IR behaves with trace `ts`.

    This is the standard compiler correctness metatheorem that the proof agent
    should instantiate for `lower_behavioral_correct`. -/
theorem IRForwardSim_behavioral {S : Type} {R : S → IRExecState → Prop}
    {step_src : S → Option (TraceEvent × S)}
    (sim : IRForwardSim R step_src)
    {s_init : S} {ir_init : IRExecState}
    (hR : R s_init ir_init)
    {ts : List TraceEvent}
    (hBehaves : DetBehaves step_src s_init ts) :
    ∃ ir_final, IRSteps ir_init ts ir_final ∧ irStep? ir_final = none := by
  obtain ⟨s_final, hSteps, hHalt⟩ := hBehaves
  -- First, lift multi-step execution preserving R
  have hLift : ∃ ir_final, IRSteps ir_init ts ir_final ∧ R s_final ir_final := by
    clear hHalt
    induction hSteps generalizing ir_init with
    | refl _ =>
      exact ⟨ir_init, IRSteps.refl _, hR⟩
    | step hstep _ ih =>
      obtain ⟨ir_mid, hIR_step, hR_mid⟩ := IRForwardSim_step_one sim hR hstep
      obtain ⟨ir_final, hIR_rest, hR_final⟩ := ih hR_mid
      exact ⟨ir_final, IRSteps.tail hIR_step hIR_rest, hR_final⟩
  -- Then use halt preservation
  obtain ⟨ir_final, hIRSteps, hR_final⟩ := hLift
  exact ⟨ir_final, hIRSteps, sim.halt_sim s_final ir_final hR_final hHalt⟩

/-- StepStar is equivalent to the ANF.Steps relation when the step function is ANF.step?.
    This bridges the ANF.Behaves definition (which uses ANF.Steps) to the DetBehaves
    definition (which uses StepStar). -/
theorem StepStar_of_Steps_generic {S : Type} {step : S → Option (TraceEvent × S)}
    {stepRel : S → TraceEvent → S → Prop}
    (step_iff : ∀ s t s', stepRel s t s' ↔ step s = some (t, s'))
    {stepsRel : S → List TraceEvent → S → Prop}
    {s_init s_final : S} {ts : List TraceEvent}
    (_hRefl : ∀ s, stepsRel s [] s)
    (_hTail : ∀ s1 t s2 ts s3, stepRel s1 t s2 → stepsRel s2 ts s3 → stepsRel s1 (t :: ts) s3)
    -- Induction principle for the stepsRel relation (matches the inductive structure)
    (hElim : ∀ {P : S → List TraceEvent → S → Prop},
      (∀ s, P s [] s) →
      (∀ s1 t s2 ts s3, stepRel s1 t s2 → stepsRel s2 ts s3 → P s2 ts s3 → P s1 (t :: ts) s3) →
      stepsRel s_init ts s_final → P s_init ts s_final)
    (hSteps : stepsRel s_init ts s_final) :
    StepStar step s_init ts s_final :=
  hElim (P := fun s ts s' => StepStar step s ts s')
    (fun s => StepStar.refl s)
    (fun s1 t s2 _ts _s3 hStep _hSteps' ih =>
      StepStar.step ((step_iff s1 t s2).mp hStep) ih)
    hSteps

/-! ### Wasm-Level Forward Simulation (for EmitCorrect)

Parallel framework for the emit pass: IR.IRStep → Wasm.Step correspondence. -/

/-- A forward simulation relating IR execution to Wasm execution.
    The emit pass produces Wasm AST from IR, so we need to show that
    each IR step corresponds to one or more Wasm steps. -/
structure WasmForwardSim (R : IRExecState → ExecState → Prop) where
  /-- Simulation step: IR step implies Wasm step(s) with mapped trace event. -/
  step_sim : ∀ (s1 : IRExecState) (s2 : ExecState) (t : TraceEvent) (s1' : IRExecState),
    R s1 s2 → irStep? s1 = some (t, s1') →
    ∃ s2', step? s2 = some (traceToWasm t, s2') ∧ R s1' s2'
  /-- Halting preservation: IR halts implies Wasm halts. -/
  halt_sim : ∀ (s1 : IRExecState) (s2 : ExecState),
    R s1 s2 → irStep? s1 = none → step? s2 = none

/-- THE KEY THEOREM for emit: Forward simulation lifts behavioral preservation
    from IR to Wasm. Given a WasmForwardSim relating IR and Wasm execution,
    if IR behaves with trace `ts`, then Wasm behaves with trace `traceListToWasm ts`. -/
theorem WasmForwardSim_behavioral (R : IRExecState → ExecState → Prop)
    (sim : WasmForwardSim R)
    {ir_init : IRExecState} {w_init : ExecState}
    (hR : R ir_init w_init)
    {ts : List TraceEvent}
    (hBehaves : ∃ ir_final, IRSteps ir_init ts ir_final ∧ irStep? ir_final = none) :
    ∃ w_final, Steps w_init (traceListToWasm ts) w_final ∧ step? w_final = none := by
  obtain ⟨ir_final, hIRSteps, hIRHalt⟩ := hBehaves
  -- Suffices: lift from any related pair, not just the initial one
  suffices h : ∀ (ir1 : IRExecState) (w1 : ExecState) (ts : List TraceEvent)
      (ir2 : IRExecState),
      R ir1 w1 → IRSteps ir1 ts ir2 → irStep? ir2 = none →
      ∃ w_final, Steps w1 (traceListToWasm ts) w_final ∧ step? w_final = none from
    h ir_init w_init ts ir_final hR hIRSteps hIRHalt
  intro ir1 w1 ts ir2 hR' hSteps hHalt
  induction hSteps generalizing w1 with
  | refl _ =>
    exact ⟨w1, Steps.refl w1, sim.halt_sim _ _ hR' hHalt⟩
  | @tail s1 s2 s3 t ts' hIRStep _hIRRest ih =>
    obtain ⟨hirEq⟩ := hIRStep
    obtain ⟨w_mid, hwStep, hR_mid⟩ := sim.step_sim _ _ _ _ hR' hirEq
    obtain ⟨w_final, hwRest, hwHalt⟩ := ih w_mid hR_mid hHalt
    exact ⟨w_final, Steps.tail (Step.mk hwStep) hwRest, hwHalt⟩

/-- Convenience: combining IRForwardSim_behavioral and WasmForwardSim_behavioral
    gives end-to-end ANF → Wasm behavioral preservation. The proof agent can chain:
    1. Construct IRForwardSim for lower (ANF.step? → irStep?)
    2. Use IRForwardSim_behavioral to get IRBehaves
    3. Construct WasmForwardSim for emit (irStep? → Wasm.step?)
    4. Use WasmForwardSim_behavioral to get Wasm.Behaves -/
theorem behavioral_chain {S : Type}
    {R_lower : S → IRExecState → Prop}
    {step_src : S → Option (TraceEvent × S)}
    (sim_lower : IRForwardSim R_lower step_src)
    {R_emit : IRExecState → ExecState → Prop}
    (sim_emit : WasmForwardSim R_emit)
    {s_init : S} {ir_init : IRExecState} {w_init : ExecState}
    (hR_lower : R_lower s_init ir_init)
    (hR_emit : R_emit ir_init w_init)
    {ts : List TraceEvent}
    (hBehaves : DetBehaves step_src s_init ts) :
    ∃ w_final, Steps w_init (traceListToWasm ts) w_final ∧ step? w_final = none := by
  have hIR := IRForwardSim_behavioral sim_lower hR_lower hBehaves
  exact WasmForwardSim_behavioral R_emit sim_emit hR_emit hIR

/-! ### ANF → IR Forward Simulation (for LowerCorrect)

The lowering pass compiles ANF.State to IR instructions. To prove behavioral
preservation, we define:
1. A wrapped step function that maps ANF's Core.TraceEvent to IR.TraceEvent
2. A state relation between ANF.State and IRExecState
3. The forward simulation instance

The proof agent can then use `IRForwardSim_behavioral` to prove `lower_behavioral_correct`. -/

/-- Wrap ANF.step? to produce IR.TraceEvent instead of Core.TraceEvent.
    This allows us to use the generic IRForwardSim framework which expects
    a step function producing IR.TraceEvent. -/
def anfStepMapped (s : ANF.State) : Option (TraceEvent × ANF.State) :=
  match ANF.step? s with
  | none => none
  | some (t, s') => some (traceFromCore t, s')

/-- anfStepMapped returns none iff ANF.step? returns none. -/
@[simp] theorem anfStepMapped_none_iff (s : ANF.State) :
    anfStepMapped s = none ↔ ANF.step? s = none := by
  simp [anfStepMapped]
  split <;> simp_all

/-- anfStepMapped preserves the step structure with mapped trace events. -/
theorem anfStepMapped_some (s s' : ANF.State) (t : Core.TraceEvent)
    (h : ANF.step? s = some (t, s')) :
    anfStepMapped s = some (traceFromCore t, s') := by
  simp [anfStepMapped, h]

/-- State relation for ANF → IR lowering simulation (deprecated, use LowerSimRel).
    Relates an ANF state to the corresponding IR execution state produced
    by lowering the program and executing to the matching point.
    REF: This is the key invariant that the lowering pass must maintain. -/
def LowerRel (prog : ANF.Program) (irmod : IRModule) (s : ANF.State) (ir : IRExecState) : Prop :=
  Wasm.lower prog = .ok irmod ∧
  ir.trace = s.trace.map traceFromCore

/-! ### Concrete Simulation Relations

The forward simulation theorems require concrete state relations.
`LowerSimRel` relates ANF states to IR states during lowering.
`EmitSimRel` relates IR states to Wasm states during emit.

Key invariants maintained by each relation:
- **Module identity**: the target module is the result of the compilation pass.
- **Code correspondence**: the target's remaining code corresponds to the
  compiled form of the source's remaining expression/instructions.
- **Data correspondence**: locals/stack/memory encode the source's env/heap.
- **Trace correspondence**: the accumulated traces are related by the event mapping.

The step_sim and halt_sim proofs require case analysis on every source step,
showing the target takes a matching step. These are sorry'd for the proof agent. -/

/-! ### Observable Events (IR level) -/

/-- Observable events: filter out `.silent` from an IR trace. -/
def observableEvents : List TraceEvent → List TraceEvent
  | [] => []
  | .silent :: ts => observableEvents ts
  | t :: ts => t :: observableEvents ts

@[simp] theorem observableEvents_nil : observableEvents ([] : List TraceEvent) = [] := rfl

@[simp] theorem observableEvents_cons_silent (ts : List TraceEvent) :
    observableEvents (.silent :: ts) = observableEvents ts := rfl

@[simp] theorem observableEvents_cons_log (s : String) (ts : List TraceEvent) :
    observableEvents (.log s :: ts) = .log s :: observableEvents ts := rfl

@[simp] theorem observableEvents_cons_error (s : String) (ts : List TraceEvent) :
    observableEvents (.error s :: ts) = .error s :: observableEvents ts := rfl

@[simp] theorem observableEvents_cons_trap (s : String) (ts : List TraceEvent) :
    observableEvents (.trap s :: ts) = .trap s :: observableEvents ts := rfl

/-- Observable events distributes over append. -/
@[simp] theorem observableEvents_append (ts1 ts2 : List TraceEvent) :
    observableEvents (ts1 ++ ts2) = observableEvents ts1 ++ observableEvents ts2 := by
  induction ts1 with
  | nil => simp [observableEvents]
  | cons t ts1 ih =>
    cases t with
    | silent => simp [observableEvents, ih]
    | trap msg => simp [observableEvents, ih]
    | log msg => simp [observableEvents, ih]
    | error msg => simp [observableEvents, ih]

/-! ### Simulation Relations -/

/-- Abstract code correspondence: the IR code is the lowered form of the ANF expression.
    Since `lowerExpr` in Lower.lean is `private partial`, we cannot reference it directly.
    Instead, this inductive captures what the lowered code looks like for each ANF form.
    Each constructor says: "if the ANF expression is X, the IR code has shape Y."
    REF: Each case corresponds to a clause in Lower.lean's lowerExpr. -/
inductive LowerCodeCorr : ANF.Expr → List IRInstr → Prop where
  /-- A literal trivial lowers to a const push. -/
  | lit_null : LowerCodeCorr (.trivial .litNull) [.const_ .i32 "0"]
  | lit_undefined : LowerCodeCorr (.trivial .litUndefined) [.const_ .i32 "0"]
  | lit_bool_true : LowerCodeCorr (.trivial (.litBool true)) [.const_ .i32 "1"]
  | lit_bool_false : LowerCodeCorr (.trivial (.litBool false)) [.const_ .i32 "0"]
  | lit_num (n : Float) (s : String) : LowerCodeCorr (.trivial (.litNum n)) [.const_ .f64 s]
  | lit_str (s : String) : ∀ instrs, LowerCodeCorr (.trivial (.litStr s)) instrs
  | lit_object (addr : Nat) (s : String) : LowerCodeCorr (.trivial (.litObject addr)) [.const_ .i32 s]
  | lit_closure (fi : ANF.FuncIdx) (ep : Nat) (instrs : List IRInstr) :
      LowerCodeCorr (.trivial (.litClosure fi ep)) instrs
  /-- Post-step halted: a non-variable trivial with empty code (both sides halted).
      This arises after a var lookup or other step resolves to a literal value. -/
  | value_done (t : ANF.Trivial) (ht : ∀ name, t ≠ .var name) :
      LowerCodeCorr (.trivial t) []
  /-- A variable reference lowers to a local.get. -/
  | var (name : ANF.VarName) (idx : Nat) :
      LowerCodeCorr (.trivial (.var name)) [.localGet idx]
  /-- A let-binding lowers to: [lowered rhs] ++ [localSet idx] ++ [lowered body]. -/
  | let_ (name : ANF.VarName) (rhs : ANF.ComplexExpr) (body : ANF.Expr)
      (rhsCode bodyCode : List IRInstr) (idx : Nat) :
      LowerCodeCorr body bodyCode →
      LowerCodeCorr (.«let» name rhs body) (rhsCode ++ [.localSet idx] ++ bodyCode)
  /-- A seq lowers to: [lowered a] ++ [drop] ++ [lowered b]. -/
  | seq (a b : ANF.Expr) (aCode bCode : List IRInstr) :
      LowerCodeCorr a aCode → LowerCodeCorr b bCode →
      LowerCodeCorr (.seq a b) (aCode ++ [.drop] ++ bCode)
  /-- An if lowers to: [lowered cond] ++ [if_ ...]. -/
  | if_ (cond : ANF.Trivial) (then_ else_ : ANF.Expr)
      (condCode thenCode elseCode : List IRInstr) :
      LowerCodeCorr then_ thenCode → LowerCodeCorr else_ elseCode →
      LowerCodeCorr (.«if» cond then_ else_) (condCode ++ [.if_ none thenCode elseCode])
  /-- A while_ lowers to block+loop: [block exitLbl [loop loopLbl (condCode ++ [call truthy, eqz, brIf exit] ++ bodyCode ++ [drop, br loop])]] ++ [undefinedConst].
      REF: Lower.lean lowerWhile, lines 519-526. -/
  | while_ (cond body : ANF.Expr) (condCode bodyCode : List IRInstr)
      (exitLbl loopLbl : String) (undefinedConst : IRInstr) :
      LowerCodeCorr cond condCode → LowerCodeCorr body bodyCode →
      LowerCodeCorr (.while_ cond body)
        ([.block exitLbl [.loop loopLbl
            (condCode ++ [.call RuntimeIdx.truthy, .unOp .i32 "eqz", .brIf exitLbl] ++
             bodyCode ++ [.drop, .br loopLbl])]] ++ [undefinedConst])
  /-- throw lowers to: argCode ++ [call throwOp] ++ transfer.
      transfer is [br exnLabel] or [return_] depending on exception context.
      REF: Lower.lean lines 446-452. -/
  | throw_br (arg : ANF.Trivial) (argCode : List IRInstr) (lbl : String) :
      LowerCodeCorr (.throw arg) (argCode ++ [.call RuntimeIdx.throwOp, .br lbl])
  | throw_ret (arg : ANF.Trivial) (argCode : List IRInstr) :
      LowerCodeCorr (.throw arg) (argCode ++ [.call RuntimeIdx.throwOp, .return_])
  /-- tryCatch lowers to a block structure. -/
  | tryCatch (body : ANF.Expr) (cp : ANF.VarName) (cb : ANF.Expr)
      (fin : Option ANF.Expr) (instrs : List IRInstr) :
      LowerCodeCorr (.tryCatch body cp cb fin) instrs
  /-- return with value lowers to: valueCode ++ [return_].
      REF: Lower.lean lines 466-471. -/
  | return_some (arg : ANF.Trivial) (argCode : List IRInstr) :
      LowerCodeCorr (.«return» (some arg)) (argCode ++ [.return_])
  /-- return without value lowers to: [return_].
      REF: Lower.lean lines 466-471. -/
  | return_none :
      LowerCodeCorr (.«return» none) [.return_]
  /-- yield lowers to some instruction sequence. -/
  | yield (arg : Option ANF.Trivial) (delegate : Bool) (instrs : List IRInstr) :
      LowerCodeCorr (.yield arg delegate) instrs
  /-- await lowers to some instruction sequence. -/
  | await (arg : ANF.Trivial) (instrs : List IRInstr) :
      LowerCodeCorr (.await arg) instrs
  /-- labeled lowers to a block structure. -/
  | labeled (label : String) (body : ANF.Expr) (instrs : List IRInstr) :
      LowerCodeCorr (.labeled label body) instrs
  /-- break lowers to: [br target].
      REF: Lower.lean lines 497-500. -/
  | break_ (label : Option String) (target : Option String) :
      LowerCodeCorr (.«break» label) [.br target]
  /-- continue lowers to: [br target].
      REF: Lower.lean lines 501-504. -/
  | continue_ (label : Option String) (target : Option String) :
      LowerCodeCorr (.«continue» label) [.br target]

structure LowerSimRel (prog : ANF.Program) (irmod : IRModule)
    (s : ANF.State) (ir : IRExecState) : Prop where
  /- The IR module is the result of lowering. -/
  hlower : Wasm.lower prog = .ok irmod
  /- Module identity. -/
  hmod : ir.module = irmod
  /- Code correspondence: the IR code is the lowered form of the ANF expression.
     This is the key invariant that connects what the ANF is about to execute
     to what the IR is about to execute. Without this, step_sim is unprovable. -/
  hcode : LowerCodeCorr s.expr ir.code
  /- Halt correspondence. -/
  hhalt : anfStepMapped s = none → ir.halted
  /- Frame non-emptiness: the IR always has at least one frame. -/
  hframes : ir.frames ≠ []
  /- Environment correspondence: each ANF variable maps to an IR local.
     The idx corresponds to the local index the compiler assigned to the variable. -/
  henv : ∀ name v, s.env.lookup name = some v →
    ∃ (idx : Nat) (val : IRValue), (Option.bind ir.frames.head? (fun f => f.locals[idx]?)) = some val
  /- Variable correspondence: when the ANF expression is a variable reference
     and the IR code is a localGet, the variable is in scope and the local is valid.
     This connects the code correspondence (which index) to the env (which value).
     After a var step, both sides are literal/empty, so this holds vacuously. -/
  hvar : ∀ name idx, s.expr = .trivial (.var name) → ir.code = [IRInstr.localGet idx] →
    (∃ v, s.env.lookup name = some v) ∧
    ∃ val, (Option.bind ir.frames.head? (fun f => f.locals[idx]?)) = some val

namespace LowerSimRel

/-- Initial states are related: the ANF initial state corresponds to the IR initial state.
    Proof: `lower prog = .ok irmod` ensures the IR module is well-formed.
    The initial ANF env is empty (no bindings to check), and the IR starts with
    the entry code (call to _start or empty).
    NOTE: `hcode` is a hypothesis because `lowerExpr` is private in Lower.lean —
    once made public, this can be proved from `hlower` directly. -/
theorem init (prog : ANF.Program) (irmod : IRModule)
    (hlower : Wasm.lower prog = .ok irmod)
    (hcode : LowerCodeCorr prog.main (irInitialState irmod).code) :
    LowerSimRel prog irmod (ANF.initialState prog) (irInitialState irmod) where
  hlower := hlower
  hmod := rfl
  hcode := by simp [ANF.initialState]; exact hcode
  hhalt := by
    -- Halt correspondence at init: irInitialState is already halted because
    -- lower always sets startFunc := none (WASI convention).
    intro _
    have hsf := lower_startFunc_none prog irmod hlower
    simp [IRExecState.halted, irInitialState, hsf]
  hframes := by simp [irInitialState]
  henv := by
    intro name v hlookup
    -- Initial ANF env is empty, so lookup always returns none
    simp [ANF.initialState, ANF.Env.empty, ANF.Env.lookup] at hlookup
  hvar := by
    intro name idx hexpr hcode_ir
    -- Initial ANF env is empty, so if expr is a var, lookup fails.
    -- But we still need this to hold — it's vacuously true if the program
    -- doesn't start with a bare variable reference (well-formed programs don't).
    -- For now, blocked on lowerExpr being private.
    sorry

/-- Step simulation (1:1): if the ANF takes one step, the IR takes a matching step.
    Now provable with LowerCodeCorr: case analysis on the ANF expression form
    tells us what the IR code looks like, which determines what irStep? returns.
    Each case is decomposed below; each sub-case may still be sorry'd but the
    architecture is clear.
    REF: Standard forward simulation diagram. -/
theorem step_sim (prog : ANF.Program) (irmod : IRModule) :
    ∀ (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State),
    LowerSimRel prog irmod s1 s2 → anfStepMapped s1 = some (t, s1') →
    ∃ s2', irStep? s2 = some (t, s2') ∧ LowerSimRel prog irmod s1' s2' := by
  intro s1 s2 t s1' hrel hstep
  simp only [anfStepMapped] at hstep
  split at hstep
  · simp at hstep
  · rename_i heq
    simp at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    -- heq : ANF.step? s1 = some (ct, s1') for some Core.TraceEvent ct
    -- hrel.hcode : LowerCodeCorr s1.expr s2.code
    -- Case analysis on the ANF expression form (= what s1.expr is)
    -- Each case tells us what IR code s2.code has (via LowerCodeCorr),
    -- which determines what irStep? s2 returns.
    match hexpr : s1.expr with
    | .trivial (.var name) =>
        -- Variable reference: IR code is [localGet idx]
        -- ANF steps by looking up name in env, IR steps by localGet
        sorry
    | .trivial .litNull =>
        -- Literal null: ANF.step? returns none for literals, contradiction with heq
        have h := ANF.step?_litNull s1
        have : { s1 with expr := ANF.Expr.trivial .litNull } = s1 := by cases s1; simp_all
        rw [this] at h; simp [h] at heq
    | .trivial .litUndefined =>
        have h := ANF.step?_litUndefined s1
        have : { s1 with expr := ANF.Expr.trivial .litUndefined } = s1 := by cases s1; simp_all
        rw [this] at h; simp [h] at heq
    | .trivial (.litBool b) =>
        have h := ANF.step?_litBool s1 b
        have : { s1 with expr := ANF.Expr.trivial (.litBool b) } = s1 := by cases s1; simp_all
        rw [this] at h; simp [h] at heq
    | .trivial (.litNum n) =>
        have h := ANF.step?_litNum s1 n
        have : { s1 with expr := ANF.Expr.trivial (.litNum n) } = s1 := by cases s1; simp_all
        rw [this] at h; simp [h] at heq
    | .trivial (.litStr str) =>
        have h := ANF.step?_litStr s1 str
        have : { s1 with expr := ANF.Expr.trivial (.litStr str) } = s1 := by cases s1; simp_all
        rw [this] at h; simp [h] at heq
    | .trivial (.litObject addr) =>
        have h := ANF.step?_litObject s1 addr
        have : { s1 with expr := ANF.Expr.trivial (.litObject addr) } = s1 := by cases s1; simp_all
        rw [this] at h; simp [h] at heq
    | .trivial (.litClosure fi ep) =>
        have h := ANF.step?_litClosure s1 fi ep
        have : { s1 with expr := ANF.Expr.trivial (.litClosure fi ep) } = s1 := by cases s1; simp_all
        rw [this] at h; simp [h] at heq
    | .«let» name rhs body =>
        -- Let-binding: ANF evaluates rhs and binds result
        -- IR code is rhsCode ++ [localSet idx] ++ bodyCode
        -- Need to show IR executes rhs code, then localSet, matching ANF's let step
        sorry
    | .seq a b =>
        -- Sequence: ANF either skips completed a, or steps a
        -- IR code is aCode ++ [drop] ++ bCode
        sorry
    | .«if» cond then_ else_ =>
        -- Conditional: ANF evaluates cond trivial, picks branch
        -- IR code is condCode ++ [if_ ...]
        sorry
    | .while_ cond body =>
        -- While loop: ANF checks cond value or steps cond
        sorry
    | .throw arg =>
        -- Throw: ANF produces error event
        sorry
    | .tryCatch body catchParam catchBody finally_ =>
        -- Try-catch: ANF steps body, catches errors
        sorry
    | .«return» arg =>
        -- Return: ANF evaluates return value
        sorry
    | .yield arg delegate =>
        -- Yield: ANF produces value
        sorry
    | .await arg =>
        -- Await: ANF evaluates argument
        sorry
    | .labeled label body =>
        -- Labeled: ANF enters labeled block
        sorry
    | .«break» label =>
        -- Break: ANF breaks to label
        sorry
    | .«continue» label =>
        -- Continue: ANF continues loop
        sorry

/-- Step simulation (stuttering): if the ANF takes one step, the IR takes
    one or more matching steps with the same observable events.
    This is the architecturally correct formulation: one ANF step
    (e.g. let-binding evaluating RHS + binding + continuing with body)
    compiles to multiple IR instructions, so the IR needs multiple steps.
    REF: Standard stuttering forward simulation diagram. -/
theorem step_sim_stutter (prog : ANF.Program) (irmod : IRModule) :
    ∀ (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State),
    LowerSimRel prog irmod s1 s2 → anfStepMapped s1 = some (t, s1') →
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  intro s1 s2 t s1' hrel hstep
  -- Can be derived from step_sim (1:1 implies stuttering with single-element trace):
  obtain ⟨s2', h1, h2⟩ := step_sim prog irmod s1 s2 t s1' hrel hstep
  exact ⟨s2', [t], .tail (.mk h1) (.refl _), h2, rfl⟩

/-- Halt simulation: if ANF halts, the IR halts.
    SORRY: When ANF.step? returns none, the ANF expression is a literal trivial
    (by step?_none_implies_lit). The lowered IR for a literal is a const push
    followed by no more instructions, so irStep? returns none at the
    synchronization point.
    The proof agent should:
    1. Use anfStepMapped_none_iff to get ANF.step? s = none
    2. Use step?_none_implies_lit (or pattern match on halted ANF state)
    3. Show that the IR code at this point is empty (all instructions consumed)
    4. Apply irStep?_halted -/
theorem halt_sim (prog : ANF.Program) (irmod : IRModule) :
    ∀ (s1 : ANF.State) (s2 : IRExecState),
    LowerSimRel prog irmod s1 s2 → anfStepMapped s1 = none → irStep? s2 = none := by
  intro s1 s2 hrel hstep
  exact irStep?_halted (hrel.hhalt hstep)

end LowerSimRel

/-- Abstract code correspondence for emit: each IR instruction maps to 1+ Wasm instructions.
    Since `emitInstr` in Emit.lean is `private partial`, we define the relation abstractly.
    Each constructor captures what Wasm instructions a given IR instruction emits to.
    REF: Each case corresponds to a clause in Emit.lean's emitInstr. -/
inductive EmitCodeCorr : List IRInstr → List Instr → Prop where
  /-- Empty IR code maps to empty Wasm code. -/
  | nil : EmitCodeCorr [] []
  /-- i32 const maps to i32.const.
      `hparse` ensures the IR string value parses to the same number. -/
  | const_i32 (v : String) (n : UInt32) (rest_ir : List IRInstr) (rest_w : List Instr)
      (hparse : v.toNat? = some n.toNat) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.const_ .i32 v :: rest_ir) (.i32Const n :: rest_w)
  /-- i64 const maps to i64.const.
      `hparse` ensures the IR string value parses to the same number. -/
  | const_i64 (v : String) (n : UInt64) (rest_ir : List IRInstr) (rest_w : List Instr)
      (hparse : v.toNat? = some n.toNat) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.const_ .i64 v :: rest_ir) (.i64Const n :: rest_w)
  /-- f64 const maps to f64.const. -/
  | const_f64 (v : String) (f : Float) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.const_ .f64 v :: rest_ir) (.f64Const f :: rest_w)
  /-- localGet maps to local.get. -/
  | localGet (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.localGet idx :: rest_ir) (.localGet idx :: rest_w)
  /-- localSet maps to local.set. -/
  | localSet (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.localSet idx :: rest_ir) (.localSet idx :: rest_w)
  /-- globalGet maps to global.get. -/
  | globalGet (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.globalGet idx :: rest_ir) (.globalGet idx :: rest_w)
  /-- globalSet maps to global.set. -/
  | globalSet (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.globalSet idx :: rest_ir) (.globalSet idx :: rest_w)
  /-- binOp i32 "add" maps to i32.add. -/
  | binOp_i32_add (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.binOp .i32 "add" :: rest_ir) (.i32Add :: rest_w)
  /-- binOp i32 "sub" maps to i32.sub. -/
  | binOp_i32_sub (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.binOp .i32 "sub" :: rest_ir) (.i32Sub :: rest_w)
  /-- binOp i32 "mul" maps to i32.mul. -/
  | binOp_i32_mul (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.binOp .i32 "mul" :: rest_ir) (.i32Mul :: rest_w)
  /-- call maps to call. -/
  | call_ (funcIdx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.call funcIdx :: rest_ir) (.call funcIdx :: rest_w)
  /-- drop maps to drop. -/
  | drop_ (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.drop :: rest_ir) (.drop :: rest_w)
  /-- return_ maps to return. -/
  | return__ (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.return_ :: rest_ir) (.return_ :: rest_w)
  /-- General case for instructions not yet decomposed. -/
  | general (ir_instr : IRInstr) (wasm_instrs : List Instr)
      (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (ir_instr :: rest_ir) (wasm_instrs ++ rest_w)

/-- EmitCodeCorr [] implies wasm code is also []. -/
theorem EmitCodeCorr.nil_inv {wcode : List Instr}
    (h : EmitCodeCorr [] wcode) : wcode = [] := by
  cases h with
  | nil => rfl

/-! ### EmitCodeCorr inversion lemmas
    These extract structure from EmitCodeCorr without dependent elimination issues. -/

/-- Inversion for drop :: rest. -/
theorem EmitCodeCorr.drop_inv {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.drop :: rest) wcode) :
    (∃ rest_w, wcode = Instr.drop :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | drop_ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for return_ :: rest. -/
theorem EmitCodeCorr.return_inv {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.return_ :: rest) wcode) :
    (∃ rest_w, wcode = Instr.return_ :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | return__ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for call :: rest. -/
theorem EmitCodeCorr.call_inv {funcIdx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.call funcIdx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.call funcIdx :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | call_ _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for localGet :: rest. -/
theorem EmitCodeCorr.localGet_inv {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.localGet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.localGet idx :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | localGet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for localSet :: rest. -/
theorem EmitCodeCorr.localSet_inv {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.localSet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.localSet idx :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | localSet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for globalGet :: rest. -/
theorem EmitCodeCorr.globalGet_inv {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.globalGet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.globalGet idx :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | globalGet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for globalSet :: rest. -/
theorem EmitCodeCorr.globalSet_inv {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.globalSet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.globalSet idx :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | globalSet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for const_ .i32 :: rest. -/
theorem EmitCodeCorr.const_i32_inv {v : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.const_ .i32 v :: rest) wcode) :
    (∃ n rest_w, wcode = Instr.i32Const n :: rest_w ∧ v.toNat? = some n.toNat ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | const_i32 _ n _ rw hp hrw => left; exact ⟨n, rw, rfl, hp, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- Inversion for const_ .f64 :: rest. -/
theorem EmitCodeCorr.const_f64_inv {v : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.const_ .f64 v :: rest) wcode) :
    (∃ f rest_w, wcode = Instr.f64Const f :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    (∃ wasm_instrs rest_w, wcode = wasm_instrs ++ rest_w ∧ EmitCodeCorr rest rest_w) := by
  cases h with
  | const_f64 _ f _ rw hrw => left; exact ⟨f, rw, rfl, hrw⟩
  | general _ wi _ rw hrw => right; exact ⟨wi, rw, rfl, hrw⟩

/-- General inversion for any IR instruction. -/
theorem EmitCodeCorr.cons_inv {instr : IRInstr} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (instr :: rest) wcode) :
    ∃ wasm_prefix rest_w, wcode = wasm_prefix ++ rest_w ∧ EmitCodeCorr rest rest_w := by
  cases h with
  | const_i32 _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | const_i64 _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | const_f64 _ _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | localGet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | localSet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | globalGet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | globalSet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_add _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_sub _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_mul _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | call_ _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | drop_ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | return__ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | general _ wi _ rw hrw => exact ⟨wi, rw, rfl, hrw⟩

/-- Simulation relation for IR → Wasm emit.
    The step correspondence field provides the matching Wasm step for each IR step.
    REF: Standard forward simulation diagram. -/
structure EmitSimRel (irmod : IRModule) (wmod : Module)
    (ir : IRExecState) (w : ExecState) : Prop where
  /- The Wasm module is the result of emitting the IR module. -/
  hemit : emit irmod = .ok wmod
  /- Code correspondence: the Wasm code is the emitted form of the IR code. -/
  hcode : EmitCodeCorr ir.code w.code
  /- Stack correspondence. -/
  hstack : ir.stack.length = w.stack.length
  /- Label correspondence (needed for halt derivation). -/
  hlabels : ir.labels.length = w.labels.length
  /- Halt correspondence. -/
  hhalt : irStep? ir = none → Wasm.step? w = none

namespace EmitSimRel

/-- emit preserves startFunc as the Wasm start section. -/
private theorem emit_preserves_start (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    wmod.start = irmod.startFunc := by
  -- emit m = .ok (buildModule m acc) for some acc
  -- buildModule_start: (buildModule m acc).start = m.startFunc
  unfold emit at hemit
  simp only [Bind.bind, Except.bind] at hemit
  split at hemit
  · simp at hemit
  · simp only [Except.ok.injEq] at hemit
    rw [← hemit]; rfl

/-- Initial states are related: the IR initial state corresponds to the Wasm initial state.
    Proof: `emit irmod = .ok wmod` ensures module correspondence.
    Both start with empty stacks, and the entry code (start function call) is
    the same (emit preserves the start function field). -/
theorem init (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    EmitSimRel irmod wmod (irInitialState irmod) (Wasm.initialState wmod) where
  hemit := hemit
  hcode := by
    -- Both initial states derive entry code from startFunc/start.
    -- emit preserves startFunc as the Wasm start section.
    have hstart := emit_preserves_start irmod wmod hemit
    simp only [irInitialState, Wasm.initialState]
    split
    · -- startFunc = some idx: IR has [call idx], Wasm has [call idx] (by hstart)
      rename_i idx hsf
      rw [hstart, hsf]
      exact .call_ idx [] [] .nil
    · -- startFunc = none: both have []
      rename_i hsf
      rw [hstart, hsf]
      exact .nil
  hstack := by simp [irInitialState, Wasm.initialState]
  hlabels := by simp [irInitialState, Wasm.initialState]
  hhalt := by
    intro hirHalt
    rw [irStep?_none_iff_halted] at hirHalt
    obtain ⟨hc, hl, _⟩ := hirHalt
    have hstart := emit_preserves_start irmod wmod hemit
    apply step?_halted
    constructor
    · simp [irInitialState] at hc
      split at hc
      · simp at hc
      · rename_i hsf; simp [Wasm.initialState, hstart, hsf]
    · simp [Wasm.initialState]

/-- Derive halt correspondence from code + label correspondence.
    Used to reconstruct `hhalt` in step_sim proofs. -/
theorem hhalt_of_structural {ir : IRExecState} {w : ExecState}
    (hcode : EmitCodeCorr ir.code w.code)
    (hlabels : ir.labels.length = w.labels.length) :
    irStep? ir = none → Wasm.step? w = none := by
  intro h
  rw [irStep?_none_iff_halted] at h
  obtain ⟨hc, hl, _⟩ := h
  apply step?_halted
  constructor
  · rw [hc] at hcode; exact EmitCodeCorr.nil_inv hcode
  · cases hlw : w.labels with
    | nil => rfl
    | cons _ _ => rw [hl, hlw] at hlabels; simp at hlabels

/-- Step simulation (1:1): if the IR takes one step, the Wasm takes a matching step.
    Now provable with EmitCodeCorr: case analysis on the IR instruction form
    tells us what the Wasm code looks like, which determines what Wasm.step? returns.
    Each IR instruction maps 1:1 to a Wasm instruction for the simple cases.
    REF: Standard forward simulation diagram. -/
theorem step_sim (irmod : IRModule) (wmod : Module) :
    ∀ (s1 : IRExecState) (s2 : ExecState) (t : TraceEvent) (s1' : IRExecState),
    EmitSimRel irmod wmod s1 s2 → irStep? s1 = some (t, s1') →
    ∃ s2', Wasm.step? s2 = some (traceToWasm t, s2') ∧
      EmitSimRel irmod wmod s1' s2' := by
  intro s1 s2 t s1' hrel hstep
  -- Case analysis on the IR code (what instruction is being executed)
  -- irStep? dispatches on s1.code; EmitCodeCorr tells us what s2.code is
  match hcode_ir : s1.code with
  | [] =>
      -- No instructions: irStep? checks labels/frames, not instruction dispatch
      -- This is the label-pop or frame-return case
      sorry
  | instr :: rest =>
      match instr with
      | .const_ .i32 v =>
          -- i32 const: IR pushes i32, Wasm pushes i32_const
          sorry
      | .const_ .i64 v =>
          -- i64 const
          sorry
      | .const_ .f64 v =>
          -- f64 const
          sorry
      | .const_ .ptr v =>
          -- ptr const (same as i32 in Wasm)
          sorry
      | .localGet idx =>
          -- local.get: both IR and Wasm look up local variable
          sorry
      | .localSet idx =>
          -- local.set: both pop value and set local
          sorry
      | .globalGet idx =>
          -- global.get
          sorry
      | .globalSet idx =>
          -- global.set
          sorry
      | .load t offset =>
          -- memory load
          sorry
      | .store t offset =>
          -- memory store
          sorry
      | .store8 offset =>
          -- memory store8
          sorry
      | .binOp t op =>
          -- binary operation: IR and Wasm use same semantics
          sorry
      | .unOp t op =>
          -- unary operation
          sorry
      | .call funcIdx =>
          -- function call
          sorry
      | .callIndirect typeIdx =>
          -- indirect call
          sorry
      | .block label body =>
          -- block: enter block scope
          sorry
      | .loop label body =>
          -- loop: enter loop scope
          sorry
      | .if_ result then_ else_ =>
          -- if: conditional branch
          sorry
      | .br label =>
          -- unconditional branch
          sorry
      | .brIf label =>
          -- conditional branch
          sorry
      | .return_ =>
          -- return from function
          sorry
      | .drop =>
          -- drop: IR and Wasm both pop top of stack (or both trap on empty stack)
          -- Invert EmitCodeCorr to get Wasm code structure
          have hc : EmitCodeCorr (IRInstr.drop :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.drop_inv with ⟨rest_w, hcw, hrest⟩ | ⟨wasm_instrs, rest_w, hcw, hrest⟩
          · -- Specific case: Wasm code = .drop :: rest_w
            match hstk : s1.stack with
            | [] =>
              -- Empty stack: both sides trap
              -- The IR traps with "stack underflow in drop"
              -- The Wasm also traps (its stack is also empty by hstack)
              sorry -- trap case: needs careful state construction
            | v :: stk =>
              -- Non-empty stack: both sides drop silently
              have hir := irStep?_eq_drop s1 rest v stk hcode_ir hstk
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- Wasm stack also non-empty (by length correspondence)
              have hlen := hrel.hstack
              rw [hstk] at hlen
              match hs2 : s2.stack with
              | [] => simp_all
              | wval :: stk_w =>
                simp [hs2] at hlen
                have hw_step := step?_eq_drop s2 rest_w wval stk_w hcw hs2
                exact ⟨{ s2 with code := rest_w, stack := stk_w, trace := s2.trace ++ [.silent] },
                  by simp [traceToWasm]; exact hw_step,
                  { hemit := hrel.hemit
                    hcode := hrest
                    hstack := by simp at hlen ⊢; omega
                    hlabels := hrel.hlabels
                    hhalt := hhalt_of_structural hrest hrel.hlabels }⟩
          · -- General case (EmitCodeCorr.general): unknown Wasm instructions
            sorry
      | .memoryGrow =>
          -- grow memory
          sorry

/-- Step simulation (stuttering): if the IR takes one step, the Wasm takes
    one or more matching steps with the same observable events.
    This is the architecturally correct formulation.
    REF: Standard stuttering forward simulation diagram. -/
theorem step_sim_stutter (irmod : IRModule) (wmod : Module) :
    ∀ (s1 : IRExecState) (s2 : ExecState) (t : TraceEvent) (s1' : IRExecState),
    EmitSimRel irmod wmod s1 s2 → irStep? s1 = some (t, s1') →
    ∃ (s2' : ExecState) (w_trace : List Wasm.TraceEvent),
      Wasm.Steps s2 w_trace s2' ∧
      EmitSimRel irmod wmod s1' s2' ∧
      Wasm.observableWasmEvents w_trace = Wasm.observableWasmEvents [traceToWasm t] := by
  intro s1 s2 t s1' hrel hstep
  obtain ⟨s2', h1, h2⟩ := step_sim irmod wmod s1 s2 t s1' hrel hstep
  exact ⟨s2', [traceToWasm t], .tail (.mk h1) (.refl _), h2, rfl⟩

/-- Halt simulation: if IR halts, Wasm halts.
    Proof: Extract halt correspondence from EmitSimRel. -/
theorem halt_sim (irmod : IRModule) (wmod : Module) :
    ∀ (s1 : IRExecState) (s2 : ExecState),
    EmitSimRel irmod wmod s1 s2 → irStep? s1 = none → Wasm.step? s2 = none := by
  intro s1 s2 hrel hstep
  exact hrel.hhalt hstep

end EmitSimRel

/-! ### Stuttering Forward Simulation (Alternative Framework)

The 1:1 `IRForwardSim` requires exactly one IR step per source step.
In practice, one ANF step (e.g., `let x = f(a) in body`) compiles to
multiple IR instructions (push args, call, localSet). The **stuttering
forward simulation** allows one source step to correspond to one or more
target steps, with all but the last producing `.silent` events.

This framework provides an alternative path to behavioral preservation
when 1:1 step correspondence is too restrictive. The proof agent may
choose either framework depending on the lowering structure. -/

/-- Stuttering forward simulation: one source step corresponds to one or more
    target IR steps. The target steps produce a trace whose observable events
    match the source step's observable event. -/
structure IRStutterSim {S : Type} (R : S → IRExecState → Prop)
    (step_src : S → Option (TraceEvent × S)) where
  /-- One source step → one or more IR steps with matching observable events. -/
  step_sim : ∀ (s1 : S) (s2 : IRExecState) (t : TraceEvent) (s1' : S),
    R s1 s2 → step_src s1 = some (t, s1') →
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      R s1' s2' ∧
      observableEvents ir_trace = observableEvents [t]
  /-- Source halts → target halts. -/
  halt_sim : ∀ (s1 : S) (s2 : IRExecState),
    R s1 s2 → step_src s1 = none → irStep? s2 = none

/-- Stuttering simulation lifts multi-step source execution to multi-step IR execution,
    preserving observable events. -/
theorem IRStutterSim_steps {S : Type} {R : S → IRExecState → Prop}
    {step_src : S → Option (TraceEvent × S)}
    (sim : IRStutterSim R step_src)
    {s1_init : S} {s2_init : IRExecState}
    {ts : List TraceEvent} {s1_final : S}
    (hR_init : R s1_init s2_init)
    (hExec : StepStar step_src s1_init ts s1_final) :
    ∃ (s2_final : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2_init ir_trace s2_final ∧
      R s1_final s2_final ∧
      observableEvents ir_trace = observableEvents ts := by
  induction hExec generalizing s2_init with
  | refl _ =>
    exact ⟨s2_init, [], IRSteps.refl _, hR_init, rfl⟩
  | step hSrcStep _hRest ih =>
    obtain ⟨ir_mid, ir_trace1, hIR1, hR_mid, hObs1⟩ :=
      sim.step_sim _ _ _ _ hR_init hSrcStep
    obtain ⟨ir_final, ir_trace2, hIR2, hR_final, hObs2⟩ := ih hR_mid
    refine ⟨ir_final, ir_trace1 ++ ir_trace2,
      IRSteps_trans hIR1 hIR2, hR_final, ?_⟩
    simp only [observableEvents_append, hObs1, hObs2]
    rename_i t_ev _
    cases t_ev <;> simp [observableEvents]

/-- Behavioral equivalence up to silent events.
    The IR produces a trace whose observable events match the mapped source trace.
    This is the correct behavioral equivalence for stuttering simulation. -/
def IRBehavesObs (m : IRModule) (obs : List TraceEvent) : Prop :=
  ∃ (sFinal : IRExecState) (ir_trace : List TraceEvent),
    IRSteps (irInitialState m) ir_trace sFinal ∧
    irStep? sFinal = none ∧
    observableEvents ir_trace = obs

/-- Stuttering simulation preserves observable behavior.
    Given a stuttering forward simulation, if the source behaves with trace `ts`,
    the IR produces a trace with the same observable events. -/
theorem IRStutterSim_behavioral {S : Type} {R : S → IRExecState → Prop}
    {step_src : S → Option (TraceEvent × S)}
    (sim : IRStutterSim R step_src)
    {s_init : S} {ir_init : IRExecState}
    (hR : R s_init ir_init)
    (hInit : ir_init = irInitialState ir_init.module)
    {ts : List TraceEvent}
    (hBehaves : DetBehaves step_src s_init ts) :
    IRBehavesObs ir_init.module (observableEvents ts) := by
  obtain ⟨s_final, hExec, hHalt⟩ := hBehaves
  obtain ⟨ir_final, ir_trace, hIRSteps, hR_final, hObs⟩ :=
    IRStutterSim_steps sim hR hExec
  rw [hInit] at hIRSteps
  exact ⟨ir_final, ir_trace, hIRSteps, sim.halt_sim _ _ hR_final hHalt, hObs⟩

/-- Bridge: convert ANF.Steps to StepStar anfStepMapped.
    This allows us to use the ANF.Behaves definition (which uses ANF.Steps)
    with the IRForwardSim framework (which uses StepStar/DetBehaves). -/
theorem StepStar_of_ANFSteps {s1 s2 : ANF.State} {ts : List Core.TraceEvent}
    (hSteps : ANF.Steps s1 ts s2) :
    StepStar anfStepMapped s1 (ts.map traceFromCore) s2 := by
  induction hSteps with
  | refl _ => simp [List.map]; exact StepStar.refl _
  | tail hstep _hrest ih =>
    obtain ⟨h⟩ := hstep
    exact .step (anfStepMapped_some _ _ _ h) ih

/-- Bridge: ANF.Behaves implies DetBehaves anfStepMapped with mapped trace.
    This is the key bridge between ANF behavioral semantics and the
    IRForwardSim framework. -/
theorem DetBehaves_of_ANFBehaves {prog : ANF.Program} {ts : List Core.TraceEvent}
    (hBeh : ANF.Behaves prog ts) :
    DetBehaves anfStepMapped (ANF.initialState prog) (ts.map traceFromCore) := by
  obtain ⟨sFinal, hSteps, hHalt⟩ := hBeh
  exact ⟨sFinal, StepStar_of_ANFSteps hSteps, (anfStepMapped_none_iff sFinal).mpr hHalt⟩

/-- traceListFromCore is the same as List.map traceFromCore. -/
@[simp] theorem traceListFromCore_eq_map (ts : List Core.TraceEvent) :
    traceListFromCore ts = ts.map traceFromCore := rfl

/-- Bridge (proved): ANF.Behaves → IRBehavesObs via stuttering simulation.
    Composes DetBehaves_of_ANFBehaves with IRStutterSim_behavioral. -/
theorem lower_behavioral_obs (prog : ANF.Program) (irmod : IRModule)
    (_hlower : Wasm.lower prog = .ok irmod)
    {R : ANF.State → IRExecState → Prop}
    (hR_init : R (ANF.initialState prog) (irInitialState irmod))
    (sim : IRStutterSim R anfStepMapped) :
    ∀ trace, ANF.Behaves prog trace →
      IRBehavesObs irmod (observableEvents (traceListFromCore trace)) := by
  intro trace hBeh
  have hDet := DetBehaves_of_ANFBehaves hBeh
  have hInitEq : irInitialState irmod = irInitialState (irInitialState irmod).module := by
    simp [irInitialState]
  rw [traceListFromCore_eq_map]
  exact IRStutterSim_behavioral sim hR_init hInitEq hDet

/-- THE FORWARD SIMULATION: ANF → IR (1:1 version for LowerCorrect.lean).
    For each ANF step, the lowered IR module can take a corresponding IR step
    with the mapped trace event. Used by the existing proof chain. -/
theorem ir_forward_sim (prog : ANF.Program) (irmod : IRModule)
    (hlower : Wasm.lower prog = .ok irmod) :
    ∃ (R : ANF.State → IRExecState → Prop),
      R (ANF.initialState prog) (irInitialState irmod) ∧
      IRForwardSim R anfStepMapped := by
  refine ⟨LowerSimRel prog irmod, ?_, ?_⟩
  · -- BLOCKED: requires LowerCodeCorr for initial program (needs lowerExpr public)
    exact LowerSimRel.init prog irmod hlower (by sorry)
  · exact {
      step_sim := LowerSimRel.step_sim prog irmod
      halt_sim := LowerSimRel.halt_sim prog irmod
    }

/-- THE STUTTERING SIMULATION: ANF → IR (architecturally correct version).
    One ANF step → one or more IR steps with matching observable events. -/
theorem ir_stutter_sim (prog : ANF.Program) (irmod : IRModule)
    (hlower : Wasm.lower prog = .ok irmod) :
    ∃ (R : ANF.State → IRExecState → Prop),
      R (ANF.initialState prog) (irInitialState irmod) ∧
      IRStutterSim R anfStepMapped := by
  refine ⟨LowerSimRel prog irmod, ?_, ?_⟩
  · -- BLOCKED: requires LowerCodeCorr for initial program (needs lowerExpr public)
    exact LowerSimRel.init prog irmod hlower (by sorry)
  · exact {
      step_sim := LowerSimRel.step_sim_stutter prog irmod
      halt_sim := LowerSimRel.halt_sim prog irmod
    }

/-- 1:1 version: lower_behavioral_correct using IRForwardSim (for LowerCorrect.lean). -/
theorem lower_behavioral_correct' (prog : ANF.Program) (irmod : IRModule)
    (hlower : Wasm.lower prog = .ok irmod) :
    ∀ trace, ANF.Behaves prog trace →
      IRBehaves irmod (traceListFromCore trace) := by
  intro trace hBeh
  obtain ⟨R, hR_init, sim⟩ := ir_forward_sim prog irmod hlower
  have hDet := DetBehaves_of_ANFBehaves hBeh
  have hIR := IRForwardSim_behavioral sim hR_init hDet
  simp only [traceListFromCore_eq_map]
  exact hIR

/-- Stuttering version: lower_behavioral_correct using observable events. -/
theorem lower_behavioral_obs_correct (prog : ANF.Program) (irmod : IRModule)
    (hlower : Wasm.lower prog = .ok irmod) :
    ∀ trace, ANF.Behaves prog trace →
      IRBehavesObs irmod (observableEvents (traceListFromCore trace)) := by
  exact lower_behavioral_obs prog irmod hlower
    (LowerSimRel.init prog irmod hlower (by sorry))
    { step_sim := LowerSimRel.step_sim_stutter prog irmod
      halt_sim := LowerSimRel.halt_sim prog irmod }

/-! ### IR → Wasm Stuttering Forward Simulation (for EmitCorrect)

The emit pass translates IR instructions to Wasm AST instructions.
Some IR instructions (e.g. f64 const, negation) emit to multiple Wasm instructions.
The stuttering simulation allows one IR step to correspond to one or more Wasm steps.
The observable events (traps) must match. -/

/-- Stuttering forward simulation: IR → Wasm.
    One IR step → one or more Wasm steps with matching observable events. -/
structure WasmStutterSim (R : IRExecState → ExecState → Prop) where
  /-- One IR step → one or more Wasm steps with matching observable events. -/
  step_sim : ∀ (s1 : IRExecState) (s2 : ExecState) (t : TraceEvent) (s1' : IRExecState),
    R s1 s2 → irStep? s1 = some (t, s1') →
    ∃ (s2' : ExecState) (w_trace : List Wasm.TraceEvent),
      Wasm.Steps s2 w_trace s2' ∧ R s1' s2' ∧
      Wasm.observableWasmEvents w_trace = Wasm.observableWasmEvents [traceToWasm t]
  /-- Halting preservation: IR halts implies Wasm halts. -/
  halt_sim : ∀ (s1 : IRExecState) (s2 : ExecState),
    R s1 s2 → irStep? s1 = none → Wasm.step? s2 = none

/-- Stuttering simulation lifts multi-step IR execution to multi-step Wasm execution,
    preserving observable events. -/
theorem WasmStutterSim_steps {R : IRExecState → ExecState → Prop}
    (sim : WasmStutterSim R)
    {ir1 : IRExecState} {w1 : ExecState}
    {ts : List TraceEvent} {ir2 : IRExecState}
    (hR : R ir1 w1)
    (hSteps : IRSteps ir1 ts ir2) :
    ∃ (w2 : ExecState) (w_trace : List Wasm.TraceEvent),
      Wasm.Steps w1 w_trace w2 ∧ R ir2 w2 ∧
      Wasm.observableWasmEvents w_trace =
        Wasm.observableWasmEvents (traceListToWasm ts) := by
  induction hSteps generalizing w1 with
  | refl _ =>
    exact ⟨w1, [], Wasm.Steps.refl w1, hR, rfl⟩
  | @tail s1 s2 s3 t ts' hIRStep _hRest ih =>
    obtain ⟨hirEq⟩ := hIRStep
    obtain ⟨w_mid, w_trace1, hwSteps1, hR_mid, hObs1⟩ := sim.step_sim _ _ _ _ hR hirEq
    obtain ⟨w_final, w_trace2, hwSteps2, hR_final, hObs2⟩ := ih hR_mid
    refine ⟨w_final, w_trace1 ++ w_trace2, Wasm.Steps_trans hwSteps1 hwSteps2, hR_final, ?_⟩
    rw [Wasm.observableWasmEvents_append, hObs1, hObs2,
        ← observableWasmEvents_traceListToWasm_cons]

/-- Behavioral equivalence at the Wasm level up to silent events. -/
def WasmBehavesObs (m : Module) (obs : List Wasm.TraceEvent) : Prop :=
  ∃ (sFinal : ExecState) (w_trace : List Wasm.TraceEvent),
    Wasm.Steps (initialState m) w_trace sFinal ∧
    Wasm.step? sFinal = none ∧
    Wasm.observableWasmEvents w_trace = obs

/-- Stuttering simulation preserves observable Wasm behavior.
    Given a WasmStutterSim, if IR executes with trace `ts` and halts,
    the Wasm executes with a trace whose observable events match. -/
theorem WasmStutterSim_behavioral {R : IRExecState → ExecState → Prop}
    (sim : WasmStutterSim R)
    {ir_init : IRExecState} {w_init : ExecState}
    (hR : R ir_init w_init)
    {ts : List TraceEvent}
    (hBehaves : ∃ ir_final, IRSteps ir_init ts ir_final ∧ irStep? ir_final = none) :
    ∃ (sFinal : ExecState) (w_trace : List Wasm.TraceEvent),
      Wasm.Steps w_init w_trace sFinal ∧
      Wasm.step? sFinal = none ∧
      Wasm.observableWasmEvents w_trace =
        Wasm.observableWasmEvents (traceListToWasm ts) := by
  obtain ⟨ir_final, hIRSteps, hIRHalt⟩ := hBehaves
  obtain ⟨w_final, w_trace, hwSteps, hR_final, hObs⟩ :=
    WasmStutterSim_steps sim hR hIRSteps
  exact ⟨w_final, w_trace, hwSteps, sim.halt_sim _ _ hR_final hIRHalt, hObs⟩

/-- THE FORWARD SIMULATION: IR → Wasm (1:1 version for EmitCorrect.lean). -/
theorem emit_forward_sim (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    ∃ (R : IRExecState → ExecState → Prop),
      R (irInitialState irmod) (initialState wmod) ∧
      WasmForwardSim R := by
  refine ⟨EmitSimRel irmod wmod, ?_, ?_⟩
  · exact EmitSimRel.init irmod wmod hemit
  · exact {
      step_sim := EmitSimRel.step_sim irmod wmod
      halt_sim := EmitSimRel.halt_sim irmod wmod
    }

/-- THE STUTTERING SIMULATION: IR → Wasm (architecturally correct version). -/
theorem emit_stutter_sim (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    ∃ (R : IRExecState → ExecState → Prop),
      R (irInitialState irmod) (initialState wmod) ∧
      WasmStutterSim R := by
  refine ⟨EmitSimRel irmod wmod, ?_, ?_⟩
  · exact EmitSimRel.init irmod wmod hemit
  · exact {
      step_sim := EmitSimRel.step_sim_stutter irmod wmod
      halt_sim := EmitSimRel.halt_sim irmod wmod
    }

/-- 1:1 version: emit_behavioral_correct using WasmForwardSim (for EmitCorrect.lean). -/
theorem emit_behavioral_correct' (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    ∀ trace, IRBehaves irmod trace →
      Behaves wmod (traceListToWasm trace) := by
  intro trace hBeh
  obtain ⟨sFinal_ir, hIRSteps, hIRHalt⟩ := hBeh
  obtain ⟨R, hR_init, sim⟩ := emit_forward_sim irmod wmod hemit
  have hW := WasmForwardSim_behavioral R sim hR_init ⟨sFinal_ir, hIRSteps, hIRHalt⟩
  obtain ⟨wFinal, hWSteps, hWHalt⟩ := hW
  exact ⟨wFinal, hWSteps, hWHalt⟩

/-- Stuttering version: emit_behavioral_correct with observable events. -/
theorem emit_behavioral_obs_correct (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    ∀ (ir_trace : List TraceEvent),
    (∃ ir_final, IRSteps (irInitialState irmod) ir_trace ir_final ∧
      irStep? ir_final = none) →
    ∃ (sFinal : ExecState) (w_trace : List Wasm.TraceEvent),
      Wasm.Steps (initialState wmod) w_trace sFinal ∧
      Wasm.step? sFinal = none ∧
      Wasm.observableWasmEvents w_trace =
        Wasm.observableWasmEvents (traceListToWasm ir_trace) := by
  intro ir_trace hIR
  obtain ⟨R, hR_init, sim⟩ := emit_stutter_sim irmod wmod hemit
  exact WasmStutterSim_behavioral sim hR_init hIR

end VerifiedJS.Wasm.IR
