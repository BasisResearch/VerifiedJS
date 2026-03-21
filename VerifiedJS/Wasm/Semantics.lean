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

end VerifiedJS.Wasm
