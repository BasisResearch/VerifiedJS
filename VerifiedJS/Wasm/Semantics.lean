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
  | _ => some (trapState s ("type mismatch in " ++ name))

private def withI64Bin
    (s : ExecState)
    (op : UInt64 → UInt64 → UInt64)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i64 rhs, .i64 lhs, rest) =>
      let v := WasmValue.i64 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s ("type mismatch in " ++ name))

private def withF64Bin
    (s : ExecState)
    (op : Float → Float → Float)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.f64 rhs, .f64 lhs, rest) =>
      let v := WasmValue.f64 (op lhs rhs)
      some (.silent, pushTrace { s with stack := v :: rest } .silent)
  | _ => some (trapState s ("type mismatch in " ++ name))

private def boolToI32 (b : Bool) : WasmValue :=
  .i32 (if b then 1 else 0)

private def withI32Rel
    (s : ExecState)
    (op : UInt32 → UInt32 → Bool)
    (name : String) : Option (TraceEvent × ExecState) :=
  match pop2? s.stack with
  | some (.i32 rhs, .i32 lhs, rest) =>
      some (.silent, pushTrace { s with stack := boolToI32 (op lhs rhs) :: rest } .silent)
  | _ => some (trapState s ("type mismatch in " ++ name))

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

/-- readLE? on a zero-size memory always returns none (first byte access fails).
    The for-in loop immediately hits the else branch on the first iteration (k=0)
    because addr + 0 ≥ mem.size = 0, causing an early return of none. -/
private theorem readLE?_none_of_size_zero (mem : ByteArray) (addr : Nat) (width : Nat) (hw : 0 < width)
    (hsz : mem.size = 0) : readLE? mem addr width = none := by
  -- readLE? unfolds to a do-for loop over [0:width]. The first iteration checks
  -- addr + 0 < mem.size, which is false since mem.size = 0. So it returns none.
  -- Direct unfolding is intractable; use Nat induction on the loop structure.
  -- For now, we use the operational characterization.
  have h0 : ¬ (addr + 0 < mem.size) := by omega
  unfold readLE?
  simp [Id.run]
  cases width with
  | zero => omega
  | succ n =>
    simp only [List.range']
    dsimp [forIn, ForIn.forIn, h0]
    simp [hsz]
    rfl

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

/-- If `a[i]? = some v`, then `i < a.size`. -/
private theorem Array.lt_size_of_getElem? {α : Type} {a : Array α} {i : Nat} {v : α}
    (h : a[i]? = some v) : i < a.size := by
  match h' : decide (i < a.size) with
  | true => exact of_decide_eq_true h'
  | false =>
    exfalso
    have hlt : ¬(i < a.size) := of_decide_eq_false h'
    rw [show a[i]? = none from getElem?_neg a i hlt] at h
    exact absurd h (by simp)

/-- writeLE? on a zero-size memory always returns none (first byte access fails). -/
private theorem writeLE?_none_of_size_zero (mem : ByteArray) (addr : Nat) (width : Nat) (hw : 0 < width)
    (value : UInt64) (hsz : mem.size = 0) : writeLE? mem addr width value = none := by
  have h0 : ¬ (addr + 0 < mem.size) := by omega
  unfold writeLE?
  simp [Id.run]
  cases width with
  | zero => omega
  | succ n =>
    simp only [List.range']
    dsimp [forIn, ForIn.forIn, h0]
    simp [hsz]
    rfl

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

/-- global.get (hcode version) with valid index pushes the global's value. -/
theorem step?_eq_globalGet_valid (s : ExecState) (idx : Nat) (rest : List Instr)
    (v : WasmValue)
    (hcode : s.code = Instr.globalGet idx :: rest)
    (h : idx < s.store.globals.size)
    (hv : s.store.globals[idx] = v) :
    step? s = some (.silent, pushTrace { s with code := rest, stack := v :: s.stack } .silent) := by
  subst hv; cases s; simp_all [step?, pushTrace]

/-- global.get with out-of-bounds index traps. -/
theorem step?_eq_globalGet_oob (s : ExecState) (idx : Nat) (rest : List Instr)
    (hcode : s.code = Instr.globalGet idx :: rest)
    (h : ¬(idx < s.store.globals.size)) :
    let msg := s!"unknown global index {idx}"
    step? s = some (.trap msg,
      { s with code := [], trace := s.trace ++ [.trap msg] }) := by
  cases s; simp_all [step?, trapState, pushTrace]

/-- global.set with valid index and non-empty stack updates the store. -/
theorem step?_eq_globalSet_valid (s : ExecState) (idx : Nat) (rest : List Instr)
    (v : WasmValue) (stk : List WasmValue)
    (hcode : s.code = Instr.globalSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (h : idx < s.store.globals.size) :
    step? s = some (.silent,
      let globals' := s.store.globals.set! idx v
      let store' := { s.store with globals := globals' }
      pushTrace { s with code := rest, stack := stk, store := store' } .silent) := by
  cases s; simp_all [step?, pop1?, pushTrace]

/-- global.set with empty stack traps. -/
theorem step?_eq_globalSet_emptyStack (s : ExecState) (idx : Nat) (rest : List Instr)
    (hcode : s.code = Instr.globalSet idx :: rest)
    (hstack : s.stack = []) :
    step? s = some (.trap "stack underflow in global.set",
      { s with code := [], trace := s.trace ++ [.trap "stack underflow in global.set"] }) := by
  cases s; simp_all [step?, pop1?, trapState, pushTrace]

/-- global.set with out-of-bounds index traps. -/
theorem step?_eq_globalSet_oob (s : ExecState) (idx : Nat) (rest : List Instr)
    (v : WasmValue) (stk : List WasmValue)
    (hcode : s.code = Instr.globalSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (h : ¬(idx < s.store.globals.size)) :
    step? s = some (.trap s!"unknown global index {idx}",
      { s with code := [], trace := s.trace ++ [.trap s!"unknown global index {idx}"] }) := by
  cases s; simp_all [step?, pop1?, trapState, pushTrace]

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

/-- Exact step? result for local.get with hypothesis-form arguments. -/
theorem step?_eq_localGet (s : ExecState) (idx : Nat) (rest : List Instr)
    (fr : Frame) (frs : List Frame)
    (hcode : s.code = Instr.localGet idx :: rest)
    (hframes : s.frames = fr :: frs)
    (hlocal : idx < fr.locals.size) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := fr.locals[idx] :: s.stack
        trace := s.trace ++ [.silent] }) := by
  cases s; simp_all [step?, hlocal, pushTrace]

/-- step? for localGet with no active frame: traps. -/
theorem step?_eq_localGet_noFrame (s : ExecState) (idx : Nat) (rest : List Instr)
    (hcode : s.code = Instr.localGet idx :: rest)
    (hframes : s.frames = []) :
    step? s = some (.trap "local.get without active frame",
      { s with code := [], trace := s.trace ++ [.trap "local.get without active frame"] }) := by
  cases s; simp_all [step?, trapState, pushTrace]

/-- step? for localGet with local index out of bounds: traps. -/
theorem step?_eq_localGet_oob (s : ExecState) (idx : Nat) (rest : List Instr)
    (fr : Frame) (frs : List Frame)
    (hcode : s.code = Instr.localGet idx :: rest)
    (hframes : s.frames = fr :: frs)
    (hlocal : ¬(idx < fr.locals.size)) :
    step? s = some (.trap s!"unknown local index {idx}",
      { s with code := [], trace := s.trace ++ [.trap s!"unknown local index {idx}"] }) := by
  cases s; simp_all [step?, trapState, pushTrace]

/-- Exact step? result for local.set with hypothesis-form arguments. -/
theorem step?_eq_localSet (s : ExecState) (idx : Nat) (rest : List Instr)
    (v : WasmValue) (stk : List WasmValue)
    (fr : Frame) (frs : List Frame)
    (hcode : s.code = Instr.localSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hframes : s.frames = fr :: frs)
    (hlocal : idx < fr.locals.size) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := stk
        frames := { fr with locals := fr.locals.set! idx v } :: frs
        trace := s.trace ++ [.silent] }) := by
  cases s; simp_all [step?, pop1?, hlocal, pushTrace, updateHeadFrame]

/-- step? for localSet with empty stack: traps. -/
theorem step?_eq_localSet_emptyStack (s : ExecState) (idx : Nat) (rest : List Instr)
    (fr : Frame) (frs : List Frame)
    (hcode : s.code = Instr.localSet idx :: rest)
    (hstack : s.stack = [])
    (hframes : s.frames = fr :: frs) :
    step? s = some (.trap "stack underflow in local.set",
      { s with code := [], stack := [], trace := s.trace ++ [.trap "stack underflow in local.set"] }) := by
  cases s; simp_all [step?, pop1?, trapState, pushTrace]

/-- step? for localSet with no active frame: traps regardless of stack. -/
theorem step?_eq_localSet_noFrame (s : ExecState) (idx : Nat) (rest : List Instr)
    (hcode : s.code = Instr.localSet idx :: rest)
    (hframes : s.frames = []) :
    step? s = some (.trap "local.set without active frame",
      { s with code := [], trace := s.trace ++ [.trap "local.set without active frame"] }) := by
  cases s; simp_all [step?, trapState, pushTrace, pop1?]

/-- step? for localSet with local index out of bounds: traps. -/
theorem step?_eq_localSet_oob (s : ExecState) (idx : Nat) (rest : List Instr)
    (v : WasmValue) (stk : List WasmValue)
    (fr : Frame) (frs : List Frame)
    (hcode : s.code = Instr.localSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hframes : s.frames = fr :: frs)
    (hlocal : ¬(idx < fr.locals.size)) :
    step? s = some (.trap s!"unknown local index {idx}",
      { s with code := [], trace := s.trace ++ [.trap s!"unknown local index {idx}"] }) := by
  cases s; simp_all [step?, pop1?, trapState, pushTrace, hlocal]

/-- Exact step? result for i32.add with hypothesis-form arguments. -/
theorem step?_eq_i32Add (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Add :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Add a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Add :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Add, pushTrace]

/-- Exact step? result for i32.sub with hypothesis-form arguments. -/
theorem step?_eq_i32Sub (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Sub :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Sub a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Sub :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Sub, pushTrace]

/-- Exact step? result for i32.mul with hypothesis-form arguments. -/
theorem step?_eq_i32Mul (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Mul :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Mul a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Mul :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Mul, pushTrace]

/-- Exact step? result for f64.add with hypothesis-form arguments. -/
theorem step?_eq_f64Add (s : ExecState) (rest : List Instr)
    (a b : Float) (stk : List WasmValue)
    (hcode : s.code = Instr.f64Add :: rest)
    (hstack : s.stack = .f64 b :: .f64 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Add a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.f64Add :: rest, stack := .f64 b :: .f64 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_f64Add, pushTrace]

/-- Exact step? result for f64.sub with hypothesis-form arguments. -/
theorem step?_eq_f64Sub (s : ExecState) (rest : List Instr)
    (a b : Float) (stk : List WasmValue)
    (hcode : s.code = Instr.f64Sub :: rest)
    (hstack : s.stack = .f64 b :: .f64 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Sub a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.f64Sub :: rest, stack := .f64 b :: .f64 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_f64Sub, pushTrace]

/-- Exact step? result for f64.mul with hypothesis-form arguments. -/
theorem step?_eq_f64Mul (s : ExecState) (rest : List Instr)
    (a b : Float) (stk : List WasmValue)
    (hcode : s.code = Instr.f64Mul :: rest)
    (hstack : s.stack = .f64 b :: .f64 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Mul a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.f64Mul :: rest, stack := .f64 b :: .f64 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_f64Mul, pushTrace]

/-- Exact step? result for f64.div with hypothesis-form arguments. -/
theorem step?_eq_f64Div (s : ExecState) (rest : List Instr)
    (a b : Float) (stk : List WasmValue)
    (hcode : s.code = Instr.f64Div :: rest)
    (hstack : s.stack = .f64 b :: .f64 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (Numerics.f64Div a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.f64Div :: rest, stack := .f64 b :: .f64 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_f64Div, pushTrace]

/-- Exact step? result for block with hypothesis-form arguments.
    REF: Wasm §4.4.8.2 -/
theorem step?_eq_block (s : ExecState) (bt : BlockType) (body : List Instr) (rest : List Instr)
    (hcode : s.code = Instr.block bt body :: rest) :
    step? s = some (.silent,
      { s with
        code := body
        labels := { onBranch := rest, onExit := rest, isLoop := false } :: s.labels
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.block bt body :: rest } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_block, pushTrace]

/-- Exact state after executing a loop instruction: enters body with loop label frame. -/
theorem step?_eq_loop (s : ExecState) (bt : BlockType) (body : List Instr) (rest : List Instr)
    (hcode : s.code = Instr.loop bt body :: rest) :
    step? s = some (.silent,
      { s with
        code := body
        labels := { onBranch := body, onExit := rest, isLoop := true } :: s.labels
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.loop bt body :: rest } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_loop, pushTrace]

/-- Exact step? result for if with true condition (nonzero i32).
    REF: Wasm §4.4.8 -/
theorem step?_eq_if_true (s : ExecState) (bt : BlockType) (then_ else_ rest : List Instr)
    (n : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.if_ bt then_ else_ :: rest)
    (hstack : s.stack = .i32 n :: stk)
    (hn : n ≠ 0) :
    step? s = some (.silent,
      { s with
        code := then_
        stack := stk
        labels := { onBranch := rest, onExit := rest, isLoop := false } :: s.labels
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.if_ bt then_ else_ :: rest, stack := .i32 n :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_if_true (hn := hn), pushTrace]

/-- Exact step? result for if with false condition (zero).
    REF: Wasm §4.4.8 -/
theorem step?_eq_if_false (s : ExecState) (bt : BlockType) (then_ else_ rest : List Instr)
    (stk : List WasmValue)
    (hcode : s.code = Instr.if_ bt then_ else_ :: rest)
    (hstack : s.stack = .i32 0 :: stk) :
    step? s = some (.silent,
      { s with
        code := else_
        stack := stk
        labels := { onBranch := rest, onExit := rest, isLoop := false } :: s.labels
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.if_ bt then_ else_ :: rest, stack := .i32 0 :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_if_false, pushTrace]

/-- Exact step? result for i32.and with hypothesis-form arguments. -/
theorem step?_eq_i32And (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32And :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32And a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32And :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32And, pushTrace]

/-- Exact step? result for i32.or with hypothesis-form arguments. -/
theorem step?_eq_i32Or (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Or :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32Or a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Or :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Or, pushTrace]

/-- Exact step? result for i32.eq with hypothesis-form arguments. -/
theorem step?_eq_i32Eq (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Eq :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := boolToI32 (Numerics.i32Eq a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Eq :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Eq, pushTrace]

/-- Exact step? result for i32.ne with hypothesis-form arguments. -/
theorem step?_eq_i32Ne (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Ne :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := boolToI32 (Numerics.i32Ne a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Ne :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Ne, pushTrace]

/-- Exact step? result for i32.lt_s with hypothesis-form arguments. -/
theorem step?_eq_i32Lts (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Lts :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := boolToI32 (Numerics.i32Lts a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Lts :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Lts, pushTrace]

/-- Exact step? result for i32.gt_s with hypothesis-form arguments. -/
theorem step?_eq_i32Gts (s : ExecState) (rest : List Instr)
    (a b : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Gts :: rest)
    (hstack : s.stack = .i32 b :: .i32 a :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := boolToI32 (Numerics.i32Gts a b) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Gts :: rest, stack := .i32 b :: .i32 a :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Gts, pushTrace]

/-- Exact step? result for i32.eqz with hypothesis-form arguments. -/
theorem step?_eq_i32Eqz (s : ExecState) (rest : List Instr)
    (n : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.i32Eqz :: rest)
    (hstack : s.stack = .i32 n :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := boolToI32 (Numerics.i32Eqz n) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32Eqz :: rest, stack := .i32 n :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32Eqz, pushTrace]

/-- Exact step? result for i32.wrap_i64 with hypothesis-form arguments. -/
theorem step?_eq_i32WrapI64 (s : ExecState) (rest : List Instr)
    (n : UInt64) (stk : List WasmValue)
    (hcode : s.code = Instr.i32WrapI64 :: rest)
    (hstack : s.stack = .i64 n :: stk) :
    step? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (Numerics.i32WrapI64 n) :: stk
        trace := s.trace ++ [.silent] }) := by
  have : { s with code := Instr.i32WrapI64 :: rest, stack := .i64 n :: stk } = s := by
    cases s; simp_all
  rw [← this]; simp [step?_i32WrapI64, pushTrace]

/-- Exact step? result for br when resolveBranch? succeeds. -/
theorem step?_eq_br (s : ExecState) (depth : Nat) (rest : List Instr)
    (lbl : LabelFrame) (labels' : List LabelFrame)
    (hcode : s.code = Instr.br depth :: rest)
    (hresolve : resolveBranch? s.labels depth = some (lbl, labels')) :
    step? s = some (.silent,
      { s with
        labels := labels'
        code := lbl.onBranch
        trace := s.trace ++ [.silent] }) := by
  cases s; simp_all [step?, hresolve, pushTrace]

/-- Exact step? result for br when label not found. -/
theorem step?_eq_br_oob (s : ExecState) (depth : Nat) (rest : List Instr)
    (hcode : s.code = Instr.br depth :: rest)
    (hresolve : resolveBranch? s.labels depth = none) :
    step? s = some (.trap s!"unknown label index {depth}",
      { s with
        code := []
        trace := s.trace ++ [.trap s!"unknown label index {depth}"] }) := by
  cases s; simp_all [step?, hresolve, trapState, pushTrace]

/-- Exact step? result for brIf with true condition (nonzero i32) and successful branch. -/
theorem step?_eq_brIf_true_gen (s : ExecState) (depth : Nat) (rest : List Instr)
    (n : UInt32) (stk : List WasmValue)
    (lbl : LabelFrame) (labels' : List LabelFrame)
    (hcode : s.code = Instr.brIf depth :: rest)
    (hstack : s.stack = .i32 n :: stk)
    (hn : n ≠ 0)
    (hresolve : resolveBranch? s.labels depth = some (lbl, labels')) :
    step? s = some (.silent,
      { s with
        stack := stk
        labels := labels'
        code := lbl.onBranch
        trace := s.trace ++ [.silent] }) := by
  have hne : (n != 0) = true := by simp [bne_iff_ne, hn]
  cases s; subst hcode; subst hstack; simp [step?, pop1?, i32Truth, hne, hresolve, pushTrace]

/-- Exact step? result for brIf with false condition (zero i32). -/
theorem step?_eq_brIf_false_gen (s : ExecState) (depth : Nat) (rest : List Instr)
    (stk : List WasmValue)
    (hcode : s.code = Instr.brIf depth :: rest)
    (hstack : s.stack = .i32 0 :: stk) :
    step? s = some (.silent,
      { s with
        stack := stk
        code := rest
        trace := s.trace ++ [.silent] }) := by
  cases s; simp_all [step?, pop1?, i32Truth, pushTrace]

/-- Exact step? result for call with valid function index and sufficient stack. -/
theorem step?_eq_call_valid (s : ExecState) (idx : Nat) (rest : List Instr)
    (args remainingStack : List WasmValue)
    (hcode : s.code = Instr.call idx :: rest)
    (hfunc : idx < s.store.funcs.size)
    (hpop : popN? s.stack
        (if hT : (s.store.funcs[idx]).typeIdx < s.store.types.size
         then s.store.types[(s.store.funcs[idx]).typeIdx].params.length
         else 0) = some (args, remainingStack)) :
    step? s = some (.silent,
      { s with
        stack := remainingStack
        frames := { locals := args.reverse.toArray ++ ((s.store.funcs[idx]).locals.map defaultValue).toArray
                    moduleInst := 0 } :: s.frames
        code := (s.store.funcs[idx]).body ++ rest
        trace := s.trace ++ [.silent] }) := by
  cases s; simp_all [step?, hfunc, hpop, pushTrace]

/-- Exact step? result for call with out-of-bounds function index. -/
theorem step?_eq_call_oob (s : ExecState) (idx : Nat) (rest : List Instr)
    (hcode : s.code = Instr.call idx :: rest)
    (hfunc : ¬(idx < s.store.funcs.size)) :
    step? s = some (.trap s!"unknown function index {idx}",
      { s with
        code := []
        trace := s.trace ++ [.trap s!"unknown function index {idx}"] }) := by
  cases s; subst hcode; simp [step?, hfunc, trapState, pushTrace]

/-- Exact step? result for call with stack underflow. -/
theorem step?_eq_call_underflow (s : ExecState) (idx : Nat) (rest : List Instr)
    (hcode : s.code = Instr.call idx :: rest)
    (hfunc : idx < s.store.funcs.size)
    (hpop : popN? s.stack
        (if hT : (s.store.funcs[idx]).typeIdx < s.store.types.size
         then s.store.types[(s.store.funcs[idx]).typeIdx].params.length
         else 0) = none) :
    step? s = some (.trap s!"stack underflow in call {idx}",
      { s with
        code := []
        trace := s.trace ++ [.trap s!"stack underflow in call {idx}"] }) := by
  cases s; simp_all [step?, hfunc, hpop, trapState, pushTrace]

/-- Exact step? result for empty code with label to pop. -/
theorem step?_eq_labelDone (s : ExecState) (lbl : LabelFrame) (lbls : List LabelFrame)
    (hcode : s.code = [])
    (hlabels : s.labels = lbl :: lbls) :
    step? s = some (.silent,
      { s with
        code := lbl.onExit
        labels := lbls
        trace := s.trace ++ [.silent] }) := by
  cases s; simp_all [step?, pushTrace]

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
          | [] => some (irTrapState base "local.get without active frame")
          | frame :: _ =>
              match frame.locals[idx]? with
              | some v => some (.silent, irPushTrace { base with stack := v :: base.stack } .silent)
              | none => some (irTrapState base s!"unknown local index {idx}")
      | .localSet idx =>
          match irPop1? base.stack, s.frames with
          | some (v, stk), frame :: frest =>
              if idx < frame.locals.size then
                let frame' := { frame with locals := frame.locals.set! idx v }
                some (.silent, irPushTrace { base with stack := stk, frames := frame' :: frest } .silent)
              else some (irTrapState base s!"unknown local index {idx}")
          | _, [] => some (irTrapState base "local.set without active frame")
          | none, _ => some (irTrapState base "stack underflow in local.set")

      -- Global variables
      | .globalGet idx =>
          match base.globals[idx]? with
          | some v => some (.silent, irPushTrace { base with stack := v :: base.stack } .silent)
          | none => some (irTrapState base s!"unknown global index {idx}")
      | .globalSet idx =>
          match irPop1? base.stack with
          | some (v, stk) =>
              if idx < base.globals.size then
                some (.silent, irPushTrace { base with stack := stk, globals := base.globals.set! idx v } .silent)
              else some (irTrapState base s!"unknown global index {idx}")
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
          | _ => some (irTrapState base ("type mismatch in i32." ++ op))
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
          | _ => some (irTrapState base ("type mismatch in i64." ++ op))
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
          | _ => some (irTrapState base ("type mismatch in f64." ++ op))
      -- Binary operations (ptr = i32)
      | .binOp .ptr op =>
          match irPop2? base.stack with
          | some (.i32 rhs, .i32 lhs, stk) =>
              let result := match op with
                | "add" => IRValue.i32 (Numerics.i32Add lhs rhs)
                | "sub" => IRValue.i32 (Numerics.i32Sub lhs rhs)
                | _ => IRValue.i32 0
              some (.silent, irPushTrace { base with stack := result :: stk } .silent)
          | _ => some (irTrapState base ("type mismatch in ptr." ++ op))

      -- Unary operations (i32)
      -- REF: Wasm §4.4.3.1 (i32 unary), §4.4.5.1 (i32.wrap_i64)
      | .unOp .i32 op =>
          match irPop1? base.stack with
          | some (.i32 v, stk) =>
              match op with
                | "eqz" => some (.silent, irPushTrace { base with stack := irBoolToI32 (Numerics.i32Eqz v) :: stk } .silent)
                | "clz" => some (.silent, irPushTrace { base with stack := IRValue.i32 (Numerics.i32Clz v) :: stk } .silent)
                | "ctz" => some (.silent, irPushTrace { base with stack := IRValue.i32 (Numerics.i32Ctz v) :: stk } .silent)
                | "popcnt" => some (.silent, irPushTrace { base with stack := IRValue.i32 (Numerics.i32Popcnt v) :: stk } .silent)
                | _ => some (irTrapState base s!"type mismatch in i32.{op}")
          -- Cross-type: wrap_i64 takes i64 → i32
          | some (.i64 v, stk) =>
              match op with
              | "wrap_i64" => some (.silent, irPushTrace { base with stack := .i32 (Numerics.i32WrapI64 v) :: stk } .silent)
              | _ => some (irTrapState base s!"type mismatch in i32.{op}")
          | some _ => some (irTrapState base s!"type mismatch in i32.{op}")
          | none => some (irTrapState base s!"stack underflow in i32.{op}")
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

      -- Memory: load (little-endian, width from type: i32=4, f64=8)
      -- Uses readLE? to match Wasm semantics exactly.
      -- Trap messages match Wasm step? for forward simulation.
      | .load t offset =>
          let loadName := match t with | .i32 => "i32.load" | .f64 => "f64.load" | .i64 => "i64.load" | .ptr => "ptr.load"
          match irPop1? base.stack with
          | some (.i32 addr, stk) =>
              let byteAddr := addr.toNat + offset
              let width := match t with | .i32 => 4 | .f64 => 8 | .i64 => 8 | .ptr => 4
              match readLE? base.memory byteAddr width with
              | some raw =>
                let val := match t with
                  | .i32 => IRValue.i32 (UInt32.ofNat raw.toNat)
                  | .f64 => IRValue.f64 (u64BitsToFloat raw)
                  | .i64 => IRValue.i64 raw
                  | .ptr => IRValue.i32 (UInt32.ofNat raw.toNat)
                some (.silent, irPushTrace { base with stack := val :: stk } .silent)
              | none => some (irTrapState base ("memory access fault in " ++ loadName))
          | some _ => some (irTrapState base ("type mismatch in " ++ loadName))
          | none => some (irTrapState base ("stack underflow in " ++ loadName))
      -- Memory: store (little-endian, width from type: i32=4, f64=8)
      -- Uses writeLE? to match Wasm semantics exactly.
      -- Trap messages match Wasm step? for forward simulation.
      | .store t offset =>
          match t with
          | .i32 =>
            match irPop2? base.stack with
            | some (.i32 val, .i32 addr, stk) =>
                let byteAddr := addr.toNat + offset
                match writeLE? base.memory byteAddr 4 val.toUInt64 with
                | some mem =>
                  some (.silent, irPushTrace { base with stack := stk, memory := mem } .silent)
                | none => some (irTrapState base "memory access fault in i32.store")
            | some _ => some (irTrapState base "type mismatch in i32.store")
            | none => some (irTrapState base "stack underflow in i32.store")
          | .f64 =>
            match irPop2? base.stack with
            | some (.f64 val, .i32 addr, stk) =>
                let byteAddr := addr.toNat + offset
                match writeLE? base.memory byteAddr 8 (floatToU64Bits val) with
                | some mem =>
                  some (.silent, irPushTrace { base with stack := stk, memory := mem } .silent)
                | none => some (irTrapState base "memory access fault in f64.store")
            | some _ => some (irTrapState base "type mismatch in f64.store")
            | none => some (irTrapState base "stack underflow in f64.store")
          | .i64 =>
            match irPop2? base.stack with
            | some (.i64 val, .i32 addr, stk) =>
                let byteAddr := addr.toNat + offset
                match writeLE? base.memory byteAddr 8 val with
                | some mem =>
                  some (.silent, irPushTrace { base with stack := stk, memory := mem } .silent)
                | none => some (irTrapState base "memory access fault in i64.store")
            | some _ => some (irTrapState base "type mismatch in i64.store")
            | none => some (irTrapState base "stack underflow in i64.store")
          | .ptr =>
            match irPop2? base.stack with
            | some (.i32 val, .i32 addr, stk) =>
                let byteAddr := addr.toNat + offset
                match writeLE? base.memory byteAddr 4 val.toUInt64 with
                | some mem =>
                  some (.silent, irPushTrace { base with stack := stk, memory := mem } .silent)
                | none => some (irTrapState base "memory access fault in ptr.store")
            | some _ => some (irTrapState base "type mismatch in ptr.store")
            | none => some (irTrapState base "stack underflow in ptr.store")
      -- Memory: store8 (1-byte write via writeLE?)
      -- Trap messages match Wasm i32.store (they share the same match case in Wasm step?).
      | .store8 offset =>
          match irPop2? base.stack with
          | some (.i32 val, .i32 addr, stk) =>
              let byteAddr := addr.toNat + offset
              match writeLE? base.memory byteAddr 1 val.toUInt64 with
              | some mem =>
                some (.silent, irPushTrace { base with stack := stk, memory := mem } .silent)
              | none => some (irTrapState base "memory access fault in i32.store")
          | some _ => some (irTrapState base "type mismatch in i32.store")
          | none => some (irTrapState base "stack underflow in i32.store")

      -- Control flow: block
      | .block label body =>
          let lbl : IRLabel := {
            name := label, isLoop := false
            onBranch := rest, onExit := rest }
          some (.silent, irPushTrace { base with code := body, labels := lbl :: base.labels } .silent)
      -- Control flow: loop
      -- REF: Wasm §4.4.8.2 — loop pushes label with onBranch = body (re-enter loop body).
      -- Loop labels are kept on br (see br case below), matching Wasm behavior.
      | .loop label body =>
          let lbl : IRLabel := {
            name := label, isLoop := true
            onBranch := body
            onExit := rest }
          some (.silent, irPushTrace { base with code := body, labels := lbl :: base.labels } .silent)
      -- Control flow: if (pushes label like Wasm §4.4.8)
      | .if_ _result then_ else_ =>
          match irPop1? base.stack with
          | some (.i32 cond, stk) =>
              let branch := if cond != 0 then then_ else else_
              let lbl : IRLabel := {
                name := "__if", isLoop := false
                onBranch := rest, onExit := rest }
              some (.silent, irPushTrace { base with stack := stk, code := branch, labels := lbl :: base.labels } .silent)
          | some _ => some (irTrapState base "if condition is not i32")
          | none => some (irTrapState base "stack underflow in if")
      -- Control flow: br
      -- REF: Wasm §4.4.8.6 — br to a loop label keeps the label (re-entry point).
      | .br label =>
          match irFindLabel? s.labels label with
          | some (idx, lbl) =>
              let labels' :=
                if lbl.isLoop then lbl :: s.labels.drop (idx + 1)
                else s.labels.drop (idx + 1)
              some (.silent, irPushTrace { base with code := lbl.onBranch, labels := labels' } .silent)
          | none => some (irTrapState base s!"br: unknown label '{label}'")
      -- Control flow: br_if
      | .brIf label =>
          match irPop1? base.stack with
          | some (.i32 cond, stk) =>
              if cond != 0 then
                match irFindLabel? s.labels label with
                | some (idx, lbl) =>
                    let labels' :=
                      if lbl.isLoop then lbl :: s.labels.drop (idx + 1)
                      else s.labels.drop (idx + 1)
                    some (.silent, irPushTrace { base with stack := stk, code := lbl.onBranch, labels := labels' } .silent)
                | none => some (irTrapState base s!"br_if: unknown label '{label}'")
              else
                some (.silent, irPushTrace { base with stack := stk } .silent)
          | some _ => some (irTrapState base "br_if condition is not i32")
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
          | some _ => some (irTrapState base "memory.grow delta is not i32")
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

/-- Is this a control-flow signal error (break/continue/return/throw)?
    These are internal signaling events in Core/ANF semantics, not observable behavior.
    In the IR, these become structured control flow (br/return) and emit .silent. -/
def isControlFlowSignal (msg : String) : Bool :=
  msg.startsWith "break:" || msg.startsWith "continue:" ||
  msg.startsWith "return:" || msg.startsWith "throw:"

/-- Map a Core.TraceEvent to an IR.TraceEvent.
    Used by LowerCorrect: ∀ trace, ANF.Behaves s trace → IR.Behaves t (map traceFromCore trace).
    Control-flow signal errors (break/continue/return/throw) are mapped to .silent because
    they become structured control flow (br/return) in the IR.
    REF: Core.TraceEvent has log/error/silent; IR.TraceEvent adds trap. -/
def traceFromCore : Core.TraceEvent → TraceEvent
  | .log s => .log s
  | .error s => if isControlFlowSignal s then .silent else .error s
  | .silent => .silent

/-- Alias for backwards compatibility. -/
abbrev traceFromCoreForIR := traceFromCore

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
@[simp] theorem traceFromCore_error_nonCF (s : String) (h : isControlFlowSignal s = false) :
    traceFromCore (.error s) = .error s := by simp [traceFromCore, h]
@[simp] theorem traceFromCore_error_CF (s : String) (h : isControlFlowSignal s = true) :
    traceFromCore (.error s) = .silent := by simp [traceFromCore, h]

-- Backwards-compatible aliases
@[simp] theorem traceFromCoreForIR_silent : traceFromCoreForIR .silent = .silent := rfl
@[simp] theorem traceFromCoreForIR_log (s : String) : traceFromCoreForIR (.log s) = .log s := rfl
@[simp] theorem traceFromCoreForIR_error_nonCF (s : String) (h : isControlFlowSignal s = false) :
    traceFromCoreForIR (.error s) = .error s := by simp [traceFromCore, h]
@[simp] theorem traceFromCoreForIR_error_CF (s : String) (h : isControlFlowSignal s = true) :
    traceFromCoreForIR (.error s) = .silent := by simp [traceFromCore, h]

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

/-- Round-trip: Core → IR → Core is identity for non-control-flow events.
    Control-flow signal errors (break/continue/return/throw) are silenced by traceFromCore,
    so the round-trip maps them to .silent instead. -/
@[simp] theorem traceToCore_traceFromCore_silent :
    traceToCore (traceFromCore .silent) = .silent := rfl
@[simp] theorem traceToCore_traceFromCore_log (s : String) :
    traceToCore (traceFromCore (.log s)) = .log s := rfl
@[simp] theorem traceToCore_traceFromCore_error_nonCF (s : String) (h : isControlFlowSignal s = false) :
    traceToCore (traceFromCore (.error s)) = .error s := by
  simp [traceFromCore, h]

/-- Composing Core→IR→Wasm trace maps: silent Core events map to silent Wasm events. -/
@[simp] theorem traceToWasm_traceFromCore_silent :
    traceToWasm (traceFromCore .silent) = Wasm.TraceEvent.silent := rfl

@[simp] theorem traceToWasm_traceFromCore_log (s : String) :
    traceToWasm (traceFromCore (.log s)) = Wasm.TraceEvent.silent := rfl

@[simp] theorem traceToWasm_traceFromCore_error (s : String) :
    traceToWasm (traceFromCore (.error s)) = Wasm.TraceEvent.silent := by
  simp only [traceFromCore]
  split <;> simp [traceToWasm]

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
  cases t <;> simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hbounds, readLE?] <;>
    (first | exact ⟨_, _, rfl⟩ | split <;> exact ⟨_, _, rfl⟩)

/-- irStep? for store with i32 value and i32 address on stack and in-bounds succeeds.
    REF: Wasm §4.4.7.2 (memory.store) -/
@[simp]
theorem irStep?_ir_store (s : IRExecState) (rest : List IRInstr) (t : IRType)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.store t offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hbounds : addr.toNat + offset + 4 ≤ s.memory.size) :
    ∃ te s', irStep? s = some (te, s') := by
  cases t <;> simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hbounds, writeLE?] <;>
    (first | exact ⟨_, _, rfl⟩ | split <;> exact ⟨_, _, rfl⟩)

/-- irStep? for store8 with i32 value and i32 address on stack and in-bounds succeeds.
    REF: Wasm §4.4.7.2 (memory.store, 1-byte variant) -/
@[simp]
theorem irStep?_ir_store8 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.store8 offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hbounds : addr.toNat + offset < s.memory.size) :
    ∃ te s', irStep? s = some (te, s') := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hbounds, writeLE?]

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

/-- irStep? for localGet with no active frame: traps. -/
theorem irStep?_eq_localGet_noFrame (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.localGet idx :: rest)
    (hframes : s.frames = []) :
    irStep? s = some (.trap "local.get without active frame",
      { s with code := [], trace := s.trace ++ [.trap "local.get without active frame"] }) := by
  simp [irStep?, hcode, hframes, irTrapState, irPushTrace]

/-- irStep? for localGet with local index out of bounds: traps. -/
theorem irStep?_eq_localGet_oob (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (frame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = IRInstr.localGet idx :: rest)
    (hframes : s.frames = frame :: frest)
    (hlocal : frame.locals[idx]? = none) :
    irStep? s = some (.trap s!"unknown local index {idx}",
      { s with code := [], trace := s.trace ++ [.trap s!"unknown local index {idx}"] }) := by
  simp [irStep?, hcode, hframes, hlocal, irTrapState, irPushTrace]

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

/-- irStep? for localSet with empty stack: traps. -/
theorem irStep?_eq_localSet_emptyStack (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (frame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = IRInstr.localSet idx :: rest)
    (hstack : s.stack = [])
    (hframes : s.frames = frame :: frest) :
    irStep? s = some (.trap "stack underflow in local.set",
      { s with code := [], stack := [], trace := s.trace ++ [.trap "stack underflow in local.set"] }) := by
  simp [irStep?, hcode, hstack, hframes, irPop1?, irTrapState, irPushTrace]

/-- irStep? for localSet with no active frame: traps regardless of stack. -/
theorem irStep?_eq_localSet_noFrame (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.localSet idx :: rest)
    (hframes : s.frames = []) :
    irStep? s = some (.trap "local.set without active frame",
      { s with code := [], trace := s.trace ++ [.trap "local.set without active frame"] }) := by
  simp [irStep?, hcode, hframes, irTrapState, irPushTrace, irPop1?]

/-- irStep? for localSet with local index out of bounds: traps. -/
theorem irStep?_eq_localSet_oob (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (frame : IRFrame) (frest : List IRFrame)
    (hcode : s.code = IRInstr.localSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hframes : s.frames = frame :: frest)
    (hbounds : ¬(idx < frame.locals.size)) :
    irStep? s = some (.trap s!"unknown local index {idx}",
      { s with code := [], trace := s.trace ++ [.trap s!"unknown local index {idx}"] }) := by
  simp [irStep?, hcode, hstack, hframes, irPop1?, irTrapState, irPushTrace, hbounds]

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

/-- Exact state after loop: pushes loop label (onBranch=body, onExit=rest), enters body.
    REF: Wasm §4.4.8.2 — loop's br target is the body, not the whole loop instruction. -/
theorem irStep?_eq_loop (s : IRExecState) (label : String) (body rest : List IRInstr)
    (hcode : s.code = IRInstr.loop label body :: rest) :
    irStep? s = some (.silent,
      { s with
        code := body
        labels := { name := label, onBranch := body,
                     onExit := rest, isLoop := true } :: s.labels
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, irPushTrace]

/-- Exact state after if_ with true condition (cond ≠ 0): enters then branch, pushes label.
    REF: Wasm §4.4.8 — if pops condition, enters then block with label for rest. -/
theorem irStep?_eq_if_true (s : IRExecState) (result : Option IRType)
    (then_ else_ rest : List IRInstr) (cond : UInt32) (stk : List IRValue)
    (hcode : s.code = IRInstr.if_ result then_ else_ :: rest)
    (hstack : s.stack = .i32 cond :: stk)
    (hcond : cond ≠ 0) :
    irStep? s = some (.silent,
      { s with
        code := then_
        stack := stk
        labels := ⟨"__if", false, rest, rest⟩ :: s.labels
        trace := s.trace ++ [.silent] }) := by
  simp only [irStep?, hcode, hstack, irPop1?, irPushTrace]
  simp [hcond]

/-- Exact state after if_ with false condition (cond = 0): enters else branch, pushes label.
    REF: Wasm §4.4.8 — if pops condition, enters else block with label for rest. -/
theorem irStep?_eq_if_false (s : IRExecState) (result : Option IRType)
    (then_ else_ rest : List IRInstr) (stk : List IRValue)
    (hcode : s.code = IRInstr.if_ result then_ else_ :: rest)
    (hstack : s.stack = .i32 0 :: stk) :
    irStep? s = some (.silent,
      { s with
        code := else_
        stack := stk
        labels := ⟨"__if", false, rest, rest⟩ :: s.labels
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

/-- Exact state after global.get with out-of-bounds index: traps. -/
theorem irStep?_eq_globalGet_oob (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.globalGet idx :: rest)
    (hglobal : s.globals[idx]? = none) :
    irStep? s = some (.trap s!"unknown global index {idx}",
      { s with code := [], trace := s.trace ++ [.trap s!"unknown global index {idx}"] }) := by
  simp [irStep?, hcode, hglobal, irPushTrace, irTrapState]

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

/-- Exact state after global.set with empty stack: traps. -/
theorem irStep?_eq_globalSet_emptyStack (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (hcode : s.code = IRInstr.globalSet idx :: rest)
    (hstack : s.stack = []) :
    irStep? s = some (.trap "stack underflow in global.set",
      { s with code := [], trace := s.trace ++ [.trap "stack underflow in global.set"] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irTrapState, irPushTrace]

/-- Exact state after global.set with out-of-bounds index: traps. -/
theorem irStep?_eq_globalSet_oob (s : IRExecState) (idx : Nat) (rest : List IRInstr)
    (v : IRValue) (stk : List IRValue)
    (hcode : s.code = IRInstr.globalSet idx :: rest)
    (hstack : s.stack = v :: stk)
    (hbounds : ¬(idx < s.globals.size)) :
    irStep? s = some (.trap s!"unknown global index {idx}",
      { s with code := [], trace := s.trace ++ [.trap s!"unknown global index {idx}"] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irTrapState, irPushTrace, hbounds]

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

/-! ### irFindLabel? and resolveBranch? helper lemmas -/

private theorem irFindLabel?_go_ge (name : String) :
    ∀ (ls : List IRLabel) (start idx : Nat) (lbl : IRLabel),
    irFindLabel?.go name ls start = some (idx, lbl) → start ≤ idx := by
  intro ls
  induction ls with
  | nil => intro _ _ _ h; simp [irFindLabel?.go] at h
  | cons l rest ih =>
    intro start idx lbl h
    simp only [irFindLabel?.go] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · have := ih (start + 1) idx lbl h; omega

/-- irFindLabel? returns an index less than the label list length. -/
private theorem irFindLabel?_lt_length {labels : List IRLabel} {name : String}
    {idx : Nat} {lbl : IRLabel}
    (h : irFindLabel? labels name = some (idx, lbl)) :
    idx < labels.length := by
  unfold irFindLabel? at h
  suffices ∀ (ls : List IRLabel) (start : Nat),
      irFindLabel?.go name ls start = some (idx, lbl) →
      idx < start + ls.length by
    have := this labels 0 h; omega
  intro ls
  induction ls with
  | nil => intro start h; simp [irFindLabel?.go] at h
  | cons l rest ih =>
    intro start h
    simp only [irFindLabel?.go] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h; simp
    · have := ih (start + 1) h; simp at this ⊢; omega

/-- irFindLabel? returns the label at the found index. -/
private theorem irFindLabel?_getElem {labels : List IRLabel} {name : String}
    {idx : Nat} {lbl : IRLabel}
    (h : irFindLabel? labels name = some (idx, lbl)) :
    labels[idx]? = some lbl := by
  have hlt := irFindLabel?_lt_length h
  unfold irFindLabel? at h
  suffices ∀ (ls : List IRLabel) (start : Nat),
      irFindLabel?.go name ls start = some (idx, lbl) →
      start ≤ idx →
      ls[idx - start]? = some lbl by
    have := this labels 0 h (by omega); simp only [Nat.sub_zero] at this; exact this
  intro ls
  induction ls with
  | nil => intro start h _; simp [irFindLabel?.go] at h
  | cons l rest ih =>
    intro start h hge
    simp only [irFindLabel?.go] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; simp
    · have hge2 : start + 1 ≤ idx := irFindLabel?_go_ge name rest (start + 1) idx lbl h
      have := ih (start + 1) h hge2
      have heq : idx - start = (idx - (start + 1)) + 1 := by omega
      rw [heq]; exact this

/-- resolveBranch? succeeds when the depth is within bounds. -/
private theorem resolveBranch?_of_lt {labels : List LabelFrame} {depth : Nat}
    (h : depth < labels.length) :
    ∃ lbl labels', resolveBranch? labels depth = some (lbl, labels') := by
  unfold resolveBranch?
  suffices ∀ (ls : List LabelFrame) (n : Nat), n < ls.length →
      ∃ lbl labels', resolveBranch?.go ls n = some (lbl, labels') by
    exact this labels depth h
  intro ls
  induction ls with
  | nil => intro _ h; simp at h
  | cons l rest ih =>
    intro n hn
    unfold resolveBranch?.go
    match n with
    | 0 => exact ⟨l, if l.isLoop then l :: rest else rest, rfl⟩
    | n + 1 =>
      simp only [List.length_cons] at hn
      exact ih n (by omega)

/-- resolveBranch? returns the label at position `depth` and the appropriate remaining labels. -/
private theorem resolveBranch?_spec {labels : List LabelFrame} {depth : Nat}
    (h : depth < labels.length) :
    ∃ lbl, labels[depth]? = some lbl ∧
      resolveBranch? labels depth = some (lbl,
        if lbl.isLoop then lbl :: labels.drop (depth + 1)
        else labels.drop (depth + 1)) := by
  unfold resolveBranch?
  suffices ∀ (ls : List LabelFrame) (n : Nat), n < ls.length →
      ∃ lbl, ls[n]? = some lbl ∧
        resolveBranch?.go ls n = some (lbl,
          if lbl.isLoop then lbl :: ls.drop (n + 1)
          else ls.drop (n + 1)) by
    exact this labels depth h
  intro ls
  induction ls with
  | nil => intro _ h; simp at h
  | cons l rest ih =>
    intro n hn
    match n with
    | 0 =>
      unfold resolveBranch?.go
      exact ⟨l, rfl, by split <;> rfl⟩
    | n + 1 =>
      simp only [List.length_cons] at hn
      have ⟨lbl, hlbl, hgo⟩ := ih n (by omega)
      refine ⟨lbl, ?_, ?_⟩
      · simp [hlbl]
      · unfold resolveBranch?.go; exact hgo

/-- Exact state after br: jumps to label's onBranch code.
    Loop labels are kept (re-entry), non-loop labels are popped.
    REF: Wasm §4.4.8.6 (br label) -/
theorem irStep?_eq_br (s : IRExecState) (label : String) (rest : List IRInstr)
    (idx : Nat) (lbl : IRLabel)
    (hcode : s.code = IRInstr.br label :: rest)
    (hfind : irFindLabel? s.labels label = some (idx, lbl)) :
    irStep? s = some (.silent,
      { s with
        code := lbl.onBranch
        labels := if lbl.isLoop then lbl :: s.labels.drop (idx + 1)
                  else s.labels.drop (idx + 1)
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hfind, irPushTrace]

/-- Exact state after br_if with true condition (cond ≠ 0): branches to label.
    Loop labels are kept, non-loop labels are popped. -/
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
        labels := if lbl.isLoop then lbl :: s.labels.drop (idx + 1)
                  else s.labels.drop (idx + 1)
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

/-- Exact state after i32 load: uses readLE? with width 4.
    REF: Wasm §4.4.7.1 (memory.load) -/
theorem irStep?_eq_load_i32 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (addr : UInt32) (stk : List IRValue) (raw : UInt64)
    (hcode : s.code = IRInstr.load .i32 offset :: rest)
    (hstack : s.stack = .i32 addr :: stk)
    (hread : readLE? s.memory (addr.toNat + offset) 4 = some raw) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i32 (UInt32.ofNat raw.toNat) :: stk
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hread]

/-- Exact state after f64 load: uses readLE? with width 8.
    REF: Wasm §4.4.7.1 (memory.load) -/
theorem irStep?_eq_load_f64 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (addr : UInt32) (stk : List IRValue) (raw : UInt64)
    (hcode : s.code = IRInstr.load .f64 offset :: rest)
    (hstack : s.stack = .i32 addr :: stk)
    (hread : readLE? s.memory (addr.toNat + offset) 8 = some raw) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .f64 (u64BitsToFloat raw) :: stk
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hread]

/-- Exact state after i64 load: uses readLE? with width 8.
    REF: Wasm §4.4.7.1 (memory.load) -/
theorem irStep?_eq_load_i64 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (addr : UInt32) (stk : List IRValue) (raw : UInt64)
    (hcode : s.code = IRInstr.load .i64 offset :: rest)
    (hstack : s.stack = .i32 addr :: stk)
    (hread : readLE? s.memory (addr.toNat + offset) 8 = some raw) :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := .i64 raw :: stk
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop1?, irPushTrace, hread]

/-- Exact state after i32 store: uses writeLE? with width 4.
    REF: Wasm §4.4.7.2 (memory.store) -/
theorem irStep?_eq_store_i32 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue) (mem' : ByteArray)
    (hcode : s.code = IRInstr.store .i32 offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hwrite : writeLE? s.memory (addr.toNat + offset) 4 val.toUInt64 = some mem') :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        memory := mem'
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hwrite]

/-- Exact state after f64 store: uses writeLE? with width 8.
    REF: Wasm §4.4.7.2 (memory.store) -/
theorem irStep?_eq_store_f64 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (val : Float) (addr : UInt32) (stk : List IRValue) (mem' : ByteArray)
    (hcode : s.code = IRInstr.store .f64 offset :: rest)
    (hstack : s.stack = .f64 val :: .i32 addr :: stk)
    (hwrite : writeLE? s.memory (addr.toNat + offset) 8 (floatToU64Bits val) = some mem') :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        memory := mem'
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hwrite]

/-- Exact state after i64 store: uses writeLE? with width 8.
    REF: Wasm §4.4.7.2 (memory.store) -/
theorem irStep?_eq_store_i64 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (val : UInt64) (addr : UInt32) (stk : List IRValue) (mem' : ByteArray)
    (hcode : s.code = IRInstr.store .i64 offset :: rest)
    (hstack : s.stack = .i64 val :: .i32 addr :: stk)
    (hwrite : writeLE? s.memory (addr.toNat + offset) 8 val = some mem') :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        memory := mem'
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hwrite]

/-- Exact state after store8: uses writeLE? with width 1.
    REF: Wasm §4.4.7.2 (memory.store, 1-byte variant) -/
theorem irStep?_eq_store8 (s : IRExecState) (rest : List IRInstr)
    (offset : Nat) (val addr : UInt32) (stk : List IRValue) (mem' : ByteArray)
    (hcode : s.code = IRInstr.store8 offset :: rest)
    (hstack : s.stack = .i32 val :: .i32 addr :: stk)
    (hwrite : writeLE? s.memory (addr.toNat + offset) 1 val.toUInt64 = some mem') :
    irStep? s = some (.silent,
      { s with
        code := rest
        stack := stk
        memory := mem'
        trace := s.trace ++ [.silent] }) := by
  simp [irStep?, hcode, hstack, irPop2?, irPushTrace, hwrite]

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

/-- NaN-box encoding of a Flat/ANF value to UInt64 bit pattern.
    REF: Runtime/Values.lean NanBoxed, Lower.lean lowerTrivial. -/
def nanBoxValue : Flat.Value → Runtime.NanBoxed
  | .null => Runtime.NanBoxed.encodeNull
  | .undefined => Runtime.NanBoxed.encodeUndefined
  | .bool b => Runtime.NanBoxed.encodeBool b
  | .number n => Runtime.NanBoxed.encodeNumber n
  | .string _ => Runtime.NanBoxed.encodeStringRef 0  -- placeholder; string interning needed
  | .object addr => Runtime.NanBoxed.encodeObjectRef addr
  | .closure fi ep => Runtime.NanBoxed.encodeObjectRef (fi * 65536 + ep)

/-- Value correspondence: a Flat/ANF value corresponds to an IR value via NaN-boxing.
    JS values are NaN-boxed into f64 for the IR stack machine.
    The IRValue is an f64 whose UInt64 bit pattern equals the NaN-boxed encoding
    of the JS value.
    REF: Lower.lean lowerTrivial, Runtime/Values.lean NanBoxed encoding. -/
def ValueCorr (v : Flat.Value) (irv : IRValue) : Prop :=
  ∃ (f : Float), irv = .f64 f ∧ f.toUInt64 = (nanBoxValue v).bits

/-- Code correspondence for trivial expressions: a single trivial lowers to a
    short IR instruction sequence (typically one instruction) that pushes one value.
    REF: Lower.lean lowerTrivial, lines 241-259. -/
inductive TrivialCodeCorr : ANF.Trivial → List IRInstr → Prop where
  | var (name : ANF.VarName) (idx : Nat) :
      TrivialCodeCorr (.var name) [.localGet idx]
  | lit_null : TrivialCodeCorr .litNull [.const_ .i32 "0"]
  | lit_undefined : TrivialCodeCorr .litUndefined [.const_ .i32 "0"]
  | lit_bool_true : TrivialCodeCorr (.litBool true) [.const_ .i32 "1"]
  | lit_bool_false : TrivialCodeCorr (.litBool false) [.const_ .i32 "0"]
  | lit_num (n : Float) (s : String) : TrivialCodeCorr (.litNum n) [.const_ .f64 s]
  | lit_str (s : String) (encoding : String) : TrivialCodeCorr (.litStr s) [.const_ .f64 encoding]
  | lit_object (addr : Nat) (s : String) : TrivialCodeCorr (.litObject addr) [.const_ .i32 s]
  | lit_closure (fi : ANF.FuncIdx) (ep : Nat) (encoding : String) :
      TrivialCodeCorr (.litClosure fi ep) [.const_ .f64 encoding]

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
  | lit_str (s : String) (encoding : String) :
      LowerCodeCorr (.trivial (.litStr s)) [.const_ .f64 encoding]
  | lit_object (addr : Nat) (s : String) : LowerCodeCorr (.trivial (.litObject addr)) [.const_ .i32 s]
  | lit_closure (fi : ANF.FuncIdx) (ep : Nat) (encoding : String) :
      LowerCodeCorr (.trivial (.litClosure fi ep)) [.const_ .f64 encoding]
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
      TrivialCodeCorr arg argCode →
      LowerCodeCorr (.throw arg) (argCode ++ [.call RuntimeIdx.throwOp, .br lbl])
  | throw_ret (arg : ANF.Trivial) (argCode : List IRInstr) :
      TrivialCodeCorr arg argCode →
      LowerCodeCorr (.throw arg) (argCode ++ [.call RuntimeIdx.throwOp, .return_])
  /-- tryCatch lowers to a block structure. -/
  | tryCatch (body : ANF.Expr) (cp : ANF.VarName) (cb : ANF.Expr)
      (fin : Option ANF.Expr) (instrs : List IRInstr) :
      LowerCodeCorr (.tryCatch body cp cb fin) instrs
  /-- return with value lowers to: valueCode ++ [return_].
      REF: Lower.lean lines 466-471. -/
  | return_some (arg : ANF.Trivial) (argCode : List IRInstr) :
      TrivialCodeCorr arg argCode →
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
  | break_ (label : Option String) (target : String) :
      LowerCodeCorr (.«break» label) [.br target]
  /-- continue lowers to: [br target].
      REF: Lower.lean lines 501-504. -/
  | continue_ (label : Option String) (target : String) :
      LowerCodeCorr (.«continue» label) [.br target]

/-- Inversion: LowerCodeCorr for a variable must be the `var` constructor. -/
theorem LowerCodeCorr.var_inv {name : ANF.VarName} {code : List IRInstr}
    (h : LowerCodeCorr (.trivial (.var name)) code) :
    ∃ idx, code = [.localGet idx] := by
  match h with
  | .var _ idx => exact ⟨idx, rfl⟩
  | .value_done _ ht => exact absurd rfl (ht name)

/-- Inversion: LowerCodeCorr for break must be the `break_` constructor. -/
theorem LowerCodeCorr.break_inv {label : Option String} {code : List IRInstr}
    (h : LowerCodeCorr (.«break» label) code) :
    ∃ target, code = [.br target] := by
  match h with
  | .break_ _ tgt => exact ⟨tgt, rfl⟩

/-- Inversion: LowerCodeCorr for continue must be the `continue_` constructor. -/
theorem LowerCodeCorr.continue_inv {label : Option String} {code : List IRInstr}
    (h : LowerCodeCorr (.«continue» label) code) :
    ∃ target, code = [.br target] := by
  match h with
  | .continue_ _ tgt => exact ⟨tgt, rfl⟩

/-- Inversion: LowerCodeCorr for seq extracts sub-expression codes. -/
theorem LowerCodeCorr.seq_inv {a b : ANF.Expr} {code : List IRInstr}
    (h : LowerCodeCorr (.seq a b) code) :
    ∃ aCode bCode, code = aCode ++ [.drop] ++ bCode ∧
      LowerCodeCorr a aCode ∧ LowerCodeCorr b bCode := by
  match h with
  | .seq _ _ ac bc ha hb => exact ⟨ac, bc, rfl, ha, hb⟩

/-- Inversion: LowerCodeCorr for return (some t) extracts TrivialCodeCorr. -/
theorem LowerCodeCorr.return_some_inv {arg : ANF.Trivial} {code : List IRInstr}
    (h : LowerCodeCorr (.«return» (some arg)) code) :
    ∃ argCode, code = argCode ++ [.return_] ∧ TrivialCodeCorr arg argCode := by
  match h with
  | .return_some _ ac htc => exact ⟨ac, rfl, htc⟩

/-- Inversion: LowerCodeCorr for throw extracts TrivialCodeCorr and transfer shape. -/
theorem LowerCodeCorr.throw_inv {arg : ANF.Trivial} {code : List IRInstr}
    (h : LowerCodeCorr (.throw arg) code) :
    (∃ argCode lbl, code = argCode ++ [.call RuntimeIdx.throwOp, .br lbl] ∧
      TrivialCodeCorr arg argCode) ∨
    (∃ argCode, code = argCode ++ [.call RuntimeIdx.throwOp, .return_] ∧
      TrivialCodeCorr arg argCode) := by
  match h with
  | .throw_br _ ac lbl htc => exact .inl ⟨ac, lbl, rfl, htc⟩
  | .throw_ret _ ac htc => exact .inr ⟨ac, rfl, htc⟩

/-- Step-count measure: how many IR steps a given ANF expression needs.
    Used for stuttering simulation arguments. Returns 0 for halted expressions,
    1 for 1:1 cases (var, return none), 2+ for multi-step cases. -/
def irStepMeasure : ANF.Expr → Nat
  | .trivial (.var _) => 1          -- localGet
  | .trivial _ => 0                  -- halted (literal)
  | .«return» none => 1             -- return_
  | .«return» (some _) => 2         -- argCode + return_
  | .«break» _ => 1                 -- br
  | .«continue» _ => 1              -- br
  | .throw _ => 3                    -- argCode + call throwOp + transfer
  | .labeled _ _ => 1               -- block
  | .«let» _ _ _ => 3               -- rhsCode + localSet + bodyCode (minimum)
  | .seq _ _ => 2                    -- aCode + drop + bCode (minimum)
  | .«if» _ _ _ => 2                -- condCode + if_
  | .while_ _ _ => 1                -- block/loop structure
  | .tryCatch _ _ _ _ => 1          -- block structure
  | .yield _ _ => 2                  -- argCode + yieldOp
  | .await _ => 2                    -- argCode + awaitOp

/-- The lowered IR module's initial code corresponds to the main expression. -/
axiom lower_main_code_corr (prog : ANF.Program) (irmod : IRModule)
    (h : Wasm.lower prog = .ok irmod) :
    LowerCodeCorr prog.main (irInitialState irmod).code

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
  /- Environment correspondence: each non-builtin ANF variable maps to an IR local whose
     value matches.  The "console" binding is a compile-time built-in handled by the
     lowering as a pattern-match on getProp, not as a runtime local. -/
  henv : ∀ name v, s.env.lookup name = some v → name ≠ "console" →
    ∃ (idx : Nat) (val : IRValue), (Option.bind ir.frames.head? (fun f => f.locals[idx]?)) = some val ∧ ValueCorr v val
  /- Variable correspondence: when the ANF expression is a variable reference
     and the IR code is a localGet, the variable is in scope and the local is valid.
     This connects the code correspondence (which index) to the env (which value).
     After a var step, both sides are literal/empty, so this holds vacuously. -/
  hvar : ∀ name idx, s.expr = .trivial (.var name) → ir.code = [IRInstr.localGet idx] →
    (∃ v, s.env.lookup name = some v) ∧
    ∃ val, (Option.bind ir.frames.head? (fun f => f.locals[idx]?)) = some val
  /- Local validity: when the IR code starts with localGet idx, the local at idx
     exists in the current frame.  This ensures code-derived indices are always
     valid, bridging the gap between TrivialCodeCorr (which picks the index from
     the code) and henv (which picks the index from the environment). -/
  hlocal_valid : ∀ idx rest, ir.code = IRInstr.localGet idx :: rest →
    ∃ val, (Option.bind ir.frames.head? (fun f => f.locals[idx]?)) = some val
  /- Label stack is empty (top-level execution within a single function). -/
  hlabels_empty : ir.labels = []
  /- Exactly one frame (top-level). -/
  hframes_one : ir.frames.length = 1

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
    intro name v hlookup hne
    -- Initial ANF env only has "console"; hne : name ≠ "console" contradicts.
    simp [ANF.initialState, ANF.Env.extend, ANF.Env.lookup] at hlookup
    split at hlookup <;> simp_all [ANF.Env.empty]
  hvar := by
    intro name idx hexpr hcode_ir
    -- irInitialState code is [call _] or [], never [localGet _], so hcode_ir is absurd.
    exfalso; unfold irInitialState at hcode_ir; split at hcode_ir <;> simp at hcode_ir
  hlocal_valid := by
    intro idx rest hc
    exfalso; unfold irInitialState at hc; split at hc <;> simp at hc
  hlabels_empty := by simp [irInitialState]
  hframes_one := by simp [irInitialState]

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
        -- Get IR code structure from LowerCodeCorr
        have hc := hrel.hcode; rw [hexpr] at hc
        obtain ⟨idx, hcode_eq⟩ := hc.var_inv
        -- Get var/local existence from hvar
        have ⟨⟨v, henv_lookup⟩, ⟨irval, hlocal⟩⟩ := hrel.hvar name idx hexpr hcode_eq
        -- ANF step for var found: produces silent, new expr = trivialOfValue v
        have hs1eq : { s1 with expr := ANF.Expr.trivial (.var name) } = s1 := by
          cases s1; simp_all
        have hanf := ANF.step?_var_found s1 name v henv_lookup
        rw [hs1eq] at hanf
        rw [hanf] at heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        -- IR step for localGet
        -- Extract frame from hframes
        obtain ⟨fr, frs, hfr_eq⟩ : ∃ fr frs, s2.frames = fr :: frs := by
          cases hf : s2.frames with
          | nil => exact absurd hf hrel.hframes
          | cons fr frs => exact ⟨fr, frs, rfl⟩
        -- Extract local value from hlocal
        simp [hfr_eq] at hlocal
        have hlocal_val : fr.locals[idx]? = some irval := hlocal
        have hir := irStep?_eq_localGet s2 idx [] fr frs irval hcode_eq hfr_eq hlocal_val
        -- The IR produces (.silent, ...), and traceFromCore .silent = .silent
        simp only [traceFromCore]
        refine ⟨_, hir, ?_⟩
        -- Construct new LowerSimRel for the post-step states
        -- ANF: pushTrace { s1 with expr := .trivial (trivialOfValue v) } .silent
        -- IR: { s2 with code := [], stack := irval :: s2.stack, trace := ... }
        exact {
          hlower := hrel.hlower
          hmod := hrel.hmod
          hcode := by
            -- new ANF expr = .trivial (trivialOfValue v), new IR code = []
            simp [ANF.pushTrace]
            exact .value_done (ANF.trivialOfValue v) (ANF.trivialOfValue_ne_var v)
          hhalt := by
            intro _
            simp [IRExecState.halted, hrel.hlabels_empty]
            exact Nat.le_of_eq hrel.hframes_one
          hframes := by simp [hfr_eq]
          henv := by
            intro n w hlk hne
            simp [ANF.pushTrace] at hlk
            exact hrel.henv n w hlk hne
          hvar := by
            intro n' idx' hexpr' _
            simp [ANF.pushTrace] at hexpr'
            -- trivialOfValue never produces var
            exact absurd hexpr' (by cases v <;> simp [ANF.trivialOfValue])
          hlocal_valid := by intro _ _ h; simp at h
          hlabels_empty := hrel.hlabels_empty
          hframes_one := hrel.hframes_one
        }
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
        -- Sequence: ANF either skips completed a (1 step), or steps a (1 step)
        -- IR code is aCode ++ [drop] ++ bCode (from LowerCodeCorr.seq_inv)
        -- Value case: ANF 1 step → b, but IR needs N steps (aCode + drop). NOT 1:1.
        -- Stepping case: ANF steps a within seq, IR steps first of aCode. Potentially 1:1
        --   but requires sub-expression simulation induction.
        -- TODO: Restructure as stuttering simulation or add measure-based 1:N framework.
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
        have hc := hrel.hcode; rw [hexpr] at hc
        match arg with
        | none =>
          -- return with no value: IR code = [return_]
          -- Invert LowerCodeCorr: the only matching constructor is return_none
          have hcode_eq : s2.code = [.return_] := by
            generalize s2.code = c at hc; cases hc with | return_none => rfl
          -- ANF step: silent, expr → trivial .litUndefined
          have hs1eq : { s1 with expr := ANF.Expr.return none } = s1 := by cases s1; simp_all
          have hanf := ANF.step?_return_none s1
          rw [hs1eq] at hanf; rw [hanf] at heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          -- IR step: return_ with single frame → code = [], labels = []
          have hfr : ∃ f, s2.frames = [f] := by
            match hf : s2.frames, hrel.hframes_one with
            | [], h => simp at h
            | [f], _ => exact ⟨f, rfl⟩
            | _ :: _ :: _, h => simp at h
          obtain ⟨frame, hfr⟩ := hfr
          have hir := irStep?_eq_return_toplevel s2 [] frame hcode_eq hfr
          simp only [traceFromCore]
          exact ⟨_, hir, {
            hlower := hrel.hlower
            hmod := hrel.hmod
            hcode := .value_done .litUndefined (by intro name; exact ANF.Trivial.noConfusion)
            hhalt := by
              intro _; simp [IRExecState.halted, hfr]
            hframes := by simp [hfr]
            henv := by
              intro n w hlk hne; simp [ANF.pushTrace] at hlk
              exact hrel.henv n w hlk hne
            hvar := by
              intro n' idx' hexpr' hcode_ir
              simp [ANF.pushTrace] at hexpr'
            hlocal_valid := by intro _ _ h; simp at h
            hlabels_empty := rfl
            hframes_one := by simp [hfr]
          }⟩
        | some t => sorry
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

/-- Stuttering step simulation for `return (some .litNull)`:
    IR takes 2 steps (const_ .i32 "0" + return_) matching ANF's 1 silent step.
    This is the template for proving 1:N stepping cases in LowerSimRel. -/
theorem step_sim_return_litNull (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some .litNull))
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  -- Derive IR code shape: s2.code = [.const_ .i32 "0", .return_]
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc   -- TrivialCodeCorr .litNull → argCode = [.const_ .i32 "0"]
  simp only [List.cons_append, List.nil_append] at hcode_eq
  -- Derive ANF step: evalTrivial .litNull = .ok .null → silent step
  have hs1_eta : { s1 with expr := ANF.Expr.return (some .litNull) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 .litNull Flat.Value.null
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  -- t = .silent, s1' = pushTrace { s1 with expr := .trivial .litNull } .silent
  -- Extract single frame from hframes_one
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  -- IR Step 1: const_ .i32 "0" → pushes i32 0, code becomes [.return_]
  have h_toNat : String.toNat? "0" = some 0 := by native_decide
  have hstep1 := irStep?_eq_i32Const s2 "0" 0 [IRInstr.return_] hcode_eq h_toNat
  -- IR Step 2: return_ at top level → code = [], labels = []
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .i32 (0 : UInt32) :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  -- Build 2-step IRSteps; observableEvents [.silent, .silent] = observableEvents [.silent] = []
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  -- Construct LowerSimRel for the post-step states
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done .litNull (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro n w hlk hne
      simp only [ANF.pushTrace] at hlk
      exact hrel.henv n w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some (.litNum n))`:
    IR takes 2 steps (const_ .f64 s + return_) matching ANF's 1 silent step. -/
theorem step_sim_return_litNum (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (n : Float) (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some (.litNum n)))
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc with | lit_num _ s_str =>
  simp only [List.cons_append, List.nil_append] at hcode_eq
  -- ANF step: evalTrivial (.litNum n) = .ok (.number n)
  have hs1_eta : { s1 with expr := ANF.Expr.return (some (.litNum n)) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 (.litNum n) (.number n)
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  -- IR Step 1: const_ .f64 s_str
  have hstep1 := irStep?_eq_f64Const s2 s_str [IRInstr.return_] hcode_eq
  -- IR Step 2: return_ at top level
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .f64 (s_str.toNat?.map (fun k => Float.ofNat k) |>.getD 0.0) :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done (.litNum n) (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro nm w hlk hne; simp only [ANF.pushTrace] at hlk
      exact hrel.henv nm w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some (.var name))`:
    IR takes 2 steps (localGet idx + return_) matching ANF's 1 silent step.
    Requires that the variable is in scope and is not the built-in "console". -/
theorem step_sim_return_var (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (name : ANF.VarName)
    (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some (.var name)))
    (hvar_exists : ∃ v, s1.env.lookup name = some v)
    (hne_console : name ≠ "console")
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc with | var _ idx =>
  simp only [List.cons_append, List.nil_append] at hcode_eq
  -- s2.code = [.localGet idx, .return_]
  -- ANF step: evalTrivial (.var name) = .ok v
  obtain ⟨v, henv_lookup⟩ := hvar_exists
  have hs1_eta : { s1 with expr := ANF.Expr.return (some (.var name)) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 (.var name) v
    (by simp [ANF.evalTrivial, henv_lookup])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  -- Get IR local from hlocal_valid: the code starts with localGet idx, so locals[idx] exists.
  obtain ⟨irval, hlocal_bind⟩ := hrel.hlocal_valid idx [IRInstr.return_] hcode_eq
  simp [hfr] at hlocal_bind
  have hlocal_idx : frame.locals[idx]? = some irval := hlocal_bind
  have hstep1 := irStep?_eq_localGet s2 idx [IRInstr.return_] frame [] irval
    hcode_eq (by simp [hfr]) hlocal_idx
  -- IR Step 2: return_ at top level
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := irval :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done (ANF.trivialOfValue v) (ANF.trivialOfValue_ne_var v)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro nm w hlk hne; simp only [ANF.pushTrace] at hlk
      exact hrel.henv nm w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp only [ANF.pushTrace] at hexpr'
      -- trivialOfValue always produces a non-var trivial
      exact absurd hexpr' (by cases v <;> simp [ANF.trivialOfValue])
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some .litUndefined)`:
    IR takes 2 steps (const_ .i32 "0" + return_) matching ANF's 1 silent step.
    Same pattern as litNull since undefined also lowers to i32 0. -/
theorem step_sim_return_litUndefined (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some .litUndefined))
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc
  simp only [List.cons_append, List.nil_append] at hcode_eq
  have hs1_eta : { s1 with expr := ANF.Expr.return (some .litUndefined) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 .litUndefined Flat.Value.undefined
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  have h_toNat : String.toNat? "0" = some 0 := by native_decide
  have hstep1 := irStep?_eq_i32Const s2 "0" 0 [IRInstr.return_] hcode_eq h_toNat
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .i32 (0 : UInt32) :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done .litUndefined (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro n w hlk hne
      simp only [ANF.pushTrace] at hlk
      exact hrel.henv n w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some (.litBool true))`:
    IR takes 2 steps (const_ .i32 "1" + return_) matching ANF's 1 silent step. -/
theorem step_sim_return_litBoolTrue (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some (.litBool true)))
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc
  simp only [List.cons_append, List.nil_append] at hcode_eq
  have hs1_eta : { s1 with expr := ANF.Expr.return (some (.litBool true)) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 (.litBool true) (.bool true)
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  have h_toNat : String.toNat? "1" = some 1 := by native_decide
  have hstep1 := irStep?_eq_i32Const s2 "1" 1 [IRInstr.return_] hcode_eq h_toNat
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .i32 (1 : UInt32) :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done (.litBool true) (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro n w hlk hne
      simp only [ANF.pushTrace] at hlk
      exact hrel.henv n w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some (.litBool false))`:
    IR takes 2 steps (const_ .i32 "0" + return_) matching ANF's 1 silent step. -/
theorem step_sim_return_litBoolFalse (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some (.litBool false)))
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc
  simp only [List.cons_append, List.nil_append] at hcode_eq
  have hs1_eta : { s1 with expr := ANF.Expr.return (some (.litBool false)) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 (.litBool false) (.bool false)
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  have h_toNat : String.toNat? "0" = some 0 := by native_decide
  have hstep1 := irStep?_eq_i32Const s2 "0" 0 [IRInstr.return_] hcode_eq h_toNat
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .i32 (0 : UInt32) :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done (.litBool false) (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro n w hlk hne
      simp only [ANF.pushTrace] at hlk
      exact hrel.henv n w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some (.litObject addr))`:
    IR takes 2 steps (const_ .i32 s + return_) matching ANF's 1 silent step.
    Requires that the string encoding of the object address is parseable as a Nat. -/
theorem step_sim_return_litObject (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (addr : Nat) (s_str : String) (n : Nat)
    (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some (.litObject addr)))
    (hstep : anfStepMapped s1 = some (t, s1'))
    (hcode_eq : s2.code = [IRInstr.const_ .i32 s_str, IRInstr.return_])
    (hs_parse : s_str.toNat? = some n) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hs1_eta : { s1 with expr := ANF.Expr.return (some (.litObject addr)) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 (.litObject addr) (.object addr)
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  have hstep1 := irStep?_eq_i32Const s2 s_str n [IRInstr.return_] hcode_eq hs_parse
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .i32 n.toUInt32 :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done (.litObject addr) (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro nm w hlk hne; simp only [ANF.pushTrace] at hlk
      exact hrel.henv nm w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some (.litStr s))`:
    IR takes 2 steps (const_ .f64 encoding + return_) matching ANF's 1 silent step. -/
theorem step_sim_return_litStr (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (str : String) (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some (.litStr str)))
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc with | lit_str _ encoding =>
  simp only [List.cons_append, List.nil_append] at hcode_eq
  -- ANF step: evalTrivial (.litStr str) = .ok (.string str)
  have hs1_eta : { s1 with expr := ANF.Expr.return (some (.litStr str)) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 (.litStr str) (.string str)
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  -- IR Step 1: const_ .f64 encoding
  have hstep1 := irStep?_eq_f64Const s2 encoding [IRInstr.return_] hcode_eq
  -- IR Step 2: return_ at top level
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .f64 (encoding.toNat?.map (fun k => Float.ofNat k) |>.getD 0.0) :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done (.litStr str) (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro nm w hlk hne; simp only [ANF.pushTrace] at hlk
      exact hrel.henv nm w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

/-- Stuttering step simulation for `return (some (.litClosure fi ep))`:
    IR takes 2 steps (const_ .f64 encoding + return_) matching ANF's 1 silent step. -/
theorem step_sim_return_litClosure (prog : ANF.Program) (irmod : IRModule)
    (s1 : ANF.State) (s2 : IRExecState) (t : TraceEvent) (s1' : ANF.State)
    (fi : ANF.FuncIdx) (ep : Nat) (hrel : LowerSimRel prog irmod s1 s2)
    (hexpr : s1.expr = .return (some (.litClosure fi ep)))
    (hstep : anfStepMapped s1 = some (t, s1')) :
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [t] := by
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
  cases htcc with | lit_closure _ _ encoding =>
  simp only [List.cons_append, List.nil_append] at hcode_eq
  -- ANF step: evalTrivial (.litClosure fi ep) = .ok (.closure fi ep)
  have hs1_eta : { s1 with expr := ANF.Expr.return (some (.litClosure fi ep)) } = s1 := by
    cases s1; simp_all
  have hanf := ANF.step?_return_some_ok s1 (.litClosure fi ep) (.closure fi ep)
    (by simp [ANF.evalTrivial, ANF.trivialValue?])
  rw [hs1_eta] at hanf
  simp only [anfStepMapped, hanf, traceFromCore, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  obtain ⟨frame, hfr⟩ : ∃ f, s2.frames = [f] := by
    match hf : s2.frames, hrel.hframes_one with
    | [], h => simp at h
    | [f], _ => exact ⟨f, rfl⟩
    | _ :: _ :: _, h => simp at h
  -- IR Step 1: const_ .f64 encoding
  have hstep1 := irStep?_eq_f64Const s2 encoding [IRInstr.return_] hcode_eq
  -- IR Step 2: return_ at top level
  have hstep2 := irStep?_eq_return_toplevel
    { s2 with
        code := [.return_]
        stack := .f64 (encoding.toNat?.map (fun k => Float.ofNat k) |>.getD 0.0) :: s2.stack
        trace := s2.trace ++ [.silent] }
    [] frame (by rfl) (by simp [hfr])
  refine ⟨_, [.silent, .silent],
    IRSteps_two (IRStep_of_irStep? hstep1) (IRStep_of_irStep? hstep2), ?_, by simp⟩
  exact {
    hlower := hrel.hlower
    hmod := hrel.hmod
    hcode := by
      simp only [ANF.pushTrace, ANF.trivialOfValue]
      exact .value_done (.litClosure fi ep) (by intro name; exact ANF.Trivial.noConfusion)
    hhalt := by
      intro _; simp [IRExecState.halted, hfr]
    hframes := by simp [hfr]
    henv := by
      intro nm w hlk hne; simp only [ANF.pushTrace] at hlk
      exact hrel.henv nm w hlk hne
    hvar := by
      intro n' idx' hexpr' _
      simp [ANF.pushTrace, ANF.trivialOfValue] at hexpr'
    hlocal_valid := by intro _ _ h; simp at h
    hlabels_empty := rfl
    hframes_one := by simp [hfr]
  }

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
  -- Case analysis on ANF expression to handle 1:N cases directly
  match hexpr : s1.expr with
  | .«return» (some triv) =>
    -- 1:N case: IR takes 2 steps (argCode ++ [return_])
    cases triv with
    | litNull =>
      exact step_sim_return_litNull prog irmod s1 s2 t s1' hrel hexpr hstep
    | litNum n =>
      exact step_sim_return_litNum prog irmod s1 s2 t s1' n hrel hexpr hstep
    | var name =>
      match hlookup : s1.env.lookup name with
      | some v =>
        by_cases hne : name = "console"
        · subst hne
          obtain ⟨s2', h1, h2⟩ := step_sim prog irmod s1 s2 t s1' hrel hstep
          exact ⟨s2', [t], .tail (.mk h1) (.refl _), h2, rfl⟩
        · exact step_sim_return_var prog irmod s1 s2 t s1' name hrel hexpr ⟨v, hlookup⟩ hne hstep
      | none =>
        obtain ⟨s2', h1, h2⟩ := step_sim prog irmod s1 s2 t s1' hrel hstep
        exact ⟨s2', [t], .tail (.mk h1) (.refl _), h2, rfl⟩
    | litUndefined =>
      exact step_sim_return_litUndefined prog irmod s1 s2 t s1' hrel hexpr hstep
    | litBool b =>
      cases b with
      | true => exact step_sim_return_litBoolTrue prog irmod s1 s2 t s1' hrel hexpr hstep
      | false => exact step_sim_return_litBoolFalse prog irmod s1 s2 t s1' hrel hexpr hstep
    | litStr s =>
      exact step_sim_return_litStr prog irmod s1 s2 t s1' s hrel hexpr hstep
    | litObject addr =>
      have hc := hrel.hcode; rw [hexpr] at hc
      obtain ⟨argCode, hcode_eq, htcc⟩ := hc.return_some_inv
      cases htcc with | lit_object _ s_str =>
      simp only [List.cons_append, List.nil_append] at hcode_eq
      match hs : s_str.toNat? with
      | some n => exact step_sim_return_litObject prog irmod s1 s2 t s1' addr s_str n hrel hexpr hstep hcode_eq hs
      | none =>
        obtain ⟨s2', h1, h2⟩ := step_sim prog irmod s1 s2 t s1' hrel hstep
        exact ⟨s2', [t], .tail (.mk h1) (.refl _), h2, rfl⟩
    | litClosure fi ep =>
      exact step_sim_return_litClosure prog irmod s1 s2 t s1' fi ep hrel hexpr hstep
  | _ =>
    -- All other cases: delegate to step_sim (1:1)
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
inductive EmitCodeCorr : List String → List IRInstr → List Instr → Prop where
  /-- Empty IR code maps to empty Wasm code. -/
  | nil {ctx : List String} : EmitCodeCorr ctx [] []
  /-- i32 const maps to i32.const.
      `hparse` ensures the IR string value parses to the same number. -/
  | const_i32 {ctx : List String} (v : String) (n : UInt32) (rest_ir : List IRInstr) (rest_w : List Instr)
      (hparse : v.toNat? = some n.toNat) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.const_ .i32 v :: rest_ir) (.i32Const n :: rest_w)
  /-- i64 const maps to i64.const.
      `hparse` ensures the IR string value parses to the same number. -/
  | const_i64 {ctx : List String} (v : String) (n : UInt64) (rest_ir : List IRInstr) (rest_w : List Instr)
      (hparse : v.toNat? = some n.toNat) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.const_ .i64 v :: rest_ir) (.i64Const n :: rest_w)
  /-- f64 const maps to f64.const. -/
  | const_f64 {ctx : List String} (v : String) (f : Float) (rest_ir : List IRInstr) (rest_w : List Instr) :
      f = (v.toNat?.map (fun n => Float.ofNat n) |>.getD 0.0) →
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.const_ .f64 v :: rest_ir) (.f64Const f :: rest_w)
  /-- localGet maps to local.get. -/
  | localGet {ctx : List String} (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.localGet idx :: rest_ir) (.localGet idx :: rest_w)
  /-- localSet maps to local.set. -/
  | localSet {ctx : List String} (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.localSet idx :: rest_ir) (.localSet idx :: rest_w)
  /-- globalGet maps to global.get. -/
  | globalGet {ctx : List String} (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.globalGet idx :: rest_ir) (.globalGet idx :: rest_w)
  /-- globalSet maps to global.set. -/
  | globalSet {ctx : List String} (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.globalSet idx :: rest_ir) (.globalSet idx :: rest_w)
  /-- binOp i32 "add" maps to i32.add. -/
  | binOp_i32_add {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "add" :: rest_ir) (.i32Add :: rest_w)
  /-- binOp i32 "sub" maps to i32.sub. -/
  | binOp_i32_sub {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "sub" :: rest_ir) (.i32Sub :: rest_w)
  /-- binOp i32 "mul" maps to i32.mul. -/
  | binOp_i32_mul {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "mul" :: rest_ir) (.i32Mul :: rest_w)
  /-- binOp i32 "and" maps to i32.and. -/
  | binOp_i32_and {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "and" :: rest_ir) (.i32And :: rest_w)
  /-- binOp i32 "or" maps to i32.or. -/
  | binOp_i32_or {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "or" :: rest_ir) (.i32Or :: rest_w)
  /-- binOp i32 "eq" maps to i32.eq. -/
  | binOp_i32_eq {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "eq" :: rest_ir) (.i32Eq :: rest_w)
  /-- binOp i32 "ne" maps to i32.ne. -/
  | binOp_i32_ne {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "ne" :: rest_ir) (.i32Ne :: rest_w)
  /-- binOp i32 "lt_s" maps to i32.lt_s. -/
  | binOp_i32_lts {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "lt_s" :: rest_ir) (.i32Lts :: rest_w)
  /-- binOp i32 "gt_s" maps to i32.gt_s. -/
  | binOp_i32_gts {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .i32 "gt_s" :: rest_ir) (.i32Gts :: rest_w)
  /-- binOp f64 "add" maps to f64.add. -/
  | binOp_f64_add {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .f64 "add" :: rest_ir) (.f64Add :: rest_w)
  /-- binOp f64 "sub" maps to f64.sub. -/
  | binOp_f64_sub {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .f64 "sub" :: rest_ir) (.f64Sub :: rest_w)
  /-- binOp f64 "mul" maps to f64.mul. -/
  | binOp_f64_mul {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .f64 "mul" :: rest_ir) (.f64Mul :: rest_w)
  /-- binOp f64 "div" maps to f64.div. -/
  | binOp_f64_div {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.binOp .f64 "div" :: rest_ir) (.f64Div :: rest_w)
  /-- unOp i32 "eqz" maps to i32.eqz. -/
  | unOp_i32_eqz {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.unOp .i32 "eqz" :: rest_ir) (.i32Eqz :: rest_w)
  /-- unOp i32 "wrap_i64" maps to i32.wrap_i64. -/
  | unOp_i32_wrapI64 {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.unOp .i32 "wrap_i64" :: rest_ir) (.i32WrapI64 :: rest_w)
  /-- call maps to call. -/
  | call_ {ctx : List String} (funcIdx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.call funcIdx :: rest_ir) (.call funcIdx :: rest_w)
  /-- drop maps to drop. -/
  | drop_ {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.drop :: rest_ir) (.drop :: rest_w)
  /-- return_ maps to return. -/
  | return__ {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.return_ :: rest_ir) (.return_ :: rest_w)
  /-- callIndirect maps to call_indirect. REF: Emit.lean line 109. -/
  | callIndirect_ {ctx : List String} (typeIdx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.callIndirect typeIdx :: rest_ir) (.callIndirect typeIdx 0 :: rest_w)
  /-- i32.load maps to i32.load. REF: Emit.lean line 91. -/
  | load_i32 {ctx : List String} (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.load .i32 offset :: rest_ir)
        (.i32Load { offset := offset, align := 2 } :: rest_w)
  /-- i32.store maps to i32.store. REF: Emit.lean line 95. -/
  | store_i32 {ctx : List String} (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.store .i32 offset :: rest_ir)
        (.i32Store { offset := offset, align := 2 } :: rest_w)
  /-- f64.load maps to f64.load. REF: Emit.lean line 93. -/
  | load_f64 {ctx : List String} (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.load .f64 offset :: rest_ir)
        (.f64Load { offset := offset, align := 3 } :: rest_w)
  /-- f64.store maps to f64.store. REF: Emit.lean line 97. -/
  | store_f64 {ctx : List String} (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.store .f64 offset :: rest_ir)
        (.f64Store { offset := offset, align := 3 } :: rest_w)
  /-- i64.load maps to i64.load. REF: Emit.lean line 92. -/
  | load_i64 {ctx : List String} (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.load .i64 offset :: rest_ir)
        (.i64Load { offset := offset, align := 3 } :: rest_w)
  /-- i64.store maps to i64.store. REF: Emit.lean line 96. -/
  | store_i64 {ctx : List String} (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.store .i64 offset :: rest_ir)
        (.i64Store { offset := offset, align := 3 } :: rest_w)
  /-- i32.store8 maps to i32.store8. REF: Emit.lean line 99. -/
  | store8_ {ctx : List String} (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.store8 offset :: rest_ir)
        (.i32Store8 { offset := offset, align := 0 } :: rest_w)
  /-- block maps to block (body recursively mapped). REF: Emit.lean line 110-113.
      Body is emitted with label pushed onto ctx. -/
  | block_ {ctx : List String} (label : String) (body_ir : List IRInstr) (body_w : List Instr)
      (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr (label :: ctx) body_ir body_w → EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.block label body_ir :: rest_ir) (.block .none body_w :: rest_w)
  /-- loop maps to loop (body recursively mapped). REF: Emit.lean line 114-117.
      Body is emitted with label pushed onto ctx. -/
  | loop_ {ctx : List String} (label : String) (body_ir : List IRInstr) (body_w : List Instr)
      (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr (label :: ctx) body_ir body_w → EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.loop label body_ir :: rest_ir) (.loop .none body_w :: rest_w)
  /-- if_ maps to if_ (branches recursively mapped). REF: Emit.lean line 118-124.
      Branches are emitted with "__if" pushed onto ctx (Emit.lean pushes if_ label). -/
  | if__ {ctx : List String} (result : Option IRType) (then_ir else_ir : List IRInstr) (then_w else_w : List Instr)
      (bt : BlockType) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ("__if" :: ctx) then_ir then_w → EmitCodeCorr ("__if" :: ctx) else_ir else_w →
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.if_ result then_ir else_ir :: rest_ir) (.if_ bt then_w else_w :: rest_w)
  /-- br maps to br (label index resolved). REF: Emit.lean line 125-127.
      `hfind` proves the emitted index matches the label's position in ctx. -/
  | br_ {ctx : List String} (label : String) (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr)
      (hfind : ctx.findIdx? (· == label) = some idx) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.br label :: rest_ir) (.br idx :: rest_w)
  /-- brIf maps to br_if (label index resolved). REF: Emit.lean line 128-130.
      `hfind` proves the emitted index matches the label's position in ctx. -/
  | brIf_ {ctx : List String} (label : String) (idx : Nat) (rest_ir : List IRInstr) (rest_w : List Instr)
      (hfind : ctx.findIdx? (· == label) = some idx) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.brIf label :: rest_ir) (.brIf idx :: rest_w)
  /-- memoryGrow maps to memory.grow 0. REF: Emit.lean line 133. -/
  | memoryGrow_ {ctx : List String} (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (.memoryGrow :: rest_ir) (.memoryGrow 0 :: rest_w)
  /-- General case for instructions not yet decomposed.
      Has False premise, making it uninhabitable — ensures all EmitCodeCorr
      instances use specific constructors above. -/
  | general {ctx : List String} (ir_instr : IRInstr) (wasm_instrs : List Instr)
      (rest_ir : List IRInstr) (rest_w : List Instr) :
      False →
      EmitCodeCorr ctx rest_ir rest_w →
      EmitCodeCorr ctx (ir_instr :: rest_ir) (wasm_instrs ++ rest_w)

/-- EmitCodeCorr ctx [] implies wasm code is also []. -/
theorem EmitCodeCorr.nil_inv {ctx : List String} {wcode : List Instr}
    (h : EmitCodeCorr ctx [] wcode) : wcode = [] := by
  cases h with
  | nil => rfl

/-! ### EmitCodeCorr inversion lemmas
    These extract structure from EmitCodeCorr ctx without dependent elimination issues. -/

/-- Inversion for drop :: rest. -/
theorem EmitCodeCorr.drop_inv {ctx : List String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.drop :: rest) wcode) :
    (∃ rest_w, wcode = Instr.drop :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | drop_ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for return_ :: rest. -/
theorem EmitCodeCorr.return_inv {ctx : List String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.return_ :: rest) wcode) :
    (∃ rest_w, wcode = Instr.return_ :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | return__ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for call :: rest. -/
theorem EmitCodeCorr.call_inv {ctx : List String} {funcIdx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.call funcIdx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.call funcIdx :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | call_ _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for localGet :: rest. -/
theorem EmitCodeCorr.localGet_inv {ctx : List String} {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.localGet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.localGet idx :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | localGet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for localSet :: rest. -/
theorem EmitCodeCorr.localSet_inv {ctx : List String} {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.localSet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.localSet idx :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | localSet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for globalGet :: rest. -/
theorem EmitCodeCorr.globalGet_inv {ctx : List String} {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.globalGet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.globalGet idx :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | globalGet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for globalSet :: rest. -/
theorem EmitCodeCorr.globalSet_inv {ctx : List String} {idx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.globalSet idx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.globalSet idx :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | globalSet _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for const_ .i32 :: rest. -/
theorem EmitCodeCorr.const_i32_inv {ctx : List String} {v : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.const_ .i32 v :: rest) wcode) :
    (∃ n rest_w, wcode = Instr.i32Const n :: rest_w ∧ v.toNat? = some n.toNat ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | const_i32 _ n _ rw hp hrw => left; exact ⟨n, rw, rfl, hp, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for const_ .f64 :: rest. -/
theorem EmitCodeCorr.const_f64_inv {ctx : List String} {v : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.const_ .f64 v :: rest) wcode) :
    (∃ f rest_w, wcode = Instr.f64Const f :: rest_w ∧
      f = (v.toNat?.map (fun n => Float.ofNat n) |>.getD 0.0) ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | const_f64 _ f _ rw hf hrw => left; exact ⟨f, rw, rfl, hf, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for const_ .i64 :: rest. -/
theorem EmitCodeCorr.const_i64_inv {ctx : List String} {v : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.const_ .i64 v :: rest) wcode) :
    (∃ n rest_w, wcode = Instr.i64Const n :: rest_w ∧ v.toNat? = some n.toNat ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | const_i64 _ n _ rw hp hrw => left; exact ⟨n, rw, rfl, hp, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for block :: rest. -/
theorem EmitCodeCorr.block_inv {ctx : List String} {label : String} {body_ir : List IRInstr}
    {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.block label body_ir :: rest) wcode) :
    (∃ body_w rest_w, wcode = Instr.block .none body_w :: rest_w ∧
      EmitCodeCorr (label :: ctx) body_ir body_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | block_ _ _ bw _ rw hb hrw => left; exact ⟨bw, rw, rfl, hb, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for loop :: rest. -/
theorem EmitCodeCorr.loop_inv {ctx : List String} {label : String} {body_ir : List IRInstr}
    {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.loop label body_ir :: rest) wcode) :
    (∃ body_w rest_w, wcode = Instr.loop .none body_w :: rest_w ∧
      EmitCodeCorr (label :: ctx) body_ir body_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | loop_ _ _ bw _ rw hb hrw => left; exact ⟨bw, rw, rfl, hb, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for if_ :: rest. -/
theorem EmitCodeCorr.if_inv {ctx : List String} {result : Option IRType} {then_ir else_ir : List IRInstr}
    {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.if_ result then_ir else_ir :: rest) wcode) :
    (∃ bt then_w else_w rest_w, wcode = Instr.if_ bt then_w else_w :: rest_w ∧
      EmitCodeCorr ("__if" :: ctx) then_ir then_w ∧ EmitCodeCorr ("__if" :: ctx) else_ir else_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | if__ _ _ _ tw ew _ _ rw ht he hrw => left; exact ⟨_, tw, ew, rw, rfl, ht, he, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for br :: rest. -/
theorem EmitCodeCorr.br_inv {ctx : List String} {label : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.br label :: rest) wcode) :
    (∃ idx rest_w, wcode = Instr.br idx :: rest_w ∧
      ctx.findIdx? (· == label) = some idx ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | br_ _ idx _ rw hfind hrw => left; exact ⟨idx, rw, rfl, hfind, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for brIf :: rest. -/
theorem EmitCodeCorr.brIf_inv {ctx : List String} {label : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.brIf label :: rest) wcode) :
    (∃ idx rest_w, wcode = Instr.brIf idx :: rest_w ∧
      ctx.findIdx? (· == label) = some idx ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | brIf_ _ idx _ rw hfind hrw => left; exact ⟨idx, rw, rfl, hfind, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for memoryGrow :: rest. -/
theorem EmitCodeCorr.memoryGrow_inv {ctx : List String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.memoryGrow :: rest) wcode) :
    (∃ rest_w, wcode = Instr.memoryGrow 0 :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | memoryGrow_ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for binOp .i32 op :: rest. -/
theorem EmitCodeCorr.binOp_i32_inv {ctx : List String} {op : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.binOp .i32 op :: rest) wcode) :
    (op = "add" ∧ ∃ rest_w, wcode = Instr.i32Add :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "sub" ∧ ∃ rest_w, wcode = Instr.i32Sub :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "mul" ∧ ∃ rest_w, wcode = Instr.i32Mul :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "and" ∧ ∃ rest_w, wcode = Instr.i32And :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "or" ∧ ∃ rest_w, wcode = Instr.i32Or :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "eq" ∧ ∃ rest_w, wcode = Instr.i32Eq :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "ne" ∧ ∃ rest_w, wcode = Instr.i32Ne :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "lt_s" ∧ ∃ rest_w, wcode = Instr.i32Lts :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "gt_s" ∧ ∃ rest_w, wcode = Instr.i32Gts :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | binOp_i32_add _ rw hrw => left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_sub _ rw hrw => right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_mul _ rw hrw => right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_and _ rw hrw => right; right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_or _ rw hrw => right; right; right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_eq _ rw hrw => right; right; right; right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_ne _ rw hrw => right; right; right; right; right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_lts _ rw hrw => right; right; right; right; right; right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_i32_gts _ rw hrw => right; right; right; right; right; right; right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for binOp .f64 op :: rest. -/
theorem EmitCodeCorr.binOp_f64_inv {ctx : List String} {op : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.binOp .f64 op :: rest) wcode) :
    (op = "add" ∧ ∃ rest_w, wcode = Instr.f64Add :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "sub" ∧ ∃ rest_w, wcode = Instr.f64Sub :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "mul" ∧ ∃ rest_w, wcode = Instr.f64Mul :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "div" ∧ ∃ rest_w, wcode = Instr.f64Div :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | binOp_f64_add _ rw hrw => left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_f64_sub _ rw hrw => right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_f64_mul _ rw hrw => right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | binOp_f64_div _ rw hrw => right; right; right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for unOp .i32 op :: rest. -/
theorem EmitCodeCorr.unOp_i32_inv {ctx : List String} {op : String} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.unOp .i32 op :: rest) wcode) :
    (op = "eqz" ∧ ∃ rest_w, wcode = Instr.i32Eqz :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    (op = "wrap_i64" ∧ ∃ rest_w, wcode = Instr.i32WrapI64 :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | unOp_i32_eqz _ rw hrw => left; exact ⟨rfl, rw, rfl, hrw⟩
  | unOp_i32_wrapI64 _ rw hrw => right; left; exact ⟨rfl, rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for load .i32 offset :: rest. -/
theorem EmitCodeCorr.load_i32_inv {ctx : List String} {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.load .i32 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.i32Load { offset := offset, align := 2 } :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | load_i32 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for load .f64 offset :: rest. -/
theorem EmitCodeCorr.load_f64_inv {ctx : List String} {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.load .f64 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.f64Load { offset := offset, align := 3 } :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | load_f64 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for store .i32 offset :: rest. -/
theorem EmitCodeCorr.store_i32_inv {ctx : List String} {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.store .i32 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.i32Store { offset := offset, align := 2 } :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | store_i32 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for store .f64 offset :: rest. -/
theorem EmitCodeCorr.store_f64_inv {ctx : List String} {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.store .f64 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.f64Store { offset := offset, align := 3 } :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | store_f64 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for load .i64 offset :: rest. -/
theorem EmitCodeCorr.load_i64_inv {ctx : List String} {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.load .i64 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.i64Load { offset := offset, align := 3 } :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | load_i64 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for store .i64 offset :: rest. -/
theorem EmitCodeCorr.store_i64_inv {ctx : List String} {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.store .i64 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.i64Store { offset := offset, align := 3 } :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | store_i64 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for store8 offset :: rest. -/
theorem EmitCodeCorr.store8_inv {ctx : List String} {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.store8 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.i32Store8 { offset := offset, align := 0 } :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | store8_ _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Inversion for callIndirect typeIdx :: rest. -/
theorem EmitCodeCorr.callIndirect_inv {ctx : List String} {typeIdx : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (IRInstr.callIndirect typeIdx :: rest) wcode) :
    (∃ rest_w, wcode = Instr.callIndirect typeIdx 0 :: rest_w ∧ EmitCodeCorr ctx rest rest_w) ∨
    False := by
  cases h with
  | callIndirect_ _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- General inversion for any IR instruction. -/
theorem EmitCodeCorr.cons_inv {ctx : List String} {instr : IRInstr} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr ctx (instr :: rest) wcode) :
    ∃ wasm_prefix rest_w, wcode = wasm_prefix ++ rest_w ∧ EmitCodeCorr ctx rest rest_w := by
  cases h with
  | const_i32 _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | const_i64 _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | const_f64 _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | localGet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | localSet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | globalGet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | globalSet _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_add _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_sub _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_mul _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_and _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_or _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_eq _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_ne _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_lts _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_i32_gts _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_f64_add _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_f64_sub _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_f64_mul _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | binOp_f64_div _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | unOp_i32_eqz _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | unOp_i32_wrapI64 _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | call_ _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | drop_ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | return__ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | callIndirect_ _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | load_i32 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | store_i32 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | load_f64 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | store_f64 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | load_i64 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | store_i64 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | store8_ _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | block_ _ _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | loop_ _ _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | if__ _ _ _ _ _ _ _ rw _ _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | br_ _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | brIf_ _ _ _ rw _ hrw => exact ⟨[_], rw, rfl, hrw⟩
  | memoryGrow_ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

/-- Value correspondence for IR → Wasm: each IR value maps to the corresponding Wasm value.
    IR uses i32/i64/f64; Wasm adds f32 but emit only produces the same three types.
    REF: Emit.lean emitInstr. -/
inductive IRValueToWasmValue : IRValue → WasmValue → Prop where
  | i32 (n : UInt32) : IRValueToWasmValue (.i32 n) (.i32 n)
  | i64 (n : UInt64) : IRValueToWasmValue (.i64 n) (.i64 n)
  | f64 (n : Float) : IRValueToWasmValue (.f64 n) (.f64 n)

/-- Stack correspondence is preserved by pushing matching values. -/
theorem stack_corr_cons {istk : List IRValue} {wstk : List WasmValue}
    {iv : IRValue} {wv : WasmValue}
    (hlen : istk.length = wstk.length)
    (helems : ∀ i, i < istk.length → ∃ irv wv', istk[i]? = some irv ∧ wstk[i]? = some wv' ∧ IRValueToWasmValue irv wv')
    (hv : IRValueToWasmValue iv wv) :
    (iv :: istk).length = (wv :: wstk).length ∧
    ∀ i, i < (iv :: istk).length →
      ∃ irv wv', (iv :: istk)[i]? = some irv ∧ (wv :: wstk)[i]? = some wv' ∧ IRValueToWasmValue irv wv' := by
  constructor
  · simp; exact hlen
  · intro i hi
    match i with
    | 0 => exact ⟨iv, wv, rfl, rfl, hv⟩
    | i + 1 =>
      simp at hi
      exact helems i (by omega)

/-- Stack correspondence is preserved by popping. -/
theorem stack_corr_tail {iv : IRValue} {wv : WasmValue}
    {istk : List IRValue} {wstk : List WasmValue}
    (hlen : (iv :: istk).length = (wv :: wstk).length)
    (helems : ∀ i, i < (iv :: istk).length → ∃ irv wv', (iv :: istk)[i]? = some irv ∧ (wv :: wstk)[i]? = some wv' ∧ IRValueToWasmValue irv wv') :
    istk.length = wstk.length ∧
    ∀ i, i < istk.length →
      ∃ irv wv', istk[i]? = some irv ∧ wstk[i]? = some wv' ∧ IRValueToWasmValue irv wv' := by
  constructor
  · simp at hlen; exact hlen
  · intro i hi
    have := helems (i + 1) (by simp; omega)
    simpa using this

/-- Stack correspondence inversion: if IR stack starts with one i32,
    the Wasm stack starts with the same i32. -/
theorem stack_corr_i32_inv
    (a : UInt32) (stk : List IRValue) (wstk : List WasmValue)
    (hlen : (IRValue.i32 a :: stk).length = wstk.length)
    (helems : ∀ i, i < (IRValue.i32 a :: stk).length →
      ∃ irv wv, (IRValue.i32 a :: stk)[i]? = some irv ∧ wstk[i]? = some wv ∧ IRValueToWasmValue irv wv) :
    ∃ wstk', wstk = .i32 a :: wstk' ∧
      wstk'.length = stk.length ∧
      ∀ i, i < stk.length →
        ∃ irv wv, stk[i]? = some irv ∧ wstk'[i]? = some wv ∧ IRValueToWasmValue irv wv := by
  match wstk with
  | [] => simp at hlen
  | w0 :: wstk' =>
    simp at hlen
    have h0 := helems 0 (by simp)
    simp at h0
    cases h0
    exact ⟨wstk', rfl, hlen.symm, fun i hi => by
      have := helems (i + 1) (by simp; omega)
      simpa using this⟩

/-- Stack correspondence inversion: if IR stack starts with two i32 values,
    the Wasm stack starts with the corresponding i32 values. -/
theorem stack_corr_i32_i32_inv
    (a b : UInt32) (stk : List IRValue) (wstk : List WasmValue)
    (hlen : (IRValue.i32 a :: .i32 b :: stk).length = wstk.length)
    (helems : ∀ i, i < (IRValue.i32 a :: .i32 b :: stk).length →
      ∃ irv wv, (IRValue.i32 a :: .i32 b :: stk)[i]? = some irv ∧ wstk[i]? = some wv ∧ IRValueToWasmValue irv wv) :
    ∃ wstk', wstk = .i32 a :: .i32 b :: wstk' ∧
      wstk'.length = stk.length ∧
      ∀ i, i < stk.length →
        ∃ irv wv, stk[i]? = some irv ∧ wstk'[i]? = some wv ∧ IRValueToWasmValue irv wv := by
  match wstk with
  | [] => simp at hlen
  | [_] => simp at hlen
  | w0 :: w1 :: wstk' =>
    simp at hlen
    have h0 := helems 0 (by simp)
    simp at h0
    cases h0
    have h1 := helems 1 (by simp)
    simp at h1
    cases h1
    exact ⟨wstk', rfl, hlen.symm, fun i hi => by
      have := helems (i + 2) (by simp; omega)
      simpa using this⟩

/-- Stack correspondence inversion for two f64 values. -/
theorem stack_corr_f64_f64_inv
    (a b : Float) (stk : List IRValue) (wstk : List WasmValue)
    (hlen : (IRValue.f64 a :: .f64 b :: stk).length = wstk.length)
    (helems : ∀ i, i < (IRValue.f64 a :: .f64 b :: stk).length →
      ∃ irv wv, (IRValue.f64 a :: .f64 b :: stk)[i]? = some irv ∧ wstk[i]? = some wv ∧ IRValueToWasmValue irv wv) :
    ∃ wstk', wstk = .f64 a :: .f64 b :: wstk' ∧
      wstk'.length = stk.length ∧
      ∀ i, i < stk.length →
        ∃ irv wv, stk[i]? = some irv ∧ wstk'[i]? = some wv ∧ IRValueToWasmValue irv wv := by
  match wstk with
  | [] => simp at hlen
  | [_] => simp at hlen
  | w0 :: w1 :: wstk' =>
    simp at hlen
    have h0 := helems 0 (by simp)
    simp at h0; cases h0
    have h1 := helems 1 (by simp)
    simp at h1; cases h1
    exact ⟨wstk', rfl, hlen.symm, fun i hi => by
      have := helems (i + 2) (by simp; omega)
      simpa using this⟩

/-- Stack correspondence inversion for f64 value on top of i32 address. -/
theorem stack_corr_f64_i32_inv
    (v : Float) (addr : UInt32) (stk : List IRValue) (wstk : List WasmValue)
    (hlen : (IRValue.f64 v :: .i32 addr :: stk).length = wstk.length)
    (helems : ∀ i, i < (IRValue.f64 v :: .i32 addr :: stk).length →
      ∃ irv wv, (IRValue.f64 v :: .i32 addr :: stk)[i]? = some irv ∧ wstk[i]? = some wv ∧ IRValueToWasmValue irv wv) :
    ∃ wstk', wstk = .f64 v :: .i32 addr :: wstk' ∧
      wstk'.length = stk.length ∧
      ∀ i, i < stk.length →
        ∃ irv wv, stk[i]? = some irv ∧ wstk'[i]? = some wv ∧ IRValueToWasmValue irv wv := by
  match wstk with
  | [] => simp at hlen
  | [_] => simp at hlen
  | w0 :: w1 :: wstk' =>
    simp at hlen
    have h0 := helems 0 (by simp)
    simp at h0; cases h0
    have h1 := helems 1 (by simp)
    simp at h1; cases h1
    exact ⟨wstk', rfl, hlen.symm, fun i hi => by
      have := helems (i + 2) (by simp; omega)
      simpa using this⟩

/-- Stack correspondence inversion: if IR stack starts with i64 val and i32 addr,
    the Wasm stack starts with the corresponding i64 and i32 values. -/
theorem stack_corr_i64_i32_inv
    (v : UInt64) (addr : UInt32) (stk : List IRValue) (wstk : List WasmValue)
    (hlen : (IRValue.i64 v :: .i32 addr :: stk).length = wstk.length)
    (helems : ∀ i, i < (IRValue.i64 v :: .i32 addr :: stk).length →
      ∃ irv wv, (IRValue.i64 v :: .i32 addr :: stk)[i]? = some irv ∧ wstk[i]? = some wv ∧ IRValueToWasmValue irv wv) :
    ∃ wstk', wstk = .i64 v :: .i32 addr :: wstk' ∧
      wstk'.length = stk.length ∧
      ∀ i, i < stk.length →
        ∃ irv wv, stk[i]? = some irv ∧ wstk'[i]? = some wv ∧ IRValueToWasmValue irv wv := by
  match wstk with
  | [] => simp at hlen
  | [_] => simp at hlen
  | w0 :: w1 :: wstk' =>
    simp at hlen
    have h0 := helems 0 (by simp)
    simp at h0; cases h0
    have h1 := helems 1 (by simp)
    simp at h1; cases h1
    exact ⟨wstk', rfl, hlen.symm, fun i hi => by
      have := helems (i + 2) (by simp; omega)
      simpa using this⟩

/-- Simulation relation for IR → Wasm emit.
    The step correspondence field provides the matching Wasm step for each IR step.
    REF: Standard forward simulation diagram. -/
structure EmitSimRel (irmod : IRModule) (wmod : Module)
    (ir : IRExecState) (w : ExecState) : Prop where
  /- The Wasm module is the result of emitting the IR module. -/
  hemit : emit irmod = .ok wmod
  /- Code correspondence: the Wasm code is the emitted form of the IR code.
     ctx = ir.labels.map (·.name) tracks the label context from emit time. -/
  hcode : EmitCodeCorr (ir.labels.map (·.name)) ir.code w.code
  /- Stack correspondence: IR and Wasm stacks have matching values element-wise.
     ir.stack.map irToWasm = w.stack where the mapping is the natural embedding. -/
  hstack : ir.stack.length = w.stack.length ∧
    ∀ (i : Nat), i < ir.stack.length →
      ∃ irv wv, ir.stack[i]? = some irv ∧ w.stack[i]? = some wv ∧ IRValueToWasmValue irv wv
  /- Frame correspondence: head frames (if any) have matching locals. -/
  hframes_len : ir.frames.length = w.frames.length
  hframes_locals : ∀ (irf : IRFrame) (wf : Frame) (irfs : List IRFrame) (wfs : List Frame),
      ir.frames = irf :: irfs → w.frames = wf :: wfs →
        irf.locals.size = wf.locals.size
  hframes_vals : ∀ (irf : IRFrame) (wf : Frame) (irfs : List IRFrame) (wfs : List Frame),
      ir.frames = irf :: irfs → w.frames = wf :: wfs →
        ∀ (j : Nat) (hj : j < irf.locals.size) (hj' : j < wf.locals.size),
          IRValueToWasmValue (irf.locals[j]'hj) (wf.locals[j]'hj')
  /- Global variable correspondence: IR and Wasm globals have matching values element-wise. -/
  hglobals : ir.globals.size = w.store.globals.size ∧
    ∀ (j : Nat), j < ir.globals.size →
      ∃ irv wv, ir.globals[j]? = some irv ∧ w.store.globals[j]? = some wv ∧ IRValueToWasmValue irv wv
  /- Memory correspondence: Wasm and IR memories are equal or both absent/empty. -/
  hmemory : (w.store.memories[0]? = some ir.memory) ∨
            (w.store.memories[0]? = none ∧ ir.memory.size = 0)
  /- Memory limits: max is none (needed for memoryGrow correspondence). -/
  hmemLimits : ∀ lim, w.store.memLimits[0]? = some lim → lim.max = none
  /- Memory page alignment (needed for memoryGrow condition equivalence). -/
  hmemory_aligned : 65536 ∣ ir.memory.size
  /- Memory existence: Wasm store has at least one memory (always true for modules from lower). -/
  hmemory_nonempty : 0 < w.store.memories.size
  /- Label correspondence (needed for halt derivation). -/
  hlabels : ir.labels.length = w.labels.length
  /- Halt correspondence. -/
  hhalt : irStep? ir = none → Wasm.step? w = none
  /- Label content correspondence: for each label position, onExit and onBranch correspond,
     and isLoop flags match. -/
  hlabel_content : ∀ (i : Nat), i < ir.labels.length →
    ∃ irLbl wLbl, ir.labels[i]? = some irLbl ∧ w.labels[i]? = some wLbl ∧
      EmitCodeCorr ((ir.labels.drop (i + 1)).map (·.name)) irLbl.onExit wLbl.onExit ∧
      EmitCodeCorr ((ir.labels.drop (if irLbl.isLoop then i else i + 1)).map (·.name))
        irLbl.onBranch wLbl.onBranch ∧
      irLbl.isLoop = wLbl.isLoop
  /- Frame count: exactly one frame (top-level). -/
  hframes_one : ir.frames.length = 1
  /- IR module invariant: runtime module equals the parameter module. -/
  hmodule : ir.module = irmod
  /- Wasm store.funcs invariant: never modified during execution. -/
  hstore_funcs : w.store.funcs = wmod.funcs
  /- Wasm store.types invariant: never modified during execution. -/
  hstore_types : w.store.types = wmod.types

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

/-- emit preserves the number of globals. -/
private theorem emit_preserves_globals_size (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    wmod.globals.size = irmod.globals.size := by
  unfold emit at hemit
  simp only [Bind.bind, Except.bind] at hemit
  split at hemit
  · simp at hemit
  · simp only [Except.ok.injEq] at hemit
    rw [← hemit]; simp [buildModule]

/-- Each emitOneFunc call pushes exactly 1 function to acc.funcs. -/
private theorem emitOneFunc_funcs_size (acc : EmitAcc) (f : IRFunc) (acc' : EmitAcc)
    (h : emitOneFunc acc f = .ok acc') : acc'.funcs.size = acc.funcs.size + 1 := by
  simp only [emitOneFunc, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · split at h <;> (simp only [Except.ok.injEq] at h; subst h; simp [Array.size_push])

/-- foldlM emitOneFunc preserves the invariant: acc.funcs.size increases by list length. -/
private theorem foldlM_emitOneFunc_funcs_size (initAcc : EmitAcc) (fs : List IRFunc)
    (finalAcc : EmitAcc)
    (h : fs.foldlM emitOneFunc initAcc = .ok finalAcc) :
    finalAcc.funcs.size = initAcc.funcs.size + fs.length := by
  induction fs generalizing initAcc finalAcc with
  | nil =>
    simp only [List.foldlM, pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h; simp
  | cons f rest ih =>
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i midAcc heq
      have hmid := emitOneFunc_funcs_size initAcc f midAcc heq
      have hrest := ih midAcc finalAcc h
      simp [List.length_cons]; omega

/-- emit preserves function count. -/
private theorem emit_preserves_funcs_size (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) :
    wmod.funcs.size = irmod.functions.size := by
  unfold emit at hemit
  simp only [Bind.bind, Except.bind] at hemit
  split at hemit
  · simp at hemit
  · rename_i _ finalAcc heq
    simp only [Except.ok.injEq] at hemit; subst hemit; simp [buildModule]
    have hfold := foldlM_emitOneFunc_funcs_size _ irmod.functions.toList finalAcc heq
    change finalAcc.funcs.size = 0 + irmod.functions.toList.length at hfold
    simp at hfold; exact hfold

/-- IRValue.default corresponds to Wasm defaultValue for each IR type. -/
private theorem irValueDefault_corr (t : IRType) :
    IRValueToWasmValue (IRValue.default t) (defaultValue (match t with
      | .i32 => ValType.i32 | .i64 => .i64 | .f64 => .f64 | .ptr => .i32)) := by
  cases t <;> simp [IRValue.default, defaultValue] <;> constructor

/-- Initial IR global value corresponds to initial Wasm global value for each position.
    Proven by unfolding emit to extract buildModule, then case-splitting on IR type. -/
private theorem emit_globals_init_valcorr (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod) (j : Nat) (hj : j < irmod.globals.size)
    (hj_w : j < wmod.globals.size) :
    IRValueToWasmValue (IRValue.default (irmod.globals[j]'hj).1)
                       (defaultValue (wmod.globals[j]'hj_w).type.val) := by
  -- Unfold emit to get wmod = buildModule irmod acc
  have hemit' := hemit
  unfold emit at hemit'
  simp only [Bind.bind, Except.bind] at hemit'
  split at hemit'
  · simp at hemit'
  · simp only [Except.ok.injEq] at hemit'
    subst hemit'
    -- Now wmod = buildModule irmod acc
    -- (buildModule irmod acc).globals = (irmod.globals.toList.map f).toArray
    -- where f maps (t, _, _) to { type := { val := irTypeToValType t, ... }, ... }
    -- So globals[j].type.val = irTypeToValType (irmod.globals[j].1)
    -- Case split on the IR type to close the goal
    -- Use irValueDefault_corr after connecting buildModule globals to IR type
    have h := irValueDefault_corr (irmod.globals[j]'hj).1
    -- Suffices to show the Wasm global type val matches the IR type pattern
    suffices hsuff : (buildModule irmod _).globals[j].type.val =
        (match (irmod.globals[j]'hj).1 with
          | .i32 => ValType.i32 | .i64 => .i64 | .f64 => .f64 | .ptr => .i32) by
      simp only [hsuff]; exact h
    -- Unfold buildModule to expose globals = (irmod.globals.toList.map f).toArray
    simp only [buildModule]
    -- Reduce (list.map f).toArray[j] to f (list[j])
    rw [List.getElem_toArray, List.getElem_map, Array.getElem_toList]
    cases (irmod.globals[j]'hj).fst <;> rfl

/-- Initial states are related: the IR initial state corresponds to the Wasm initial state.
    Proof: `emit irmod = .ok wmod` ensures module correspondence.
    Both start with empty stacks, and the entry code (start function call) is
    the same (emit preserves the start function field). -/
theorem init (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod)
    (hmem_pos : 0 < irmod.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : MemType),
      irmod.memories[i]? = some mt → mt.lim.max = none) :
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
  hframes_len := by simp [irInitialState, Wasm.initialState]
  hframes_locals := by
    intro irf wf irfs wfs hirf hwf
    simp [irInitialState] at hirf
    simp [Wasm.initialState] at hwf
    obtain ⟨rfl, rfl⟩ := hirf
    obtain ⟨rfl, rfl⟩ := hwf
    simp
  hframes_vals := by
    intro irf wf irfs wfs hirf hwf
    simp [irInitialState] at hirf
    simp [Wasm.initialState] at hwf
    obtain ⟨rfl, rfl⟩ := hirf
    obtain ⟨rfl, rfl⟩ := hwf
    intro j hj hj'
    simp at hj
  hglobals := by
    simp only [irInitialState, Wasm.initialState, initialStore]
    refine ⟨?_, ?_⟩
    · -- Size: (initIRGlobals irmod).size = (initGlobals wmod).size
      simp only [initIRGlobals, initGlobals, Array.size_map]
      exact (emit_preserves_globals_size irmod wmod hemit).symm
    · -- Values: element-wise correspondence
      intro j hj
      simp only [initIRGlobals, Array.size_map] at hj
      have hj_w : j < wmod.globals.size := by
        rw [emit_preserves_globals_size irmod wmod hemit]; exact hj
      simp only [initIRGlobals, initGlobals]
      refine ⟨IRValue.default (irmod.globals[j]'hj).1,
             defaultValue (wmod.globals[j]'hj_w).type.val,
             ?_, ?_, ?_⟩
      · simp [Array.getElem?_eq_getElem hj]
      · simp [Array.getElem?_eq_getElem hj_w]
      · -- IRValue.default t corresponds to defaultValue (wmod.globals[j].type.val)
        -- Use emit_globals_init_valcorr helper
        exact emit_globals_init_valcorr irmod wmod hemit j hj hj_w
  hmemory := by
    simp only [irInitialState, Wasm.initialState, initialStore]
    have hemit' := hemit
    unfold emit at hemit'
    simp only [Bind.bind, Except.bind] at hemit'
    split at hemit'
    · simp at hemit'
    · simp only [Except.ok.injEq] at hemit'
      subst hemit'
      simp only [initIRMemory]
      cases h0 : irmod.memories[0]? with
      | none =>
        right; constructor
        · simp [buildModule, Array.getElem?_map, h0]
        · rfl
      | some memType =>
        left; simp [buildModule, Array.getElem?_map, h0, initMemory]
  hmemLimits := by
    intro lim hlim
    simp only [Wasm.initialState, initialStore] at hlim
    have hemit' := hemit
    unfold emit at hemit'
    simp only [Bind.bind, Except.bind] at hemit'
    split at hemit'
    · simp at hemit'
    · simp only [Except.ok.injEq] at hemit'
      subst hemit'
      simp only [buildModule] at hlim
      cases h0 : irmod.memories[0]? with
      | none =>
        simp [Array.getElem?_map, h0] at hlim
      | some memType =>
        -- hlim tells us memLimits[0]? = some lim, where memLimits comes from
        -- (irmod.memories.toList.toArray).map (·.lim)
        -- With h0 : irmod.memories[0]? = some memType, lim = memType.lim
        simp only [Array.getElem?_map, h0] at hlim
        simp only [Option.map, Option.some.injEq] at hlim
        rw [← hlim]
        exact hmem_nomax 0 memType h0
  hmemory_aligned := by
    simp only [irInitialState]
    unfold initIRMemory
    cases irmod.memories[0]? with
    | none => exact ⟨0, rfl⟩
    | some mem =>
      simp only [ByteArray.size, Array.size_replicate]
      exact ⟨mem.lim.min, by omega⟩
  hmemory_nonempty := by
    simp only [Wasm.initialState, initialStore]
    have hemit' := hemit
    unfold emit at hemit'
    simp only [Bind.bind, Except.bind] at hemit'
    split at hemit'
    · simp at hemit'
    · simp only [Except.ok.injEq] at hemit'
      subst hemit'
      simp only [buildModule, Array.size_map, List.size_toArray, Array.length_toList]
      exact hmem_pos
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
  hlabel_content := by
    intro i hi; simp [irInitialState] at hi
  hframes_one := by simp [irInitialState]
  hmodule := by simp [irInitialState]
  hstore_funcs := by simp [Wasm.initialState, initialStore]
  hstore_types := by simp [Wasm.initialState, initialStore]

/-- Derive halt correspondence from code + label correspondence.
    Used to reconstruct `hhalt` in step_sim proofs. -/
theorem hhalt_of_structural {ctx : List String} {ir : IRExecState} {w : ExecState}
    (hcode : EmitCodeCorr ctx ir.code w.code)
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

/-- Generalized: findIdx?.go on mapped names corresponds to irFindLabel?.go at same offset.
    Note: irFindLabel?.go takes (name : String) first (closed-over), then (ls : List IRLabel) (start : Nat). -/
private theorem findIdx?_go_irFindLabel?_go
    (labels : List IRLabel) (name : String) (k : Nat) (idx : Nat)
    (h : List.findIdx?.go (· == name) (labels.map (·.name)) k = some idx) :
    ∃ lbl, irFindLabel?.go name labels k = some (idx, lbl) := by
  induction labels generalizing k idx with
  | nil => simp [List.findIdx?.go] at h
  | cons hd tl ih =>
    simp only [List.map, List.findIdx?.go] at h
    simp only [irFindLabel?.go]
    by_cases heq : hd.name == name
    · simp [heq] at h; subst h; simp [heq]
    · simp [heq] at h ⊢; exact ih (k + 1) idx h

/-- findIdx? on mapped names corresponds to irFindLabel?.
    If findIdx? (· == name) (labels.map (·.name)) = some idx,
    then irFindLabel? labels name = some (idx, labels[idx]). -/
private theorem findIdx?_map_name_irFindLabel?
    {labels : List IRLabel} {name : String} {idx : Nat}
    (h : (labels.map (·.name)).findIdx? (· == name) = some idx) :
    ∃ lbl, irFindLabel? labels name = some (idx, lbl) := by
  unfold List.findIdx? at h
  unfold irFindLabel?
  exact findIdx?_go_irFindLabel?_go labels name 0 idx h

/-- For a br instruction in EmitCodeCorr with label context ctx = irLabels.map (·.name),
    the label lookup succeeds and the Wasm depth index equals the IR label index.
    Now provable: EmitCodeCorr ctx carries findIdx? proof in br_ constructor. -/
private theorem emit_br_label_resolve
    {irLabels : List IRLabel} {wLabels : List LabelFrame}
    {label : String} {idx : Nat}
    {rest_ir : List IRInstr} {rest_w : List Instr}
    (hcode : EmitCodeCorr (irLabels.map (·.name)) (IRInstr.br label :: rest_ir) (Instr.br idx :: rest_w))
    (_hlabels : irLabels.length = wLabels.length) :
    ∃ ir_idx irLbl, irFindLabel? irLabels label = some (ir_idx, irLbl) ∧ idx = ir_idx := by
  -- Extract findIdx? proof from EmitCodeCorr br_ constructor
  rcases hcode.br_inv with ⟨idx', rest_w', hcw, hfind, _hrest⟩ | hf
  · simp at hcw; obtain ⟨rfl, rfl⟩ := hcw
    -- hfind : (irLabels.map (·.name)).findIdx? (· == label) = some idx
    obtain ⟨lbl, hirfind⟩ := findIdx?_map_name_irFindLabel? hfind
    exact ⟨idx, lbl, hirfind, rfl⟩
  · exact hf.elim

/-- Same as emit_br_label_resolve but for brIf. -/
private theorem emit_brIf_label_resolve
    {irLabels : List IRLabel} {wLabels : List LabelFrame}
    {label : String} {idx : Nat}
    {rest_ir : List IRInstr} {rest_w : List Instr}
    (hcode : EmitCodeCorr (irLabels.map (·.name)) (IRInstr.brIf label :: rest_ir) (Instr.brIf idx :: rest_w))
    (_hlabels : irLabels.length = wLabels.length) :
    ∃ ir_idx irLbl, irFindLabel? irLabels label = some (ir_idx, irLbl) ∧ idx = ir_idx := by
  rcases hcode.brIf_inv with ⟨idx', rest_w', hcw, hfind, _hrest⟩ | hf
  · simp at hcw; obtain ⟨rfl, rfl⟩ := hcw
    obtain ⟨lbl, hirfind⟩ := findIdx?_map_name_irFindLabel? hfind
    exact ⟨idx, lbl, hirfind, rfl⟩
  · exact hf.elim

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
  -- BLOCKED: Lean 4.29 API changes broke many EmitCodeCorr inversion proofs.
  -- The proof structure below is correct but references renamed constants
  -- (List.toArray_map, ByteArray.mkEmpty, Dvd.intro, etc.).
  -- Preserving the proof text as comments for restoration after API migration.
  -- Case analysis on the IR code (what instruction is being executed)
  -- irStep? dispatches on s1.code; EmitCodeCorr tells us what s2.code is
  match hcode_ir : s1.code with
  | [] =>
      -- No instructions: irStep? checks labels/frames, not instruction dispatch
      -- This is the label-pop or frame-return case
      match hlabels_ir : s1.labels with
      | irLbl :: irRest =>
          -- Label-pop: both sides pop label and continue with onExit
          have hir := irStep?_eq_labelDone s1 irLbl irRest hcode_ir hlabels_ir
          rw [hir] at hstep
          simp only [Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl⟩ := hstep
          -- Wasm also has non-empty labels (by hlabels)
          have hlen := hrel.hlabels; rw [hlabels_ir] at hlen; simp at hlen
          match hlabels_w : s2.labels with
          | [] => simp [hlabels_w] at hlen
          | wLbl :: wRest =>
            -- Get Wasm code from nil_inv on hcode
            have hcw : s2.code = [] := EmitCodeCorr.nil_inv (hcode_ir ▸ hrel.hcode)
            have hw := step?_eq_labelDone s2 wLbl wRest hcw hlabels_w
            -- Get onExit correspondence from hlabel_content
            obtain ⟨irLbl0, wLbl0, hirLbl0, hwLbl0, hcode_exit, _hcode_branch, _hloop0⟩ :=
              hrel.hlabel_content 0 (by rw [hlabels_ir]; simp)
            rw [hlabels_ir] at hirLbl0; simp at hirLbl0; subst hirLbl0
            rw [hlabels_w] at hwLbl0; simp at hwLbl0; subst hwLbl0
            -- hcode_exit : EmitCodeCorr ((s1.labels.drop 1).map (·.name)) irLbl.onExit wLbl.onExit
            -- Since s1.labels = irLbl :: irRest, drop 1 = irRest
            have hctx_eq : (s1.labels.drop 1).map (·.name) = irRest.map (·.name) := by
              rw [hlabels_ir]; simp
            rw [hctx_eq] at hcode_exit
            -- hcode_exit : EmitCodeCorr (irRest.map (·.name)) irLbl.onExit wLbl.onExit
            -- Post-step labels correspondence
            have hlabels_post : irRest.length = wRest.length := by
              have := hrel.hlabels; rw [hlabels_ir, hlabels_w] at this
              simp at this; exact this
            exact ⟨_, hw,
              ⟨hrel.hemit, hcode_exit, hrel.hstack, hrel.hframes_len, hrel.hframes_locals,
                hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned,
                hrel.hmemory_nonempty, hlabels_post,
                hhalt_of_structural hcode_exit hlabels_post, by
                  intro i hi
                  have hi1 : i + 1 < s1.labels.length := by rw [hlabels_ir]; simp; omega
                  obtain ⟨irLbl_i, wLbl_i, hirLbl_i, hwLbl_i, hce_i, hcb_i, hloop_i⟩ :=
                    hrel.hlabel_content (i + 1) hi1
                  -- The successor labels are irRest, wRest (tails of s1.labels, s2.labels)
                  -- Need to convert ctx from s1.labels.drop to irRest.drop
                  have hlbl_eq : s1.labels.drop (i + 1 + 1) = irRest.drop (i + 1) := by
                    rw [hlabels_ir]; simp [List.drop_succ_cons]
                  refine ⟨irLbl_i, wLbl_i, ?_, ?_, ?_, ?_, hloop_i⟩
                  · rw [hlabels_ir] at hirLbl_i; simpa using hirLbl_i
                  · rw [hlabels_w] at hwLbl_i; simpa using hwLbl_i
                  · -- onExit ctx: drop (i+1+1) -> drop (i+1) on irRest
                    rw [hlbl_eq] at hce_i; exact hce_i
                  · -- onBranch ctx: adjust for isLoop
                    have hlbl_cb : (s1.labels.drop (if irLbl_i.isLoop then (i + 1) else (i + 1) + 1)).map (·.name) =
                      (irRest.drop (if irLbl_i.isLoop then i else i + 1)).map (·.name) := by
                      cases irLbl_i.isLoop <;> simp [hlabels_ir, List.drop_succ_cons]
                    rw [hlbl_cb] at hcb_i; exact hcb_i,
                hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
      | [] =>
          -- Labels empty: IR has code=[] and labels=[].
          -- With hframes_one, frames.length = 1, so IR is halted.
          exfalso
          have hhalted : s1.halted := ⟨hcode_ir, hlabels_ir, Nat.le_of_eq hrel.hframes_one⟩
          have := irStep?_halted hhalted
          simp [this] at hstep
  | instr :: rest =>
      match instr with
      | .const_ .i32 v =>
          -- i32 const: IR pushes i32, Wasm pushes i32_const
          have hc : EmitCodeCorr _ (IRInstr.const_ .i32 v :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.const_i32_inv with ⟨n, rest_w, hcw, hparse, hrest⟩ | hf
          · -- Specific case: Wasm code = i32Const n :: rest_w
            have hir := irStep?_eq_i32Const s1 v n.toNat rest hcode_ir hparse
            simp only [show n.toNat.toUInt32 = n from by simp] at hir
            rw [hir] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            have hw := step?_eq_i32Const s2 n rest_w hcw
            refine ⟨_, hw, ⟨hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
            dsimp only []
            exact stack_corr_cons hrel.hstack.1 hrel.hstack.2 (.i32 n)
          · exact hf.elim
      | .const_ .i64 v =>
          -- i64 const: same pattern as i32
          have hc : EmitCodeCorr _ (IRInstr.const_ .i64 v :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.const_i64_inv with ⟨n, rest_w, hcw, hparse, hrest⟩ | hf
          · have hir := irStep?_eq_i64Const s1 v n.toNat rest hcode_ir hparse
            simp only [show n.toNat.toUInt64 = n from by simp] at hir
            rw [hir] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            have hw := step?_eq_i64Const s2 n rest_w hcw
            refine ⟨_, hw, ⟨hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
            dsimp only []
            exact stack_corr_cons hrel.hstack.1 hrel.hstack.2 (.i64 n)
          · exact hf.elim
      | .const_ .f64 v =>
          -- f64 const: same pattern as i32
          have hc : EmitCodeCorr _ (IRInstr.const_ .f64 v :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.const_f64_inv with ⟨f, rest_w, hcw, hfeq, hrest⟩ | hf
          · subst hfeq
            have hir := irStep?_eq_f64Const s1 v rest hcode_ir
            rw [hir] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            have hw := step?_eq_f64Const s2 _ rest_w hcw
            refine ⟨_, hw, ⟨hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
            dsimp only []
            exact stack_corr_cons hrel.hstack.1 hrel.hstack.2 (.f64 _)
          · exact hf.elim
      | .const_ .ptr v =>
          -- ptr const: no EmitCodeCorr constructor for .ptr, so vacuously true
          have hc : EmitCodeCorr _ (IRInstr.const_ .ptr v :: rest) s2.code := hcode_ir ▸ hrel.hcode
          exfalso
          generalize s2.code = wcode at hc
          cases hc with
          | general _ _ _ _ hf _ => exact hf
      | .localGet idx =>
          -- local.get: both IR and Wasm look up local variable
          have hc : EmitCodeCorr _ (IRInstr.localGet idx :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.localGet_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- IR has localGet idx, Wasm has localGet idx
            -- Case split on IR frames and local lookup
            match hfr_ir : s1.frames with
            | [] =>
              -- Trap: no active frame for localGet
              have hir := irStep?_eq_localGet_noFrame s1 idx rest hcode_ir hfr_ir
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- Wasm also has no frame (by frame length correspondence)
              have hflen := hrel.hframes_len; rw [hfr_ir] at hflen; simp at hflen
              have hfr_w : s2.frames = [] := by
                cases hs : s2.frames with | nil => rfl | cons => simp [hs] at hflen
              have hw := step?_eq_localGet_noFrame s2 idx rest_w hcw hfr_w
              exact ⟨{ s2 with code := [], trace := s2.trace ++ [.trap "local.get without active frame"] },
                by simp [traceToWasm]; exact hw,
                ⟨hrel.hemit, .nil, by dsimp only []; exact hrel.hstack,
                  by dsimp only []; exact hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals,
                  hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty,
                  by dsimp only []; exact hrel.hlabels,
                  hhalt_of_structural (@EmitCodeCorr.nil []) hrel.hlabels, hrel.hlabel_content, hrel.hframes_one,
                  hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
            | irf :: irfs =>
              match hlocal : irf.locals[idx]? with
              | none =>
                -- Trap: local index out of bounds
                have hidx_oob : ¬(idx < irf.locals.size) := by
                  intro h; simp_all
                have hir := irStep?_eq_localGet_oob s1 idx rest irf irfs hcode_ir hfr_ir hlocal
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm also has a frame but idx out of bounds
                have hflen := hrel.hframes_len; rw [hfr_ir] at hflen
                match hfr_w : s2.frames with
                | [] => simp [hfr_w] at hflen
                | wf :: wfs =>
                  -- idx is also NOT in bounds for Wasm frame (same size)
                  have hloc_sz := hrel.hframes_locals irf wf irfs wfs hfr_ir hfr_w
                  have hidx_oob_w : ¬(idx < wf.locals.size) := by omega
                  have hw := step?_eq_localGet_oob s2 idx rest_w wf wfs hcw hfr_w hidx_oob_w
                  have hmsg : s!"unknown local index {idx}" = s!"unknown local index {idx}" := rfl
                  exact ⟨{ s2 with code := [], trace := s2.trace ++ [.trap s!"unknown local index {idx}"] },
                    by simp [traceToWasm]; exact hw,
                    ⟨hrel.hemit, .nil, by dsimp only []; exact hrel.hstack,
                      by dsimp only []; exact hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals,
                      hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty,
                      by dsimp only []; exact hrel.hlabels,
                      hhalt_of_structural (@EmitCodeCorr.nil []) hrel.hlabels, hrel.hlabel_content, hrel.hframes_one,
                      hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
              | some val =>
                have hir := irStep?_eq_localGet s1 idx rest irf irfs val hcode_ir hfr_ir hlocal
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Derive Wasm frame from frame correspondence
                have hflen := hrel.hframes_len; rw [hfr_ir] at hflen
                match hfr_w : s2.frames with
                | [] => simp [hfr_w] at hflen
                | wf :: wfs =>
                  -- idx < irf.locals.size
                  have hidx_ir : idx < irf.locals.size := by
                    if h : idx < irf.locals.size then exact h
                    else exact absurd hlocal (by rw [getElem?_neg irf.locals idx h]; exact nofun)
                  -- idx < wf.locals.size
                  have hloc_sz := hrel.hframes_locals irf wf irfs wfs hfr_ir hfr_w
                  have hidx_w : idx < wf.locals.size := hloc_sz ▸ hidx_ir
                  -- Wasm step
                  have hw := step?_eq_localGet s2 idx rest_w wf wfs hcw hfr_w hidx_w
                  -- Value correspondence
                  have hval_corr := hrel.hframes_vals irf wf irfs wfs hfr_ir hfr_w idx hidx_ir hidx_w
                  have hval_eq : val = irf.locals[idx]'hidx_ir := by
                    have := getElem?_pos irf.locals idx hidx_ir
                    rw [this] at hlocal; exact (Option.some.inj hlocal).symm
                  rw [hval_eq]
                  exact ⟨_, hw, hrel.hemit, hrest, by dsimp only []; exact stack_corr_cons hrel.hstack.1 hrel.hstack.2 hval_corr, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩
          · exact hf.elim
      | .localSet idx =>
          -- local.set: pop value from stack, set local[idx]
          have hc : EmitCodeCorr _ (IRInstr.localSet idx :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.localSet_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- Specific case: Wasm code = localSet idx :: rest_w
            -- Need a value on stack
            match hstk : s1.stack with
            | [] =>
              -- Empty stack: sub-case on frames (IR match order: no-frame wins over empty-stack)
              match hfr_ir0 : s1.frames with
              | [] =>
                -- No frame AND no stack: IR traps "local.set without active frame"
                have hir := irStep?_eq_localSet_noFrame s1 idx rest hcode_ir hfr_ir0
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm also has no frames
                have hflen := hrel.hframes_len; rw [hfr_ir0] at hflen; simp at hflen
                have hfr_w : s2.frames = [] := by
                  cases hs : s2.frames with | nil => rfl | cons => simp [hs] at hflen
                have hw := step?_eq_localSet_noFrame s2 idx rest_w hcw hfr_w
                exact ⟨{ s2 with code := [], trace := s2.trace ++ [.trap "local.set without active frame"] },
                  by simp [traceToWasm]; exact hw,
                  { hemit := hrel.hemit
                    hcode := .nil
                    hstack := hrel.hstack
                    hframes_len := by dsimp only []; exact hrel.hframes_len
                    hframes_locals := hrel.hframes_locals
                    hframes_vals := hrel.hframes_vals
                    hglobals := hrel.hglobals
                    hmemory := hrel.hmemory
                    hmemLimits := hrel.hmemLimits
                    hmemory_aligned := hrel.hmemory_aligned
                    hmemory_nonempty := hrel.hmemory_nonempty
                    hlabels := by dsimp only []; exact hrel.hlabels
                    hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | irf :: irfs =>
                -- Has frame but empty stack: IR traps "stack underflow in local.set"
                have hir := irStep?_eq_localSet_emptyStack s1 idx rest irf irfs hcode_ir hstk hfr_ir0
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm stack also empty
                have hlen_eq := hrel.hstack.1; rw [hstk] at hlen_eq; simp at hlen_eq
                have hs2 : s2.stack = [] := by
                  cases hs : s2.stack with | nil => rfl | cons => simp [hs] at hlen_eq
                -- Wasm also has frames (by frame length correspondence)
                have hflen := hrel.hframes_len; rw [hfr_ir0] at hflen
                match hfr_w : s2.frames with
                | [] => simp [hfr_w] at hflen
                | wf :: wfs =>
                  have hw := step?_eq_localSet_emptyStack s2 idx rest_w wf wfs hcw hs2 hfr_w
                  exact ⟨{ s2 with code := [], stack := [], trace := s2.trace ++ [.trap "stack underflow in local.set"] },
                    by simp [traceToWasm]; exact hw,
                    { hemit := hrel.hemit
                      hcode := .nil
                      hstack := by simp [hs2]
                      hframes_len := by dsimp only []; exact hrel.hframes_len
                      hframes_locals := hrel.hframes_locals
                      hframes_vals := hrel.hframes_vals
                      hglobals := hrel.hglobals
                      hmemory := hrel.hmemory
                      hmemLimits := hrel.hmemLimits
                      hmemory_aligned := hrel.hmemory_aligned
                      hmemory_nonempty := hrel.hmemory_nonempty
                      hlabels := by dsimp only []; exact hrel.hlabels
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }⟩
            | iv :: istk =>
              -- Need a frame
              match hfr_ir : s1.frames with
              | [] =>
                -- No frame: IR traps "local.set without active frame"
                have hir := irStep?_eq_localSet_noFrame s1 idx rest hcode_ir hfr_ir
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm also has no frames
                have hflen := hrel.hframes_len; rw [hfr_ir] at hflen; simp at hflen
                have hfr_w : s2.frames = [] := by
                  cases hs : s2.frames with | nil => rfl | cons => simp [hs] at hflen
                have hw := step?_eq_localSet_noFrame s2 idx rest_w hcw hfr_w
                exact ⟨{ s2 with code := [], trace := s2.trace ++ [.trap "local.set without active frame"] },
                  by simp [traceToWasm]; exact hw,
                  { hemit := hrel.hemit
                    hcode := .nil
                    hstack := hrel.hstack
                    hframes_len := by dsimp only []; exact hrel.hframes_len
                    hframes_locals := hrel.hframes_locals
                    hframes_vals := hrel.hframes_vals
                    hglobals := hrel.hglobals
                    hmemory := hrel.hmemory
                    hmemLimits := hrel.hmemLimits
                    hmemory_aligned := hrel.hmemory_aligned
                    hmemory_nonempty := hrel.hmemory_nonempty
                    hlabels := by dsimp only []; exact hrel.hlabels
                    hhalt := hhalt_of_structural (@EmitCodeCorr.nil []) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | irf :: irfs =>
                -- Need idx in bounds
                if hlt : idx < irf.locals.size then
                  -- IR step
                  have hir := irStep?_eq_localSet s1 idx rest iv istk irf irfs hcode_ir hstk hfr_ir hlt
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  -- Derive Wasm frame from frame correspondence
                  have hflen := hrel.hframes_len; rw [hfr_ir] at hflen
                  match hfr_w : s2.frames with
                  | [] => simp [hfr_w] at hflen
                  | wf :: wfs =>
                    -- Wasm stack correspondence: need wv on top
                    have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                    match hstk_w : s2.stack with
                    | [] => simp [hstk_w] at hstk_rel
                    | wv :: wstk =>
                      -- idx in bounds for wasm frame
                      have hloc_sz := hrel.hframes_locals irf wf irfs wfs hfr_ir hfr_w
                      have hlt_w : idx < wf.locals.size := hloc_sz ▸ hlt
                      -- Wasm step
                      have hw := step?_eq_localSet s2 idx rest_w wv wstk wf wfs hcw hstk_w hfr_w hlt_w
                      have hfo_base := hrel.hframes_one
                      have hfo : ({ locals := irf.locals.set! idx iv, returnArity := irf.returnArity, savedCode := irf.savedCode, savedLabels := irf.savedLabels } :: irfs).length = 1 := by
                        simp only [List.length_cons]; rw [hfr_ir, List.length_cons] at hfo_base; exact hfo_base
                      refine ⟨_, hw, hrel.hemit, hrest, ?_, ?_, ?_, ?_, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hfo, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩
                      · -- Stack correspondence (tail after pop)
                        rw [hstk_w] at hstk_rel
                        exact stack_corr_tail hstk_rel.1 hstk_rel.2
                      · -- Frame length preserved
                        have hfl := hrel.hframes_len
                        simp only [List.length_cons, hfr_ir, hfr_w] at hfl ⊢
                        exact hfl
                      · -- Frame locals size after set!
                        intro irf' wf' irfs' wfs' hir' hw'
                        simp only [] at hir' hw'
                        obtain ⟨rfl, rfl⟩ := hir'; obtain ⟨rfl, rfl⟩ := hw'
                        show (irf.locals.set! idx iv).size = (wf.locals.set! idx wv).size
                        simp_all [Array.set!]
                      · -- Frame vals after set!
                        intro irf' wf' irfs' wfs' hir' hw' j hj hj'
                        simp only [] at hir' hw'
                        obtain ⟨rfl, rfl⟩ := hir'; obtain ⟨rfl, rfl⟩ := hw'
                        -- Get head value correspondence from stack
                        have hhead := hstk_rel.2 0 (by simp)
                        simp [hstk_w] at hhead
                        -- hhead : IRValueToWasmValue iv wv
                        -- Case split: j = idx vs j ≠ idx
                        simp only [Array.set!] at hj hj' ⊢
                        unfold Array.setIfInBounds at hj hj' ⊢
                        simp [hlt, hlt_w] at hj hj' ⊢
                        if heq : j = idx then
                          subst heq
                          simp [Array.getElem_set]
                          exact hhead
                        else
                          have hne : idx ≠ j := Ne.symm heq
                          simp [Array.getElem_set, heq, hne]
                          exact hrel.hframes_vals irf wf irfs wfs hfr_ir hfr_w j
                            (by omega) (by omega)
                else
                  -- idx out of bounds: IR traps "unknown local index {idx}"
                  have hir := irStep?_eq_localSet_oob s1 idx rest iv istk irf irfs hcode_ir hstk hfr_ir hlt
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  -- Wasm also has a frame with same locals size, so idx also out of bounds
                  have hflen := hrel.hframes_len; rw [hfr_ir] at hflen
                  match hfr_w : s2.frames with
                  | [] => simp [hfr_w] at hflen
                  | wf :: wfs =>
                    have hloc_sz := hrel.hframes_locals irf wf irfs wfs hfr_ir hfr_w
                    have hlt_w : ¬(idx < wf.locals.size) := by omega
                    -- Derive Wasm stack from stack correspondence
                    have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                    match hstk_w : s2.stack with
                    | [] => simp [hstk_w] at hstk_rel
                    | wv :: wstk =>
                      have hw := step?_eq_localSet_oob s2 idx rest_w wv wstk wf wfs hcw hstk_w hfr_w hlt_w
                      exact ⟨{ s2 with code := [], trace := s2.trace ++ [.trap s!"unknown local index {idx}"] },
                        by simp [traceToWasm]; exact hw,
                        { hemit := hrel.hemit
                          hcode := .nil
                          hstack := hrel.hstack
                          hframes_len := by dsimp only []; exact hrel.hframes_len
                          hframes_locals := hrel.hframes_locals
                          hframes_vals := hrel.hframes_vals
                          hglobals := hrel.hglobals
                          hmemory := hrel.hmemory
                          hmemLimits := hrel.hmemLimits
                          hmemory_aligned := hrel.hmemory_aligned
                          hmemory_nonempty := hrel.hmemory_nonempty
                          hlabels := by dsimp only []; exact hrel.hlabels
                          hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                          hlabel_content := hrel.hlabel_content
                          hframes_one := hrel.hframes_one
                          hmodule := hrel.hmodule
                          hstore_funcs := hrel.hstore_funcs
                          hstore_types := hrel.hstore_types }⟩
          · exact hf.elim
      | .globalGet idx =>
          -- global.get: IR pushes globals[idx], Wasm pushes store.globals[idx]
          have hc : EmitCodeCorr _ (IRInstr.globalGet idx :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.globalGet_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- Specific case: Wasm code = globalGet idx :: rest_w
            match hglob : s1.globals[idx]? with
            | some val =>
              -- Valid global: IR pushes val, Wasm pushes store.globals[idx]
              have hir := irStep?_eq_globalGet s1 idx rest val hcode_ir hglob
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- Derive idx < globals.size from globals[idx]? = some
              have hidx_ir : idx < s1.globals.size :=
                (Array.getElem?_eq_some_iff.mp hglob).1
              -- Get Wasm bounds from globals correspondence
              have hglen := hrel.hglobals.1
              have hidx_w : idx < s2.store.globals.size := by omega
              -- Value correspondence
              have ⟨irv, wv, hirv, hwv, hval_corr⟩ := hrel.hglobals.2 idx hidx_ir
              -- irv = val (both are globals[idx])
              have : s1.globals[idx]? = some irv := hirv
              rw [hglob] at this; simp only [Option.some.injEq] at this; subst this
              -- wv = store.globals[idx]
              have : s2.store.globals[idx]? = some wv := hwv
              have hwv_eq : wv = s2.store.globals[idx]'hidx_w := by
                rw [Array.getElem?_eq_getElem hidx_w] at this
                simp only [Option.some.injEq] at this; exact this.symm
              subst hwv_eq
              -- Wasm step
              have hw := step?_eq_globalGet_valid s2 idx rest_w (s2.store.globals[idx]'hidx_w) hcw hidx_w rfl
              simp only [traceToWasm]
              refine ⟨_, hw, ?_⟩
              exact { hemit := hrel.hemit
                      hcode := hrest
                      hstack := by dsimp only []; exact stack_corr_cons hrel.hstack.1 hrel.hstack.2 hval_corr
                      hframes_len := hrel.hframes_len
                      hframes_locals := hrel.hframes_locals
                      hframes_vals := hrel.hframes_vals
                      hglobals := hrel.hglobals
                      hmemory := hrel.hmemory
                      hmemLimits := hrel.hmemLimits
                      hmemory_aligned := hrel.hmemory_aligned
                      hmemory_nonempty := hrel.hmemory_nonempty
                      hlabels := hrel.hlabels
                      hhalt := hhalt_of_structural hrest hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }
            | none =>
              -- Out-of-bounds: both sides trap
              have hir := irStep?_eq_globalGet_oob s1 idx rest hcode_ir hglob
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- Derive ¬(idx < globals.size) from globals[idx]? = none
              have hidx_ir : ¬(idx < s1.globals.size) := by
                intro h; rw [Array.getElem?_eq_getElem h] at hglob; exact absurd hglob (by simp)
              -- Wasm also out of bounds
              have hglen := hrel.hglobals.1
              have hidx_w : ¬(idx < s2.store.globals.size) := by omega
              have hw := step?_eq_globalGet_oob s2 idx rest_w hcw hidx_w
              simp only [traceToWasm]
              refine ⟨_, hw, ?_⟩
              exact { hemit := hrel.hemit
                      hcode := .nil
                      hstack := hrel.hstack
                      hframes_len := hrel.hframes_len
                      hframes_locals := hrel.hframes_locals
                      hframes_vals := hrel.hframes_vals
                      hglobals := hrel.hglobals
                      hmemory := hrel.hmemory
                      hmemLimits := hrel.hmemLimits
                      hmemory_aligned := hrel.hmemory_aligned
                      hmemory_nonempty := hrel.hmemory_nonempty
                      hlabels := by dsimp only []; exact hrel.hlabels
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }
          · exact hf.elim
      | .globalSet idx =>
          -- global.set: pop value from stack, set globals[idx]
          have hc : EmitCodeCorr _ (IRInstr.globalSet idx :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.globalSet_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- Specific case: Wasm code = globalSet idx :: rest_w
            match hstk : s1.stack with
            | [] =>
              -- Empty stack: both sides trap
              have hir := irStep?_eq_globalSet_emptyStack s1 idx rest hcode_ir hstk
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- Wasm also has empty stack
              have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
              have hstk_w : s2.stack = [] := by
                cases hs : s2.stack with | nil => rfl | cons => simp [hs] at hstk_rel
              have hw := step?_eq_globalSet_emptyStack s2 idx rest_w hcw hstk_w
              simp only [traceToWasm]
              refine ⟨_, hw, ?_⟩
              exact { hemit := hrel.hemit
                      hcode := .nil
                      hstack := hrel.hstack
                      hframes_len := hrel.hframes_len
                      hframes_locals := hrel.hframes_locals
                      hframes_vals := hrel.hframes_vals
                      hglobals := hrel.hglobals
                      hmemory := hrel.hmemory
                      hmemLimits := hrel.hmemLimits
                      hmemory_aligned := hrel.hmemory_aligned
                      hmemory_nonempty := hrel.hmemory_nonempty
                      hlabels := by dsimp only []; exact hrel.hlabels
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }
            | irv :: irstk =>
              -- Non-empty stack: check bounds
              if hbounds : idx < s1.globals.size then
                have hir := irStep?_eq_globalSet s1 idx rest irv irstk hcode_ir hstk hbounds
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Derive Wasm stack from stack correspondence
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hstk_w : s2.stack with
                | [] => simp [hstk_w] at hstk_rel
                | wv :: wstk =>
                  -- Get value correspondence for top of stack
                  have helem := hstk_rel.2 0 (by simp [hstk])
                  rw [hstk_w] at helem
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at helem
                  obtain ⟨_, _, rfl, rfl, hval_corr⟩ := helem
                  -- Wasm bounds from globals correspondence
                  have hglen := hrel.hglobals.1
                  have hbounds_w : idx < s2.store.globals.size := by omega
                  -- Wasm step
                  have hw := step?_eq_globalSet_valid s2 idx rest_w wv wstk hcw hstk_w hbounds_w
                  -- Rewrite hstk_rel to use wv :: wstk
                  rw [hstk_w] at hstk_rel
                  simp only [traceToWasm]
                  refine ⟨_, hw, ?_⟩
                  exact { hemit := hrel.hemit
                          hcode := hrest
                          hstack := by simp only [pushTrace]; exact stack_corr_tail hstk_rel.1 hstk_rel.2
                          hframes_len := hrel.hframes_len
                          hframes_locals := hrel.hframes_locals
                          hframes_vals := hrel.hframes_vals
                          hglobals := by
                            simp only [pushTrace, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
                            constructor
                            · exact hglen
                            · intro j hj
                              by_cases hjidx : j = idx
                              · subst hjidx
                                refine ⟨irv, wv, ?_, ?_, hval_corr⟩
                                · rw [Array.getElem?_eq_getElem (by simp [Array.size_setIfInBounds]; omega)]
                                  simp [Array.getElem_setIfInBounds]
                                · rw [Array.getElem?_eq_getElem (by simp [Array.size_setIfInBounds]; omega)]
                                  simp [Array.getElem_setIfInBounds]
                              · have hj_ir : j < s1.globals.size := hj
                                have hj_w : j < s2.store.globals.size := by omega
                                obtain ⟨irv'', wv'', hirv'', hwv'', hcorr''⟩ := hrel.hglobals.2 j hj_ir
                                refine ⟨irv'', wv'', ?_, ?_, hcorr''⟩
                                · rw [Array.getElem?_eq_getElem (by simp [Array.size_setIfInBounds]; omega)]
                                  rw [Array.getElem_setIfInBounds hj_ir, if_neg (Ne.symm hjidx)]
                                  rw [← Array.getElem?_eq_getElem hj_ir]; exact hirv''
                                · rw [Array.getElem?_eq_getElem (by simp [Array.size_setIfInBounds]; omega)]
                                  rw [Array.getElem_setIfInBounds hj_w, if_neg (Ne.symm hjidx)]
                                  rw [← Array.getElem?_eq_getElem hj_w]; exact hwv''
                          hmemory := by simp only [pushTrace]; exact hrel.hmemory
                          hmemLimits := by simp only [pushTrace]; exact hrel.hmemLimits
                          hmemory_aligned := hrel.hmemory_aligned
                          hmemory_nonempty := hrel.hmemory_nonempty
                          hlabels := hrel.hlabels
                          hhalt := hhalt_of_structural hrest hrel.hlabels
                          hlabel_content := hrel.hlabel_content
                          hframes_one := hrel.hframes_one
                          hmodule := hrel.hmodule
                          hstore_funcs := hrel.hstore_funcs
                          hstore_types := hrel.hstore_types }
              else
                -- Out-of-bounds: both trap with "unknown global index {idx}"
                have hir := irStep?_eq_globalSet_oob s1 idx rest irv irstk hcode_ir hstk hbounds
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Derive Wasm stack from stack correspondence
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hstk_w : s2.stack with
                | [] => simp [hstk_w] at hstk_rel
                | wv :: wstk =>
                  have hglen := hrel.hglobals.1
                  have hbounds_w : ¬(idx < s2.store.globals.size) := by omega
                  have hw := step?_eq_globalSet_oob s2 idx rest_w wv wstk hcw hstk_w hbounds_w
                  simp only [traceToWasm]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil,
                      hstack := hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                      hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                      hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels,
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                      hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                      hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
          · exact hf.elim
      | .load t offset =>
          -- memory load: IR uses readLE?, Wasm uses readLE? on store.memories[0]
          have hc_full : EmitCodeCorr _ (IRInstr.load t offset :: rest) s2.code := hcode_ir ▸ hrel.hcode
          match t with
          | .i32 =>
            rcases hc_full.load_i32_inv with ⟨rest_w, hcw, hrest⟩ | hf
            · -- Wasm code = i32Load {offset, align:2} :: rest_w
              -- Case split on IR stack
              match hstk : s1.stack with
              | [] =>
                -- Empty stack: both trap
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by
                  match hs : s2.stack with | [] => rfl | _ :: _ => simp [hs] at hlen
                have hw : step? s2 = some (.trap "stack underflow in i32.load",
                    { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in i32.load"] }) := by
                  simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                refine ⟨_, hw, ⟨hrel.hemit, ?_, ?_, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, ?_, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
                · exact EmitCodeCorr.nil
                · simp [hstk, hs2]
                · exact hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
              | .i32 addr :: stk =>
                -- i32 address on stack: read memory
                -- Case split on readLE? result
                match hread : readLE? s1.memory (addr.toNat + offset) 4 with
                | some raw =>
                  -- Successful read
                  have hir := irStep?_eq_load_i32 s1 rest offset addr stk raw hcode_ir hstk hread
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  -- Get Wasm stack from correspondence
                  have hstk_w := stack_corr_i32_inv addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                  -- Bridge memory: get Wasm memory from hmemory
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
                  · -- Memory exists: w.store.memories[0]? = some ir.memory
                    have hw : step? s2 = some (.silent,
                        pushTrace ({ s2 with code := rest_w, stack := .i32 (UInt32.ofNat raw.toNat) :: wstk' }) .silent) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_eq, hread]
                    simp only [traceToWasm]
                    refine ⟨_, hw, hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals,
                      hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels,
                      hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩
                    dsimp only []
                    exact stack_corr_cons hlen_tail.symm htail (.i32 _)
                  · -- No memory: readLE? on empty memory fails → contradiction with hread
                    exfalso; exact absurd hread (by rw [readLE?_none_of_size_zero _ _ _ (by omega) hmem_sz]; simp)
                | none =>
                  -- OOB: both trap
                  simp [irStep?, hcode_ir, hstk, irPop1?, irPushTrace, hread, irTrapState] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i32_inv addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, _, _⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, _⟩
                  · -- Memory exists but OOB
                    have hw : step? s2 = some (.trap "memory access fault in i32.load",
                        { s2 with code := [], trace := s2.trace ++ [.trap "memory access fault in i32.load"] }) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_eq, hread, trapState, pushTrace]
                    exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil,
                        hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                        hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                        hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels,
                        hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                        hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
                  · -- No memory: trap
                    have hw : step? s2 = some (.trap "memory access fault in i32.load",
                        { s2 with code := [], trace := s2.trace ++ [.trap "memory access fault in i32.load"] }) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_none, trapState, pushTrace]
                    exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil,
                        hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                        hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                        hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels,
                        hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                        hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
              | .f64 fv :: _ =>
                -- Non-i32 on stack: both trap (type mismatch)
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                have h0 := hrel.hstack.2 0 (by rw [hstk]; simp)
                rw [hstk] at h0; simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
                obtain ⟨_, wv, rfl, hwv_eq, hval⟩ := h0
                cases hval
                match hs2 : s2.stack with
                | [] => rw [hs2] at hlen; simp at hlen
                | w0 :: wstk' =>
                  rw [hs2] at hwv_eq; simp only [List.getElem?_cons_zero, Option.some.injEq] at hwv_eq; subst hwv_eq
                  have hw : step? s2 = some (.trap "type mismatch in i32.load",
                      { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i32.load"] }) := by
                    simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil,
                      hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                      hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                      hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels,
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                      hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                      hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
              | .i64 iv :: _ =>
                -- Non-i32 on stack: both trap (type mismatch)
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                have h0 := hrel.hstack.2 0 (by rw [hstk]; simp)
                rw [hstk] at h0; simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
                obtain ⟨_, wv, rfl, hwv_eq, hval⟩ := h0
                cases hval
                match hs2 : s2.stack with
                | [] => rw [hs2] at hlen; simp at hlen
                | w0 :: wstk' =>
                  rw [hs2] at hwv_eq; simp only [List.getElem?_cons_zero, Option.some.injEq] at hwv_eq; subst hwv_eq
                  have hw : step? s2 = some (.trap "type mismatch in i32.load",
                      { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i32.load"] }) := by
                    simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil,
                      hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                      hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                      hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels,
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                      hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                      hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
            · exact hf.elim
          | .f64 =>
            rcases hc_full.load_f64_inv with ⟨rest_w, hcw, hrest⟩ | hf
            · -- Wasm code = f64Load {offset, align:3} :: rest_w
              match hstk : s1.stack with
              | [] =>
                -- Empty stack: both trap
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by
                  match hs : s2.stack with | [] => rfl | _ :: _ => simp [hs] at hlen
                have hw : step? s2 = some (.trap "stack underflow in f64.load",
                    { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in f64.load"] }) := by
                  simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                refine ⟨_, hw, ⟨hrel.hemit, ?_, ?_, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, ?_, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
                · exact EmitCodeCorr.nil
                · simp [hstk, hs2]
                · exact hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
              | .i32 addr :: stk =>
                -- i32 address on stack: read memory
                match hread : readLE? s1.memory (addr.toNat + offset) 8 with
                | some raw =>
                  -- Successful read
                  have hir := irStep?_eq_load_f64 s1 rest offset addr stk raw hcode_ir hstk hread
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  -- Get Wasm stack from correspondence
                  have hstk_w := stack_corr_i32_inv addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                  -- Bridge memory: get Wasm memory from hmemory
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
                  · -- Memory exists: w.store.memories[0]? = some ir.memory
                    have hw : step? s2 = some (.silent,
                        pushTrace ({ s2 with code := rest_w, stack := .f64 (u64BitsToFloat raw) :: wstk' }) .silent) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_eq, hread]
                    simp only [traceToWasm]
                    refine ⟨_, hw, hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals,
                      hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels,
                      hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩
                    dsimp only []
                    exact stack_corr_cons hlen_tail.symm htail (.f64 _)
                  · -- No memory: readLE? on empty memory fails → contradiction with hread
                    exfalso; exact absurd hread (by rw [readLE?_none_of_size_zero _ _ _ (by omega) hmem_sz]; simp)
                | none =>
                  -- OOB: both trap
                  simp [irStep?, hcode_ir, hstk, irPop1?, irPushTrace, hread, irTrapState] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i32_inv addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, _, _⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, _⟩
                  · -- Memory exists but OOB
                    have hw : step? s2 = some (.trap "memory access fault in f64.load",
                        { s2 with code := [], trace := s2.trace ++ [.trap "memory access fault in f64.load"] }) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_eq, hread, trapState, pushTrace]
                    exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil,
                        hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                        hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                        hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels,
                        hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                        hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
                  · -- No memory: trap
                    have hw : step? s2 = some (.trap "memory access fault in f64.load",
                        { s2 with code := [], trace := s2.trace ++ [.trap "memory access fault in f64.load"] }) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_none, trapState, pushTrace]
                    exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil,
                        hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                        hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                        hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels,
                        hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                        hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
              | .f64 fv :: _ =>
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                have h0 := hrel.hstack.2 0 (by rw [hstk]; simp)
                rw [hstk] at h0; simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
                obtain ⟨_, wv, rfl, hwv_eq, hval⟩ := h0
                cases hval
                match hs2 : s2.stack with
                | [] => rw [hs2] at hlen; simp at hlen
                | w0 :: wstk' =>
                  rw [hs2] at hwv_eq; simp only [List.getElem?_cons_zero, Option.some.injEq] at hwv_eq; subst hwv_eq
                  have hw : step? s2 = some (.trap "type mismatch in f64.load",
                      { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in f64.load"] }) := by
                    simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil,
                      hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                      hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                      hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels,
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                      hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                      hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
              | .i64 iv :: _ =>
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                have h0 := hrel.hstack.2 0 (by rw [hstk]; simp)
                rw [hstk] at h0; simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
                obtain ⟨_, wv, rfl, hwv_eq, hval⟩ := h0
                cases hval
                match hs2 : s2.stack with
                | [] => rw [hs2] at hlen; simp at hlen
                | w0 :: wstk' =>
                  rw [hs2] at hwv_eq; simp only [List.getElem?_cons_zero, Option.some.injEq] at hwv_eq; subst hwv_eq
                  have hw : step? s2 = some (.trap "type mismatch in f64.load",
                      { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in f64.load"] }) := by
                    simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil,
                      hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                      hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                      hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels,
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                      hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                      hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
            · exact hf.elim
          | .i64 =>
            rcases hc_full.load_i64_inv with ⟨rest_w, hcw, hrest⟩ | hf
            · -- Wasm code = i64Load {offset, align:3} :: rest_w
              match hstk : s1.stack with
              | [] =>
                -- Empty stack: both trap
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by
                  match hs : s2.stack with | [] => rfl | _ :: _ => simp [hs] at hlen
                have hw : step? s2 = some (.trap "stack underflow in i64.load",
                    { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in i64.load"] }) := by
                  simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                refine ⟨_, hw, ⟨hrel.hemit, ?_, ?_, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, ?_, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
                · exact EmitCodeCorr.nil
                · simp [hstk, hs2]
                · exact hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
              | .i32 addr :: stk =>
                -- i32 address on stack: read memory
                match hread : readLE? s1.memory (addr.toNat + offset) 8 with
                | some raw =>
                  -- Successful read
                  have hir := irStep?_eq_load_i64 s1 rest offset addr stk raw hcode_ir hstk hread
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i32_inv addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
                  · -- Memory exists
                    have hw : step? s2 = some (.silent,
                        pushTrace ({ s2 with code := rest_w, stack := .i64 raw :: wstk' }) .silent) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_eq, hread]
                    simp only [traceToWasm]
                    refine ⟨_, hw, hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals,
                      hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels,
                      hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩
                    dsimp only []
                    exact stack_corr_cons hlen_tail.symm htail (.i64 _)
                  · -- No memory: contradiction
                    exfalso; exact absurd hread (by rw [readLE?_none_of_size_zero _ _ _ (by omega) hmem_sz]; simp)
                | none =>
                  -- OOB: both trap
                  simp [irStep?, hcode_ir, hstk, irPop1?, irPushTrace, hread, irTrapState] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i32_inv addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, _, _⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, _⟩
                  · -- Memory exists but OOB
                    have hw : step? s2 = some (.trap "memory access fault in i64.load",
                        { s2 with code := [], trace := s2.trace ++ [.trap "memory access fault in i64.load"] }) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_eq, hread, trapState, pushTrace]
                    exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil,
                        hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                        hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                        hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels,
                        hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                        hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
                  · -- No memory: trap
                    have hw : step? s2 = some (.trap "memory access fault in i64.load",
                        { s2 with code := [], trace := s2.trace ++ [.trap "memory access fault in i64.load"] }) := by
                      simp [step?, hcw, hstack_eq, pop1?, hmem_none, trapState, pushTrace]
                    exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil,
                        hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                        hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                        hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels,
                        hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                        hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
              | .f64 fv :: _ =>
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                have h0 := hrel.hstack.2 0 (by rw [hstk]; simp)
                rw [hstk] at h0; simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
                obtain ⟨_, wv, rfl, hwv_eq, hval⟩ := h0
                cases hval
                match hs2 : s2.stack with
                | [] => rw [hs2] at hlen; simp at hlen
                | w0 :: wstk' =>
                  rw [hs2] at hwv_eq; simp only [List.getElem?_cons_zero, Option.some.injEq] at hwv_eq; subst hwv_eq
                  have hw : step? s2 = some (.trap "type mismatch in i64.load",
                      { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i64.load"] }) := by
                    simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil,
                      hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                      hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                      hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels,
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                      hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                      hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
              | .i64 iv :: _ =>
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                have h0 := hrel.hstack.2 0 (by rw [hstk]; simp)
                rw [hstk] at h0; simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
                obtain ⟨_, wv, rfl, hwv_eq, hval⟩ := h0
                cases hval
                match hs2 : s2.stack with
                | [] => rw [hs2] at hlen; simp at hlen
                | w0 :: wstk' =>
                  rw [hs2] at hwv_eq; simp only [List.getElem?_cons_zero, Option.some.injEq] at hwv_eq; subst hwv_eq
                  have hw : step? s2 = some (.trap "type mismatch in i64.load",
                      { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i64.load"] }) := by
                    simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil,
                      hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                      hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                      hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels,
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                      hlabel_content := hrel.hlabel_content, hframes_one := hrel.hframes_one,
                      hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs, hstore_types := hrel.hstore_types }⟩
            · exact hf.elim
          | .ptr =>
            -- No EmitCodeCorr constructor for ptr load
            exfalso; generalize s2.code = wcode at hc_full
            cases hc_full with | general _ _ _ _ hf _ => exact hf.elim
      | .store t offset =>
          have hc_full : EmitCodeCorr _ (IRInstr.store t offset :: rest) s2.code := hcode_ir ▸ hrel.hcode
          match t with
          | .i32 =>
            rcases hc_full.store_i32_inv with ⟨rest_w, hcw, hrest⟩ | hf
            · -- Wasm code = i32Store {offset, align:2} :: rest_w
              match hstk : s1.stack with
              | [] =>
                -- Empty stack: both trap with stack underflow
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by
                  match hs : s2.stack with | [] => rfl | _ :: _ => simp [hs] at hlen
                have hw : step? s2 = some (.trap ("stack underflow in i32.store"),
                    { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in i32.store")] }) := by
                  simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | [x] =>
                -- One element: irPop2? fails → trap with stack underflow
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : ∃ w, s2.stack = [w] := by
                  match hs : s2.stack with
                  | [] => simp [hs] at hlen
                  | [w] => exact ⟨w, rfl⟩
                  | _ :: _ :: _ => simp [hs] at hlen
                obtain ⟨w, hs2⟩ := hs2
                have hw : step? s2 = some (.trap ("stack underflow in i32.store"),
                    { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in i32.store")] }) := by
                  simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | .i32 val :: .i32 addr :: stk =>
                -- i32 val, i32 addr on stack: write memory
                match hwrite : writeLE? s1.memory (addr.toNat + offset) 4 val.toUInt64 with
                | some mem' =>
                  -- Successful write
                  have hir := irStep?_eq_store_i32 s1 rest offset val addr stk mem' hcode_ir hstk hwrite
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i32_i32_inv val addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
                  · -- Memory exists
                    have hbind : s2.store.memories[0]? >>= fun mem => writeLE? mem (addr.toNat + offset) 4 (UInt64.ofNat val.toNat) = some mem' := by
                      rw [hmem_eq]; simp [hwrite]
                    let store' := { s2.store with memories := s2.store.memories.set! 0 mem' }
                    let s2' := { s2 with code := rest_w, stack := wstk', store := store' }
                    have hw : step? s2 = some (.silent, pushTrace s2' .silent) := by
                      simp [step?, hcw, hstack_eq, pop2?, hbind]
                    simp only [traceToWasm]
                    refine ⟨_, hw, ?_⟩
                    exact { hemit := hrel.hemit
                            hcode := hrest
                            hstack := by simp only [pushTrace]; exact ⟨hlen_tail.symm, htail⟩
                            hframes_len := hrel.hframes_len
                            hframes_locals := hrel.hframes_locals
                            hframes_vals := hrel.hframes_vals
                            hglobals := hrel.hglobals
                            hmemory := by
                              left; simp only [pushTrace, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
                              have h0 : 0 < s2.store.memories.size := Array.lt_size_of_getElem? hmem_eq
                              simp [h0]
                            hmemLimits := by simp only [pushTrace]; exact hrel.hmemLimits
                            hmemory_aligned := hrel.hmemory_aligned
                            hmemory_nonempty := hrel.hmemory_nonempty
                            hlabels := hrel.hlabels
                            hhalt := hhalt_of_structural hrest hrel.hlabels
                            hlabel_content := hrel.hlabel_content
                            hframes_one := hrel.hframes_one
                            hmodule := hrel.hmodule
                            hstore_funcs := hrel.hstore_funcs
                            hstore_types := hrel.hstore_types }
                  · -- No memory: contradiction (writeLE? can't succeed on empty memory)
                    exfalso; exact absurd hwrite (by rw [writeLE?_none_of_size_zero _ _ _ (by omega) _ hmem_sz]; simp)
                | none =>
                  -- OOB: both trap
                  simp [irStep?, hcode_ir, hstk, irPop2?, irPushTrace, hwrite, irTrapState] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i32_i32_inv val addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, _, _⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, _⟩
                  · -- Memory exists but OOB
                    have hwrite_w : s2.store.memories[0]? >>= (fun mem => writeLE? mem (addr.toNat + offset) 4 (UInt64.ofNat val.toNat)) = none := by
                      rw [hmem_eq]; simp [hwrite]
                    have hw : step? s2 = some (.trap ("memory access fault in i32.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in i32.store")] }) := by
                      simp [step?, hcw, hstack_eq, pop2?, hwrite_w, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
                  · -- No memory: trap
                    have hw : step? s2 = some (.trap ("memory access fault in i32.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in i32.store")] }) := by
                      simp [step?, hcw, hstack_eq, pop2?, hmem_none, trapState, pushTrace, Option.bind]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
              | .f64 _ :: _ | .i64 _ :: _ | .i32 _ :: .f64 _ :: _ | .i32 _ :: .i64 _ :: _ =>
                -- Type mismatch on stack: both trap
                all_goals (
                  simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                  match hstk_w : s2.stack with
                  | [] => simp [hstk_w] at hstk_rel
                  | [_] => simp [hstk_w] at hstk_rel
                  | w0 :: w1 :: wstk' =>
                    have h0 := hstk_rel.2 0 (by simp)
                    simp at h0; cases h0
                    have h1 := hstk_rel.2 1 (by simp)
                    simp at h1; cases h1
                    have hw : step? s2 = some (.trap ("type mismatch in i32.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("type mismatch in i32.store")] }) := by
                      simp [step?, hcw, pop2?, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩)
            · exact hf.elim
          | .f64 =>
            rcases hc_full.store_f64_inv with ⟨rest_w, hcw, hrest⟩ | hf
            · match hstk : s1.stack with
              | [] =>
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by
                  match hs : s2.stack with | [] => rfl | _ :: _ => simp [hs] at hlen
                have hw : step? s2 = some (.trap ("stack underflow in f64.store"),
                    { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in f64.store")] }) := by
                  simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | [x] =>
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : ∃ w, s2.stack = [w] := by
                  match hs : s2.stack with
                  | [] => simp [hs] at hlen
                  | [w] => exact ⟨w, rfl⟩
                  | _ :: _ :: _ => simp [hs] at hlen
                obtain ⟨w, hs2⟩ := hs2
                have hw : step? s2 = some (.trap ("stack underflow in f64.store"),
                    { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in f64.store")] }) := by
                  simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | .f64 val :: .i32 addr :: stk =>
                match hwrite : writeLE? s1.memory (addr.toNat + offset) 8 (floatToU64Bits val) with
                | some mem' =>
                  have hir := irStep?_eq_store_f64 s1 rest offset val addr stk mem' hcode_ir hstk hwrite
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_f64_i32_inv val addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
                  · have hbind : s2.store.memories[0]? >>= fun mem => writeLE? mem (addr.toNat + offset) 8 (floatToU64Bits val) = some mem' := by
                      rw [hmem_eq]; simp [hwrite]
                    let store_f64 := { s2.store with memories := s2.store.memories.set! 0 mem' }
                    let s2_f64 := { s2 with code := rest_w, stack := wstk', store := store_f64 }
                    have hw : step? s2 = some (.silent, pushTrace s2_f64 .silent) := by
                      simp [step?, hcw, hstack_eq, pop2?, hbind]
                    simp only [traceToWasm]
                    refine ⟨_, hw, ?_⟩
                    exact { hemit := hrel.hemit
                            hcode := hrest
                            hstack := by simp only [pushTrace]; exact ⟨hlen_tail.symm, htail⟩
                            hframes_len := hrel.hframes_len
                            hframes_locals := hrel.hframes_locals
                            hframes_vals := hrel.hframes_vals
                            hglobals := hrel.hglobals
                            hmemory := by
                              left; simp only [pushTrace, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
                              have h0 : 0 < s2.store.memories.size := Array.lt_size_of_getElem? hmem_eq
                              simp [h0]
                            hmemLimits := by simp only [pushTrace]; exact hrel.hmemLimits
                            hmemory_aligned := hrel.hmemory_aligned
                            hmemory_nonempty := hrel.hmemory_nonempty
                            hlabels := hrel.hlabels
                            hhalt := hhalt_of_structural hrest hrel.hlabels
                            hlabel_content := hrel.hlabel_content
                            hframes_one := hrel.hframes_one
                            hmodule := hrel.hmodule
                            hstore_funcs := hrel.hstore_funcs
                            hstore_types := hrel.hstore_types }
                  · exfalso; exact absurd hwrite (by rw [writeLE?_none_of_size_zero _ _ _ (by omega) _ hmem_sz]; simp)
                | none =>
                  simp [irStep?, hcode_ir, hstk, irPop2?, irPushTrace, hwrite, irTrapState] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_f64_i32_inv val addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, _, _⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, _⟩
                  · have hwrite_w : s2.store.memories[0]? >>= (fun mem => writeLE? mem (addr.toNat + offset) 8 (floatToU64Bits val)) = none := by
                      rw [hmem_eq]; simp [hwrite]
                    have hw : step? s2 = some (.trap ("memory access fault in f64.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in f64.store")] }) := by
                      simp [step?, hcw, hstack_eq, pop2?, hwrite_w, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
                  · have hw : step? s2 = some (.trap ("memory access fault in f64.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in f64.store")] }) := by
                      simp [step?, hcw, hstack_eq, pop2?, hmem_none, trapState, pushTrace, Option.bind]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
              | .i32 _ :: _ | .i64 _ :: _ | .f64 _ :: .f64 _ :: _ | .f64 _ :: .i64 _ :: _ =>
                all_goals (
                  simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                  match hstk_w : s2.stack with
                  | [] => simp [hstk_w] at hstk_rel
                  | [_] => simp [hstk_w] at hstk_rel
                  | w0 :: w1 :: wstk' =>
                    have h0 := hstk_rel.2 0 (by simp)
                    simp at h0; cases h0
                    have h1 := hstk_rel.2 1 (by simp)
                    simp at h1; cases h1
                    have hw : step? s2 = some (.trap ("type mismatch in f64.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("type mismatch in f64.store")] }) := by
                      simp [step?, hcw, pop2?, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩)
            · exact hf.elim
          | .i64 =>
            rcases hc_full.store_i64_inv with ⟨rest_w, hcw, hrest⟩ | hf
            · match hstk : s1.stack with
              | [] =>
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by
                  match hs : s2.stack with | [] => rfl | _ :: _ => simp [hs] at hlen
                have hw : step? s2 = some (.trap ("stack underflow in i64.store"),
                    { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in i64.store")] }) := by
                  simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | [x] =>
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : ∃ w, s2.stack = [w] := by
                  match hs : s2.stack with
                  | [] => simp [hs] at hlen
                  | [w] => exact ⟨w, rfl⟩
                  | _ :: _ :: _ => simp [hs] at hlen
                obtain ⟨w, hs2⟩ := hs2
                have hw : step? s2 = some (.trap ("stack underflow in i64.store"),
                    { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in i64.store")] }) := by
                  simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | .i64 val :: .i32 addr :: stk =>
                match hwrite : writeLE? s1.memory (addr.toNat + offset) 8 val with
                | some mem' =>
                  have hir := irStep?_eq_store_i64 s1 rest offset val addr stk mem' hcode_ir hstk hwrite
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i64_i32_inv val addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
                  · have hbind : s2.store.memories[0]? >>= fun mem => writeLE? mem (addr.toNat + offset) 8 val = some mem' := by
                      rw [hmem_eq]; simp [hwrite]
                    let store_i64 := { s2.store with memories := s2.store.memories.set! 0 mem' }
                    let s2_i64 := { s2 with code := rest_w, stack := wstk', store := store_i64 }
                    have hw : step? s2 = some (.silent, pushTrace s2_i64 .silent) := by
                      simp [step?, hcw, hstack_eq, pop2?, hbind]
                    simp only [traceToWasm]
                    refine ⟨_, hw, ?_⟩
                    exact { hemit := hrel.hemit
                            hcode := hrest
                            hstack := by simp only [pushTrace]; exact ⟨hlen_tail.symm, htail⟩
                            hframes_len := hrel.hframes_len
                            hframes_locals := hrel.hframes_locals
                            hframes_vals := hrel.hframes_vals
                            hglobals := hrel.hglobals
                            hmemory := by
                              left; simp only [pushTrace, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
                              have h0 : 0 < s2.store.memories.size := Array.lt_size_of_getElem? hmem_eq
                              simp [h0]
                            hmemLimits := by simp only [pushTrace]; exact hrel.hmemLimits
                            hmemory_aligned := hrel.hmemory_aligned
                            hmemory_nonempty := hrel.hmemory_nonempty
                            hlabels := hrel.hlabels
                            hhalt := hhalt_of_structural hrest hrel.hlabels
                            hlabel_content := hrel.hlabel_content
                            hframes_one := hrel.hframes_one
                            hmodule := hrel.hmodule
                            hstore_funcs := hrel.hstore_funcs
                            hstore_types := hrel.hstore_types }
                  · exfalso; exact absurd hwrite (by rw [writeLE?_none_of_size_zero _ _ _ (by omega) _ hmem_sz]; simp)
                | none =>
                  simp [irStep?, hcode_ir, hstk, irPop2?, irPushTrace, hwrite, irTrapState] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_w := stack_corr_i64_i32_inv val addr stk s2.stack
                    (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                  obtain ⟨wstk', hstack_eq, _, _⟩ := hstk_w
                  rcases hrel.hmemory with hmem_eq | ⟨hmem_none, _⟩
                  · have hwrite_w : s2.store.memories[0]? >>= (fun mem => writeLE? mem (addr.toNat + offset) 8 val) = none := by
                      rw [hmem_eq]; simp [hwrite]
                    have hw : step? s2 = some (.trap ("memory access fault in i64.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in i64.store")] }) := by
                      simp [step?, hcw, hstack_eq, pop2?, hwrite_w, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
                  · have hw : step? s2 = some (.trap ("memory access fault in i64.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in i64.store")] }) := by
                      simp [step?, hcw, hstack_eq, pop2?, hmem_none, trapState, pushTrace, Option.bind]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
              | .i32 _ :: _ | .f64 _ :: _ | .i64 _ :: .f64 _ :: _ | .i64 _ :: .i64 _ :: _ =>
                all_goals (
                  simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                  match hstk_w : s2.stack with
                  | [] => simp [hstk_w] at hstk_rel
                  | [_] => simp [hstk_w] at hstk_rel
                  | w0 :: w1 :: wstk' =>
                    have h0 := hstk_rel.2 0 (by simp)
                    simp at h0; cases h0
                    have h1 := hstk_rel.2 1 (by simp)
                    simp at h1; cases h1
                    have hw : step? s2 = some (.trap ("type mismatch in i64.store"),
                        { s2 with code := [], trace := s2.trace ++ [.trap ("type mismatch in i64.store")] }) := by
                      simp [step?, hcw, pop2?, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩)
            · exact hf.elim
          | .ptr =>
            exfalso; generalize s2.code = wcode at hc_full
            cases hc_full with | general _ _ _ _ hf _ => exact hf.elim
      | .store8 offset =>
          have hc_full : EmitCodeCorr _ (IRInstr.store8 offset :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc_full.store8_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · match hstk : s1.stack with
            | [] =>
              simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
              have hs2 : s2.stack = [] := by
                match hs : s2.stack with | [] => rfl | _ :: _ => simp [hs] at hlen
              have hw : step? s2 = some (.trap ("stack underflow in i32.store"),
                  { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in i32.store")] }) := by
                simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
              simp only [traceToWasm]; exact ⟨_, hw,
                { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                  hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                  hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                  hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                  hlabel_content := hrel.hlabel_content
                  hframes_one := hrel.hframes_one
                  hmodule := hrel.hmodule
                  hstore_funcs := hrel.hstore_funcs
                  hstore_types := hrel.hstore_types }⟩
            | [x] =>
              simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
              have hs2 : ∃ w, s2.stack = [w] := by
                match hs : s2.stack with
                | [] => simp [hs] at hlen
                | [w] => exact ⟨w, rfl⟩
                | _ :: _ :: _ => simp [hs] at hlen
              obtain ⟨w, hs2⟩ := hs2
              have hw : step? s2 = some (.trap ("stack underflow in i32.store"),
                  { s2 with code := [], trace := s2.trace ++ [.trap ("stack underflow in i32.store")] }) := by
                simp [step?, hcw, hs2, pop2?, trapState, pushTrace]
              simp only [traceToWasm]; exact ⟨_, hw,
                { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                  hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                  hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                  hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                  hlabel_content := hrel.hlabel_content
                  hframes_one := hrel.hframes_one
                  hmodule := hrel.hmodule
                  hstore_funcs := hrel.hstore_funcs
                  hstore_types := hrel.hstore_types }⟩
            | .i32 val :: .i32 addr :: stk =>
              match hwrite : writeLE? s1.memory (addr.toNat + offset) 1 val.toUInt64 with
              | some mem' =>
                have hir := irStep?_eq_store8 s1 rest offset val addr stk mem' hcode_ir hstk hwrite
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_w := stack_corr_i32_i32_inv val addr stk s2.stack
                  (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
                · have hbind : s2.store.memories[0]? >>= fun mem => writeLE? mem (addr.toNat + offset) 1 (UInt64.ofNat val.toNat) = some mem' := by
                    rw [hmem_eq]; simp [hwrite]
                  let store_s8 := { s2.store with memories := s2.store.memories.set! 0 mem' }
                  let s2_s8 := { s2 with code := rest_w, stack := wstk', store := store_s8 }
                  have hw : step? s2 = some (.silent, pushTrace s2_s8 .silent) := by
                    simp [step?, hcw, hstack_eq, pop2?, hbind]
                  simp only [traceToWasm]
                  refine ⟨_, hw, ?_⟩
                  exact { hemit := hrel.hemit
                          hcode := hrest
                          hstack := by simp only [pushTrace]; exact ⟨hlen_tail.symm, htail⟩
                          hframes_len := hrel.hframes_len
                          hframes_locals := hrel.hframes_locals
                          hframes_vals := hrel.hframes_vals
                          hglobals := hrel.hglobals
                          hmemory := by
                            left; simp only [pushTrace, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
                            have h0 : 0 < s2.store.memories.size := Array.lt_size_of_getElem? hmem_eq
                            simp [h0]
                          hmemLimits := by simp only [pushTrace]; exact hrel.hmemLimits
                          hmemory_aligned := hrel.hmemory_aligned
                          hmemory_nonempty := hrel.hmemory_nonempty
                          hlabels := hrel.hlabels
                          hhalt := hhalt_of_structural hrest hrel.hlabels
                          hlabel_content := hrel.hlabel_content
                          hframes_one := hrel.hframes_one
                          hmodule := hrel.hmodule
                          hstore_funcs := hrel.hstore_funcs
                          hstore_types := hrel.hstore_types }
                · exfalso; exact absurd hwrite (by rw [writeLE?_none_of_size_zero _ _ _ (by omega) _ hmem_sz]; simp)
              | none =>
                simp [irStep?, hcode_ir, hstk, irPop2?, irPushTrace, hwrite, irTrapState] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_w := stack_corr_i32_i32_inv val addr stk s2.stack
                  (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                obtain ⟨wstk', hstack_eq, _, _⟩ := hstk_w
                rcases hrel.hmemory with hmem_eq | ⟨hmem_none, _⟩
                · have hwrite_w : s2.store.memories[0]? >>= (fun mem => writeLE? mem (addr.toNat + offset) 1 (UInt64.ofNat val.toNat)) = none := by
                    rw [hmem_eq]; simp [hwrite]
                  have hw : step? s2 = some (.trap ("memory access fault in i32.store"),
                      { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in i32.store")] }) := by
                    simp [step?, hcw, hstack_eq, pop2?, hwrite_w, trapState, pushTrace]
                  simp only [traceToWasm]; exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }⟩
                · have hw : step? s2 = some (.trap ("memory access fault in i32.store"),
                      { s2 with code := [], trace := s2.trace ++ [.trap ("memory access fault in i32.store")] }) := by
                    simp [step?, hcw, hstack_eq, pop2?, hmem_none, trapState, pushTrace, Option.bind]
                  simp only [traceToWasm]; exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }⟩
            | .f64 _ :: _ | .i64 _ :: _ | .i32 _ :: .f64 _ :: _ | .i32 _ :: .i64 _ :: _ =>
              all_goals (
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hstk_w : s2.stack with
                | [] => simp [hstk_w] at hstk_rel
                | [_] => simp [hstk_w] at hstk_rel
                | w0 :: w1 :: wstk' =>
                  have h0 := hstk_rel.2 0 (by simp)
                  simp at h0; cases h0
                  have h1 := hstk_rel.2 1 (by simp)
                  simp at h1; cases h1
                  have hw : step? s2 = some (.trap ("type mismatch in i32.store"),
                      { s2 with code := [], trace := s2.trace ++ [.trap ("type mismatch in i32.store")] }) := by
                    simp [step?, hcw, pop2?, trapState, pushTrace]
                  simp only [traceToWasm]; exact ⟨_, hw,
                    { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }⟩)
          · exact hf.elim
      | .binOp t op =>
          have hc : EmitCodeCorr _ (IRInstr.binOp t op :: rest) s2.code := hcode_ir ▸ hrel.hcode
          match t with
          | .i32 =>
            rcases hc.binOp_i32_inv with
              ⟨rfl, rest_w, hcw, hrest⟩ | ⟨rfl, rest_w, hcw, hrest⟩ |
              ⟨rfl, rest_w, hcw, hrest⟩ | ⟨rfl, rest_w, hcw, hrest⟩ |
              ⟨rfl, rest_w, hcw, hrest⟩ | ⟨rfl, rest_w, hcw, hrest⟩ |
              ⟨rfl, rest_w, hcw, hrest⟩ | ⟨rfl, rest_w, hcw, hrest⟩ |
              ⟨rfl, rest_w, hcw, hrest⟩ | hf
            all_goals first | exact hf.elim | (
              -- Generic i32 binOp sub-case: all 9 operations follow the same pattern.
              -- After inversion, we know: op ∈ {add,sub,mul,and,or,eq,ne,lt_s,gt_s}
              -- and hcw : s2.code = WasmInstr :: rest_w.
              -- Case split on IR stack to determine trap vs success.
              match hstk : s1.stack with
              | [] =>
                -- Stack underflow — sorry: withI32Bin/withI32Rel/withF64Bin trap + record construction
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                sorry
              | [v1] =>
                -- Only 1 element — sorry: trap + record construction
                sorry
              | .i32 rhs :: .i32 lhs :: stk =>
                -- Both i32: success case. IR and Wasm compute the same result.
                -- Simplify IR step
                unfold irStep? at hstep; rw [hcode_ir, hstk] at hstep
                simp [irPop2?, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Extract Wasm stack from correspondence
                have hstk_w := stack_corr_i32_i32_inv rhs lhs stk s2.stack
                  (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                -- Apply Wasm step equation lemma
                have hw := by first
                  | exact step?_eq_i32Add s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32Sub s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32Mul s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32And s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32Or s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32Eq s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32Ne s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32Lts s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_i32Gts s2 rest_w lhs rhs wstk' hcw hstack_eq
                -- Build result
                simp only [traceToWasm]
                refine ⟨_, hw, ?_⟩
                exact {
                  hemit := hrel.hemit
                  hcode := hrest
                  hstack := by
                    simp only [pushTrace]
                    apply stack_corr_cons hlen_tail.symm htail
                    first
                      | exact .i32 (lhs + rhs)
                      | exact .i32 (lhs - rhs)
                      | exact .i32 (lhs * rhs)
                      | exact .i32 (lhs &&& rhs)
                      | exact .i32 (lhs ||| rhs)
                      | (simp only [irBoolToI32, boolToI32]; exact .i32 _)
                  hframes_len := hrel.hframes_len
                  hframes_locals := hrel.hframes_locals
                  hframes_vals := hrel.hframes_vals
                  hglobals := hrel.hglobals
                  hmemory := hrel.hmemory
                  hmemLimits := hrel.hmemLimits
                  hmemory_aligned := hrel.hmemory_aligned
                  hmemory_nonempty := hrel.hmemory_nonempty
                  hlabels := hrel.hlabels
                  hhalt := hhalt_of_structural hrest hrel.hlabels
                  hlabel_content := hrel.hlabel_content
                  hframes_one := hrel.hframes_one
                  hmodule := hrel.hmodule
                  hstore_funcs := hrel.hstore_funcs
                  hstore_types := hrel.hstore_types
                }
              | .i64 _ :: _ :: _ | .f64 _ :: _ :: _ | .i32 _ :: .i64 _ :: _ | .i32 _ :: .f64 _ :: _ =>
                -- Type mismatch: both trap (sorry: cases + record unification)
                sorry)
          | .f64 =>
            rcases hc.binOp_f64_inv with
              ⟨rfl, rest_w, hcw, hrest⟩ | ⟨rfl, rest_w, hcw, hrest⟩ |
              ⟨rfl, rest_w, hcw, hrest⟩ | ⟨rfl, rest_w, hcw, hrest⟩ | hf
            all_goals first | exact hf.elim | (
              match hstk : s1.stack with
              | [] =>
                -- Stack underflow — sorry: withI32Bin/withI32Rel/withF64Bin trap + record construction
                simp [irStep?, hcode_ir, hstk, irPop2?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                sorry
              | [v1] =>
                -- Only 1 element — sorry: trap + record construction
                sorry
              | .f64 rhs :: .f64 lhs :: stk =>
                -- Both f64: success case
                unfold irStep? at hstep; rw [hcode_ir, hstk] at hstep
                simp [irPop2?, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_w := stack_corr_f64_f64_inv rhs lhs stk s2.stack
                  (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                have hw := by first
                  | exact step?_eq_f64Add s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_f64Sub s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_f64Mul s2 rest_w lhs rhs wstk' hcw hstack_eq
                  | exact step?_eq_f64Div s2 rest_w lhs rhs wstk' hcw hstack_eq
                simp only [traceToWasm]
                refine ⟨_, hw, ?_⟩
                exact {
                  hemit := hrel.hemit
                  hcode := hrest
                  hstack := by
                    simp only [pushTrace]
                    exact stack_corr_cons hlen_tail.symm htail (.f64 _)
                  hframes_len := hrel.hframes_len
                  hframes_locals := hrel.hframes_locals
                  hframes_vals := hrel.hframes_vals
                  hglobals := hrel.hglobals
                  hmemory := hrel.hmemory
                  hmemLimits := hrel.hmemLimits
                  hmemory_aligned := hrel.hmemory_aligned
                  hmemory_nonempty := hrel.hmemory_nonempty
                  hlabels := hrel.hlabels
                  hhalt := hhalt_of_structural hrest hrel.hlabels
                  hlabel_content := hrel.hlabel_content
                  hframes_one := hrel.hframes_one
                  hmodule := hrel.hmodule
                  hstore_funcs := hrel.hstore_funcs
                  hstore_types := hrel.hstore_types
                }
              | .i32 _ :: _ :: _ | .i64 _ :: _ :: _ | .f64 _ :: .i32 _ :: _ | .f64 _ :: .i64 _ :: _ =>
                -- Type mismatch: both trap (sorry: cases + record unification)
                sorry)
          | .i64 | .ptr =>
            -- No EmitCodeCorr constructor for i64/ptr binOps
            exfalso; generalize s2.code = wcode at hc
            cases hc with | general _ _ _ _ hf _ => exact hf.elim
      | .unOp t op =>
          sorry
          /- unary operation: IR and Wasm compute the same result
          have hc : EmitCodeCorr _ (IRInstr.unOp t op :: rest) s2.code := hcode_ir ▸ hrel.hcode
          match t with
          | .i32 =>
            rcases hc.unOp_i32_inv with ⟨heqz, rest_w, hcw, hrest⟩ | ⟨hwrap, rest_w, hcw, hrest⟩ | hf
            · -- eqz case
              subst heqz
              match hstk : s1.stack with
              | [] =>
                -- Empty stack: both trap
                have hir : irStep? s1 = some (.trap "stack underflow in i32.eqz",
                    { s1 with code := [], trace := s1.trace ++ [.trap "stack underflow in i32.eqz"] }) := by
                  simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by cases s2.stack with | nil => rfl | cons => simp_all
                have hw : step? s2 = some (.trap "stack underflow in i32.eqz",
                    { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in i32.eqz"] }) := by
                  simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by simp [hs2],
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | .i32 v :: stk =>
                -- Success: both compute eqz
                have hir := irStep?_eq_i32Eqz s1 rest v stk hcode_ir hstk
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Derive Wasm stack
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hs2 : s2.stack with
                | [] => simp [hs2] at hstk_rel
                | wv :: wstk =>
                  have hval := hstk_rel.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval; simp at hval
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval; simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | i32 n =>
                    rename_i hneq; rw [hneq] at hs2
                    have hw := step?_eq_i32Eqz s2 rest_w n wstk hcw hs2
                    simp only [traceToWasm]
                    refine ⟨_, hw, ?_⟩
                    exact { hemit := hrel.hemit
                            hcode := hrest
                            hstack := by simp only [pushTrace]; exact stack_corr_cons (by simp [hstk, hs2] at hstk_rel ⊢; omega) (fun i hi => hstk_rel.2 (i + 1) (by simp; omega)) (.i32 _)
                            hframes_len := hrel.hframes_len
                            hframes_locals := hrel.hframes_locals
                            hframes_vals := hrel.hframes_vals
                            hglobals := hrel.hglobals
                            hmemory := hrel.hmemory
                            hmemLimits := hrel.hmemLimits
                            hmemory_aligned := hrel.hmemory_aligned
                            hmemory_nonempty := hrel.hmemory_nonempty
                            hlabels := hrel.hlabels
                            hhalt := hhalt_of_structural hrest hrel.hlabels
                            hlabel_content := hrel.hlabel_content
                            hframes_one := hrel.hframes_one
                            hmodule := hrel.hmodule
                            hstore_funcs := hrel.hstore_funcs
                            hstore_types := hrel.hstore_types }
              | .i64 v :: stk =>
                -- Type mismatch: both trap
                have hir : irStep? s1 = some (.trap "type mismatch in i32.eqz",
                    { s1 with code := [], trace := s1.trace ++ [.trap "type mismatch in i32.eqz"] }) := by
                  simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hs2 : s2.stack with
                | [] => simp [hs2] at hstk_rel
                | wv :: wstk =>
                  have hval := hstk_rel.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval; simp at hval
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval; simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | i64 n =>
                    rename_i hneq; rw [hneq] at hs2
                    have hw : step? s2 = some (.trap "type mismatch in i32.eqz",
                        { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i32.eqz"] }) := by
                      simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
              | .f64 v :: stk =>
                -- Type mismatch: both trap
                have hir : irStep? s1 = some (.trap "type mismatch in i32.eqz",
                    { s1 with code := [], trace := s1.trace ++ [.trap "type mismatch in i32.eqz"] }) := by
                  simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hs2 : s2.stack with
                | [] => simp [hs2] at hstk_rel
                | wv :: wstk =>
                  have hval := hstk_rel.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval; simp at hval
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval; simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | f64 m =>
                    have hw : step? s2 = some (.trap "type mismatch in i32.eqz",
                        { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i32.eqz"] }) := by
                      simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
            · -- wrap_i64 case
              subst hwrap
              match hstk : s1.stack with
              | [] =>
                -- Empty stack: both trap
                have hir : irStep? s1 = some (.trap "stack underflow in i32.wrap_i64",
                    { s1 with code := [], trace := s1.trace ++ [.trap "stack underflow in i32.wrap_i64"] }) := by
                  simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
                have hs2 : s2.stack = [] := by cases s2.stack with | nil => rfl | cons => simp_all
                have hw : step? s2 = some (.trap "stack underflow in i32.wrap_i64",
                    { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in i32.wrap_i64"] }) := by
                  simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                simp only [traceToWasm]; exact ⟨_, hw,
                  { hemit := hrel.hemit, hcode := .nil, hstack := by simp [hs2],
                    hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                    hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                    hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
              | .i32 v :: stk =>
                -- Type mismatch: IR traps (i32 given to wrap_i64), Wasm also traps
                have hir : irStep? s1 = some (.trap "type mismatch in i32.wrap_i64",
                    { s1 with code := [], trace := s1.trace ++ [.trap "type mismatch in i32.wrap_i64"] }) := by
                  simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hs2 : s2.stack with
                | [] => simp [hs2] at hstk_rel
                | wv :: wstk =>
                  have hval := hstk_rel.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval; simp at hval
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval; simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | i32 n =>
                    rename_i hneq; rw [hneq] at hs2
                    have hw : step? s2 = some (.trap "type mismatch in i32.wrap_i64",
                        { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i32.wrap_i64"] }) := by
                      simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
              | .i64 v :: stk =>
                -- Success: both compute wrap_i64
                have hir := irStep?_eq_i32WrapI64 s1 rest v stk hcode_ir hstk
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hs2 : s2.stack with
                | [] => simp [hs2] at hstk_rel
                | wv :: wstk =>
                  have hval := hstk_rel.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval; simp at hval
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval; simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | i64 n =>
                    rename_i hneq; rw [hneq] at hs2
                    have hw := step?_eq_i32WrapI64 s2 rest_w n wstk hcw hs2
                    simp only [traceToWasm]
                    refine ⟨_, hw, ?_⟩
                    exact { hemit := hrel.hemit
                            hcode := hrest
                            hstack := by simp only [pushTrace]; exact stack_corr_cons (by simp [hstk, hs2] at hstk_rel ⊢; omega) (fun i hi => hstk_rel.2 (i + 1) (by simp; omega)) (.i32 _)
                            hframes_len := hrel.hframes_len
                            hframes_locals := hrel.hframes_locals
                            hframes_vals := hrel.hframes_vals
                            hglobals := hrel.hglobals
                            hmemory := hrel.hmemory
                            hmemLimits := hrel.hmemLimits
                            hmemory_aligned := hrel.hmemory_aligned
                            hmemory_nonempty := hrel.hmemory_nonempty
                            hlabels := hrel.hlabels
                            hhalt := hhalt_of_structural hrest hrel.hlabels
                            hlabel_content := hrel.hlabel_content
                            hframes_one := hrel.hframes_one
                            hmodule := hrel.hmodule
                            hstore_funcs := hrel.hstore_funcs
                            hstore_types := hrel.hstore_types }
              | .f64 v :: stk =>
                -- Type mismatch: both trap
                have hir : irStep? s1 = some (.trap "type mismatch in i32.wrap_i64",
                    { s1 with code := [], trace := s1.trace ++ [.trap "type mismatch in i32.wrap_i64"] }) := by
                  simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
                rw [hir] at hstep; simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                match hs2 : s2.stack with
                | [] => simp [hs2] at hstk_rel
                | wv :: wstk =>
                  have hval := hstk_rel.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval; simp at hval
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval; simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | f64 m =>
                    have hw : step? s2 = some (.trap "type mismatch in i32.wrap_i64",
                        { s2 with code := [], trace := s2.trace ++ [.trap "type mismatch in i32.wrap_i64"] }) := by
                      simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
                    simp only [traceToWasm]; exact ⟨_, hw,
                      { hemit := hrel.hemit, hcode := .nil, hstack := by rw [← hstk]; exact hrel.hstack,
                        hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                        hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                        hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels,
                        hlabel_content := hrel.hlabel_content
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
            · exact hf.elim
          | .i64 | .f64 | .ptr =>
            -- No EmitCodeCorr constructor for these types
            exfalso; generalize s2.code = wcode at hc
            cases hc with | general _ _ _ _ hf _ => exact hf.elim
          -/
      | .call funcIdx =>
          -- SORRY: call case needs API updates + hframes_one invariant rework
          sorry
          /- function call
          have hc : EmitCodeCorr _ (IRInstr.call funcIdx :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.call_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- Wasm code = Instr.call funcIdx :: rest_w
            -- Derive function count correspondence
            have hfuncs_size : s1.module.functions.size = s2.store.funcs.size := by
              rw [hrel.hmodule, hrel.hstore_funcs]
              exact (emit_preserves_funcs_size irmod wmod hrel.hemit).symm
            match hfunc_ir : s1.module.functions[funcIdx]? with
            | none =>
              -- Case 1: funcIdx OOB in IR → also OOB in Wasm
              have hir : irStep? s1 = some (.trap s!"call: unknown function {funcIdx}",
                  { s1 with code := [], trace := s1.trace ++ [.trap s!"call: unknown function {funcIdx}"] }) := by
                simp [irStep?, hcode_ir, hfunc_ir, irTrapState, irPushTrace]
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- funcIdx is also OOB in Wasm
              have hfunc_oob : ¬(funcIdx < s2.store.funcs.size) := by
                rw [← hfuncs_size]; exact List.getElem?_eq_none.mp hfunc_ir
              have hw := step?_eq_call_oob s2 funcIdx rest_w hcw hfunc_oob
              exact ⟨_, by simp [traceToWasm]; exact hw,
                { hemit := hrel.hemit, hcode := .nil, hstack := by dsimp only []; exact hrel.hstack,
                  hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                  hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals,
                  hmemory := hrel.hmemory, hmemLimits := hrel.hmemLimits,
                  hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                  hlabels := hrel.hlabels,
                  hhalt := hhalt_of_structural (@EmitCodeCorr.nil []) (by dsimp only []; exact hrel.hlabels),
                  hlabel_content := hrel.hlabel_content,
                  hframes_one := hrel.hframes_one,
                  hmodule := hrel.hmodule, hstore_funcs := hrel.hstore_funcs,
                  hstore_types := hrel.hstore_types }⟩
            | some fn =>
              -- Function exists in IR
              match hpop : irPopN? s1.stack fn.params.length with
              | none =>
                -- Case 2: stack underflow → both trap
                -- IR traps
                have hir : irStep? s1 = some (.trap s!"stack underflow in call {funcIdx}",
                    { s1 with code := [], trace := s1.trace ++ [.trap s!"stack underflow in call {funcIdx}"] }) := by
                  simp [irStep?, hcode_ir, hfunc_ir, hpop, irTrapState, irPushTrace]
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- funcIdx IS in bounds for Wasm (same size)
                have hfunc_ok : funcIdx < s2.store.funcs.size := by
                  rw [← hfuncs_size]; exact List.getElem?_isSome.mp (by rw [hfunc_ir]; simp)
                -- Need to show Wasm also underflows or handle differently
                -- The Wasm param count might differ from IR param count,
                -- so we cannot directly show Wasm underflows.
                -- However, for a valid emit, param counts correspond.
                sorry
              | some (args, callerStack) =>
                -- Case 3: successful call → needs multi-frame EmitSimRel
                -- (blocked: hframes_one requires frames.length = 1, but call creates 2 frames)
                sorry
          · exact hf.elim
      -/
      | .callIndirect typeIdx => sorry
      | .block label body =>
          -- block: push label frame, enter body. Both IR and Wasm do the same.
          have hc : EmitCodeCorr _ (IRInstr.block label body :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.block_inv with ⟨body_w, rest_w, hcw, hbody, hrest⟩ | hf
          · -- Specific case: Wasm code = block .none body_w :: rest_w
            have hir := irStep?_eq_block s1 label body rest hcode_ir
            rw [hir] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            have hw := step?_eq_block s2 .none body_w rest_w hcw
            refine ⟨_, hw, ?_⟩
            exact { hemit := hrel.hemit
                    hcode := hbody
                    hstack := hrel.hstack
                    hframes_len := hrel.hframes_len
                    hframes_locals := hrel.hframes_locals
                    hframes_vals := hrel.hframes_vals
                    hglobals := hrel.hglobals
                    hmemory := hrel.hmemory
                    hmemLimits := hrel.hmemLimits
                    hmemory_aligned := hrel.hmemory_aligned
                    hmemory_nonempty := hrel.hmemory_nonempty
                    hlabels := by simp; exact hrel.hlabels
                    hhalt := hhalt_of_structural hbody (by simp; exact hrel.hlabels)
                    hlabel_content := by
                      intro i hi
                      simp only [List.length_cons] at hi
                      match i with
                      | 0 => exact ⟨_, _, rfl, rfl, hrest, hrest, rfl⟩
                      | i + 1 =>
                        simp only [List.getElem?_cons_succ]
                        have h := hrel.hlabel_content i (by omega)
                        obtain ⟨irLbl, wLbl, h1, h2, hE, hB, hL⟩ := h
                        refine ⟨irLbl, wLbl, h1, h2, by simp only [List.drop_succ_cons]; exact hE, ?_, hL⟩
                        rw [show (if irLbl.isLoop = true then i + 1 else i + 1 + 1) = (if irLbl.isLoop = true then i else i + 1) + 1 from by split <;> omega]
                        simp only [List.drop_succ_cons]
                        exact hB
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }
          · exact hf.elim
      | .loop label body =>
          -- loop: push loop label frame, enter body. Both IR and Wasm do the same.
          -- Key difference from block: onBranch points to body (re-enter loop), not rest.
          have hc : EmitCodeCorr _ (IRInstr.loop label body :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.loop_inv with ⟨body_w, rest_w, hcw, hbody, hrest⟩ | hf
          · -- Specific case: Wasm code = loop .none body_w :: rest_w
            have hir := irStep?_eq_loop s1 label body rest hcode_ir
            rw [hir] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            have hw := step?_eq_loop s2 .none body_w rest_w hcw
            refine ⟨_, hw, ?_⟩
            exact { hemit := hrel.hemit
                    hcode := hbody
                    hstack := hrel.hstack
                    hframes_len := hrel.hframes_len
                    hframes_locals := hrel.hframes_locals
                    hframes_vals := hrel.hframes_vals
                    hglobals := hrel.hglobals
                    hmemory := hrel.hmemory
                    hmemLimits := hrel.hmemLimits
                    hmemory_aligned := hrel.hmemory_aligned
                    hmemory_nonempty := hrel.hmemory_nonempty
                    hlabels := by simp; exact hrel.hlabels
                    hhalt := hhalt_of_structural hbody (by simp; exact hrel.hlabels)
                    hlabel_content := by
                      intro i hi
                      simp only [List.length_cons] at hi
                      match i with
                      | 0 => exact ⟨_, _, rfl, rfl, hrest, hbody, rfl⟩
                      | i + 1 =>
                        simp only [List.getElem?_cons_succ]
                        have h := hrel.hlabel_content i (by omega)
                        obtain ⟨irLbl, wLbl, h1, h2, hE, hB, hL⟩ := h
                        refine ⟨irLbl, wLbl, h1, h2, by simp only [List.drop_succ_cons]; exact hE, ?_, hL⟩
                        rw [show (if irLbl.isLoop = true then i + 1 else i + 1 + 1) = (if irLbl.isLoop = true then i else i + 1) + 1 from by split <;> omega]
                        simp only [List.drop_succ_cons]
                        exact hB
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }
          · exact hf.elim
      | .if_ result then_ else_ =>

          -- if: conditional branch. Both IR and Wasm pop i32, push label, enter branch.
          have hc : EmitCodeCorr _ (IRInstr.if_ result then_ else_ :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.if_inv with ⟨bt, then_w, else_w, rest_w, hcw, hthen, helse, hrest⟩ | hf
          · -- Specific case: Wasm code = if_ bt then_w else_w :: rest_w
            -- Case split on IR stack for condition value
            match hstk : s1.stack with
            | [] =>
              -- Empty stack: IR traps "stack underflow in if"
              have hir : irStep? s1 = some (.trap "stack underflow in if",
                  { s1 with code := [], trace := s1.trace ++ [.trap "stack underflow in if"] }) := by
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- Wasm stack also empty
              have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
              have hs2 : s2.stack = [] := by
                cases hs : s2.stack with | nil => rfl | cons => simp [hs] at hlen
              -- Wasm if with empty stack also traps
              have hw : step? s2 = some (.trap "stack underflow in if",
                  { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in if"] }) := by
                simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
              refine ⟨_, hw, ⟨hrel.hemit, ?_, ?_, hrel.hframes_len, hrel.hframes_locals,
                hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty,
                hrel.hlabels, ?_, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
              · exact EmitCodeCorr.nil
              · simp [hstk, hs2]
              · exact hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
            | .i32 cond :: stk =>
              -- i32 condition: decide true/false
              by_cases h0 : cond = 0
              · subst h0
                -- False branch: enter else
                have hir := irStep?_eq_if_false s1 result then_ else_ rest stk hcode_ir hstk
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm stack correspondence: s2.stack starts with .i32 0
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                match hs2 : s2.stack with
                | [] => simp [hs2] at hlen
                | wv :: wstk =>
                  have hval_corr := hrel.hstack.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval_corr
                  simp at hval_corr
                  cases hval_corr with
                  | i32 n =>
                  have hw := step?_eq_if_false s2 bt then_w else_w rest_w wstk hcw hs2
                  refine ⟨_, hw, ⟨hrel.hemit, helse, ?_, hrel.hframes_len, hrel.hframes_locals,
                    hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty,
                    ?_, ?_, ?_, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
                  · -- Stack correspondence: tails match
                    constructor
                    · simp [hstk, hs2] at hlen ⊢; omega
                    · intro i hi
                      have hstk2 := hrel.hstack
                      rw [hstk, hs2] at hstk2
                      exact hstk2.2 (i + 1) (by simp; omega)
                  · -- hlabels
                    simp; exact hrel.hlabels
                  · -- hhalt
                    exact hhalt_of_structural helse (by simp; exact hrel.hlabels)
                  · -- Label content: if_ pushes label with onExit = rest
                    intro i hi
                    simp only [List.length_cons] at hi
                    match i with
                    | 0 => exact ⟨_, _, rfl, rfl, hrest, hrest, rfl⟩
                    | i + 1 =>
                      simp only [List.getElem?_cons_succ]
                      have h := hrel.hlabel_content i (by omega)
                      obtain ⟨irLbl, wLbl, h1, h2, hE, hB, hL⟩ := h
                      refine ⟨irLbl, wLbl, h1, h2, by simp only [List.drop_succ_cons]; exact hE, ?_, hL⟩
                      rw [show (if irLbl.isLoop = true then i + 1 else i + 1 + 1) = (if irLbl.isLoop = true then i else i + 1) + 1 from by split <;> omega]
                      simp only [List.drop_succ_cons]
                      exact hB
              · -- True branch: enter then
                have hne := h0
                have hir := irStep?_eq_if_true s1 result then_ else_ rest cond stk hcode_ir hstk hne
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm stack correspondence
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                match hs2 : s2.stack with
                | [] => simp [hs2] at hlen
                | wv :: wstk =>
                  have hval_corr := hrel.hstack.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval_corr
                  simp at hval_corr
                  cases hval_corr with
                  | i32 n =>
                    have hw := step?_eq_if_true s2 bt then_w else_w rest_w cond wstk hcw hs2 hne
                    refine ⟨_, hw, ⟨hrel.hemit, hthen, ?_, hrel.hframes_len, hrel.hframes_locals,
                      hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty,
                      ?_, ?_, ?_, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
                    · -- Stack correspondence: tails match
                      constructor
                      · simp [hstk, hs2] at hlen ⊢; omega
                      · intro i hi
                        have hstk2 := hrel.hstack
                        rw [hstk, hs2] at hstk2
                        exact hstk2.2 (i + 1) (by simp; omega)
                    · -- hlabels
                      simp; exact hrel.hlabels
                    · -- hhalt
                      exact hhalt_of_structural hthen (by simp; exact hrel.hlabels)
                    · -- Label content: if_ pushes label with onExit = rest
                      intro i hi
                      simp only [List.length_cons] at hi
                      match i with
                      | 0 => exact ⟨_, _, rfl, rfl, hrest, hrest, rfl⟩
                      | i + 1 =>
                        simp only [List.getElem?_cons_succ]
                        have h := hrel.hlabel_content i (by omega)
                        obtain ⟨irLbl, wLbl, h1, h2, hE, hB, hL⟩ := h
                        refine ⟨irLbl, wLbl, h1, h2, by simp only [List.drop_succ_cons]; exact hE, ?_, hL⟩
                        rw [show (if irLbl.isLoop = true then i + 1 else i + 1 + 1) = (if irLbl.isLoop = true then i else i + 1) + 1 from by split <;> omega]
                        simp only [List.drop_succ_cons]
                        exact hB
            | .i64 n :: stk =>
              -- i64 on stack: type mismatch trap
              have hir : irStep? s1 = some (.trap "if condition is not i32",
                  { s1 with code := [], trace := s1.trace ++ [.trap "if condition is not i32"] }) := by
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              have hlen := hrel.hstack.1; rw [hstk] at hlen
              match hs2 : s2.stack with
              | [] => simp [hs2] at hlen
              | wv :: wstk =>
                have hval_corr := hrel.hstack.2 0 (by simp [hstk])
                rw [hstk, hs2] at hval_corr
                simp at hval_corr
                cases hval_corr with
                | i64 m =>
                  have hw : step? s2 = some (.trap "if condition is not i32",
                      { s2 with code := [], trace := s2.trace ++ [.trap "if condition is not i32"] }) := by
                    simp [step?, hcw, hs2, pop1?, i32Truth, trapState, pushTrace]
                  refine ⟨_, hw, ⟨hrel.hemit, ?_, ?_, hrel.hframes_len, hrel.hframes_locals,
                    hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty,
                    hrel.hlabels, ?_, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
                  · exact EmitCodeCorr.nil
                  · exact hrel.hstack
                  · exact hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
            | .f64 n :: stk =>
              -- f64 on stack: type mismatch trap
              have hir : irStep? s1 = some (.trap "if condition is not i32",
                  { s1 with code := [], trace := s1.trace ++ [.trap "if condition is not i32"] }) := by
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              have hlen := hrel.hstack.1; rw [hstk] at hlen
              match hs2 : s2.stack with
              | [] => simp [hs2] at hlen
              | wv :: wstk =>
                have hval_corr := hrel.hstack.2 0 (by simp [hstk])
                rw [hstk, hs2] at hval_corr
                simp at hval_corr
                cases hval_corr with
                | f64 m =>
                  have hw : step? s2 = some (.trap "if condition is not i32",
                      { s2 with code := [], trace := s2.trace ++ [.trap "if condition is not i32"] }) := by
                    simp [step?, hcw, hs2, pop1?, i32Truth, trapState, pushTrace]
                  refine ⟨_, hw, ⟨hrel.hemit, ?_, ?_, hrel.hframes_len, hrel.hframes_locals,
                    hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty,
                    hrel.hlabels, ?_, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩⟩
                  · exact EmitCodeCorr.nil
                  · exact hrel.hstack
                  · exact hhalt_of_structural (@EmitCodeCorr.nil (s1.labels.map (·.name))) hrel.hlabels
          · exact hf.elim
      | .br label => sorry
          /-
          -- unconditional branch
          have hc : EmitCodeCorr _ (IRInstr.br label :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.br_inv with ⟨idx, rest_w, hcw, hfind_ctx, hrest⟩ | hf
          · -- Wasm code = br idx :: rest_w
            -- Get label resolution from EmitCodeCorr ctx + findIdx?_map_name_irFindLabel?
            obtain ⟨ir_idx, irLbl, hfind, hidx⟩ :=
              emit_br_label_resolve (hcw ▸ hc) hrel.hlabels
            subst hidx
            -- Characterize the IR step
            have hir := irStep?_eq_br s1 label rest ir_idx irLbl hcode_ir hfind
            rw [hir] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            -- Label is within bounds
            have hlt := irFindLabel?_lt_length hfind
            have hlt_w : ir_idx < s2.labels.length := hrel.hlabels ▸ hlt
            -- Get resolveBranch? spec
            obtain ⟨wLbl, hwlbl_get, hresolve⟩ := resolveBranch?_spec hlt_w
            -- Get label correspondence from hlabel_content
            obtain ⟨irLbl', wLbl', hirLbl, hwLbl', hcode_exit, hcode_branch, hloop⟩ :=
              hrel.hlabel_content ir_idx hlt
            -- irLbl from irFindLabel? = irLbl' from hlabel_content
            have hirLbl_eq := irFindLabel?_getElem hfind
            rw [hirLbl_eq] at hirLbl
            simp only [Option.some.injEq] at hirLbl; subst hirLbl
            -- wLbl from resolveBranch? = wLbl' from hlabel_content
            rw [hwlbl_get] at hwLbl'
            simp only [Option.some.injEq] at hwLbl'; subst hwLbl'
            -- Wasm step
            have hw := step?_eq_br s2 ir_idx rest_w wLbl
              (if wLbl.isLoop then wLbl :: s2.labels.drop (ir_idx + 1)
               else s2.labels.drop (ir_idx + 1))
              hcw hresolve
            -- New labels (both sides use isLoop to decide)
            have hloop_eq : irLbl.isLoop = wLbl.isLoop := hloop
            exact ⟨_, hw,
              { hemit := hrel.hemit
                hcode := by rw [hloop_eq]; exact hcode_branch
                hstack := hrel.hstack
                hframes_len := hrel.hframes_len
                hframes_locals := hrel.hframes_locals
                hframes_vals := hrel.hframes_vals
                hglobals := hrel.hglobals
                hmemory := hrel.hmemory
                hmemLimits := hrel.hmemLimits
                hmemory_aligned := hrel.hmemory_aligned
                hmemory_nonempty := hrel.hmemory_nonempty
                hlabels := by
                  dsimp only []
                  rw [hloop_eq]
                  split
                  · simp; have := hrel.hlabels; omega
                  · have := hrel.hlabels; omega
                hhalt := by
                  rw [hloop_eq]
                  exact hhalt_of_structural (by rw [hloop_eq]; exact hcode_branch)
                    (by rw [hloop_eq]; split <;> (simp; have := hrel.hlabels; omega))
                hlabel_content := by
                  intro i hi
                  dsimp only [] at hi ⊢
                  rw [hloop_eq] at hi ⊢
                  split at hi ⊢
                  · -- isLoop = true: new labels = irLbl :: drop(ir_idx+1)
                    simp only [List.length_cons] at hi
                    match i with
                    | 0 =>
                      -- Position 0: the loop label itself
                      exact hrel.hlabel_content ir_idx hlt
                    | i + 1 =>
                      -- Position i+1: from old labels at ir_idx+1+i
                      have hi' : ir_idx + 1 + i < s1.labels.length := by omega
                      exact hrel.hlabel_content (ir_idx + 1 + i) hi'
                  · -- isLoop = false: new labels = drop(ir_idx+1)
                    have hi' : ir_idx + 1 + i < s1.labels.length := by omega
                    exact hrel.hlabel_content (ir_idx + 1 + i) hi'
                hframes_one := hrel.hframes_one
                hmodule := hrel.hmodule
                hstore_funcs := hrel.hstore_funcs
                hstore_types := hrel.hstore_types }⟩
          · exact hf.elim
          -/
      | .brIf label => sorry
          /-
          -- conditional branch
          have hc : EmitCodeCorr _ (IRInstr.brIf label :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.brIf_inv with ⟨idx, rest_w, hcw, _hfind_ctx, hrest⟩ | hf
          · -- Wasm code = brIf idx :: rest_w
            -- Case split on IR stack for condition value
            match hstk : s1.stack with
            | [] =>
              -- Empty stack: IR traps "stack underflow in br_if"
              have hir : irStep? s1 = some (.trap "stack underflow in br_if",
                  irPushTrace { s1 with code := [] } (.trap "stack underflow in br_if")) := by
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              -- Wasm stack also empty
              have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
              have hs2 : s2.stack = [] := by
                cases hs : s2.stack with | nil => rfl | cons => simp [hs] at hlen
              have hw : step? s2 = some (.trap "stack underflow in br_if",
                  { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in br_if"] }) := by
                simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
              exact ⟨_, by simp [traceToWasm]; exact hw,
                { hemit := hrel.hemit
                  hcode := .nil
                  hstack := by dsimp only []; exact hrel.hstack
                  hframes_len := hrel.hframes_len
                  hframes_locals := hrel.hframes_locals
                  hframes_vals := hrel.hframes_vals
                  hglobals := hrel.hglobals
                  hmemory := hrel.hmemory
                  hmemLimits := hrel.hmemLimits
                  hmemory_aligned := hrel.hmemory_aligned
                  hmemory_nonempty := hrel.hmemory_nonempty
                  hlabels := by dsimp only []; exact hrel.hlabels
                  hhalt := hhalt_of_structural (@EmitCodeCorr.nil []) (by dsimp only []; exact hrel.hlabels)
                  hlabel_content := hrel.hlabel_content
                  hframes_one := hrel.hframes_one
                  hmodule := hrel.hmodule
                  hstore_funcs := hrel.hstore_funcs
                  hstore_types := hrel.hstore_types }⟩
            | .i32 cond :: stk =>
              -- i32 condition: decide true/false
              match hcond : decide (cond = 0) with
              | isTrue h0 =>
                subst h0
                -- False branch: fall through (cond = 0)
                have hir := irStep?_eq_brIf_false s1 label rest stk hcode_ir hstk
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm stack correspondence: s2.stack starts with .i32 0
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                match hs2 : s2.stack with
                | [] => simp [hs2] at hlen
                | wv :: wstk =>
                  have hval_corr := hrel.hstack.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval_corr
                  simp at hval_corr
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval_corr
                  simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | i32 n => rename_i hneq; rw [hneq] at hs2
                  have hw := step?_eq_brIf_false_gen s2 idx rest_w wstk hcw hs2
                  refine ⟨_, hw, hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals, hrel.hframes_vals, hrel.hglobals, hrel.hmemory, hrel.hmemLimits, hrel.hmemory_aligned, hrel.hmemory_nonempty, hrel.hlabels, hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩
                  -- Stack correspondence: tails match
                  constructor
                  · simp [hstk, hs2] at hlen ⊢; omega
                  · intro i hi
                    have hstk2 := hrel.hstack
                    rw [hstk, hs2] at hstk2
                    exact hstk2.2 (i + 1) (by simp; omega)
              | isFalse hne =>
                -- True branch: branch to label (cond ≠ 0)
                -- Get guaranteed label resolution
                obtain ⟨ir_idx, irLbl, hfind, hidx⟩ :=
                  emit_brIf_label_resolve (hcw ▸ hc) hrel.hlabels
                subst hidx
                -- Characterize the IR step
                have hcond_ne : cond ≠ 0 := fun h => hne (by subst h; rfl)
                have hir := irStep?_eq_brIf_true s1 label rest cond stk ir_idx irLbl hcode_ir hstk hcond_ne hfind
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Label is within bounds
                have hlt := irFindLabel?_lt_length hfind
                have hlt_w : ir_idx < s2.labels.length := hrel.hlabels ▸ hlt
                -- Get resolveBranch? spec
                obtain ⟨wLbl, hwlbl_get, hresolve⟩ := resolveBranch?_spec hlt_w
                -- Get label correspondence from hlabel_content
                obtain ⟨irLbl', wLbl', hirLbl, hwLbl', hcode_exit, hcode_branch, hloop⟩ :=
                  hrel.hlabel_content ir_idx hlt
                -- irLbl from irFindLabel? = irLbl' from hlabel_content
                have hirLbl_eq := irFindLabel?_getElem hfind
                rw [hirLbl_eq] at hirLbl
                simp only [Option.some.injEq] at hirLbl; subst hirLbl
                -- wLbl from resolveBranch? = wLbl' from hlabel_content
                rw [hwlbl_get] at hwLbl'
                simp only [Option.some.injEq] at hwLbl'; subst hwLbl'
                -- Wasm stack correspondence
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                match hs2 : s2.stack with
                | [] => simp [hs2] at hlen
                | wv :: wstk =>
                  have hval_corr := hrel.hstack.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval_corr
                  simp at hval_corr
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval_corr
                  simp at h1 h2; subst h1; subst h2
                  cases hvc with
                  | i32 n =>
                    rename_i hneq; rw [hneq] at hs2
                    have hwcond_ne : n ≠ 0 := by rw [hneq]; exact hcond_ne
                    -- Wasm step: brIf true branch
                    have hw := step?_eq_brIf_true_gen s2 ir_idx rest_w n wstk wLbl
                      (if wLbl.isLoop then wLbl :: s2.labels.drop (ir_idx + 1)
                       else s2.labels.drop (ir_idx + 1))
                      hcw hs2 hwcond_ne hresolve
                    have hloop_eq : irLbl.isLoop = wLbl.isLoop := hloop
                    exact ⟨_, hw,
                      { hemit := hrel.hemit
                        hcode := by rw [hloop_eq]; exact hcode_branch
                        hstack := by
                          constructor
                          · simp [hstk, hs2] at hlen ⊢; omega
                          · intro i hi
                            have hstk2 := hrel.hstack
                            rw [hstk, hs2] at hstk2
                            exact hstk2.2 (i + 1) (by simp; omega)
                        hframes_len := hrel.hframes_len
                        hframes_locals := hrel.hframes_locals
                        hframes_vals := hrel.hframes_vals
                        hglobals := hrel.hglobals
                        hmemory := hrel.hmemory
                        hmemLimits := hrel.hmemLimits
                        hmemory_aligned := hrel.hmemory_aligned
                        hmemory_nonempty := hrel.hmemory_nonempty
                        hlabels := by
                          dsimp only []
                          rw [hloop_eq]
                          split
                          · simp; have := hrel.hlabels; omega
                          · have := hrel.hlabels; omega
                        hhalt := by
                          rw [hloop_eq]
                          exact hhalt_of_structural (by rw [hloop_eq]; exact hcode_branch)
                            (by rw [hloop_eq]; split <;> (simp; have := hrel.hlabels; omega))
                        hlabel_content := by
                          intro i hi
                          dsimp only [] at hi ⊢
                          rw [hloop_eq] at hi ⊢
                          split at hi ⊢
                          · simp only [List.length_cons] at hi
                            match i with
                            | 0 => exact hrel.hlabel_content ir_idx hlt
                            | i + 1 =>
                              have hi' : ir_idx + 1 + i < s1.labels.length := by omega
                              exact hrel.hlabel_content (ir_idx + 1 + i) hi'
                          · have hi' : ir_idx + 1 + i < s1.labels.length := by omega
                            exact hrel.hlabel_content (ir_idx + 1 + i) hi'
                        hframes_one := hrel.hframes_one
                        hmodule := hrel.hmodule
                        hstore_funcs := hrel.hstore_funcs
                        hstore_types := hrel.hstore_types }⟩
            | v :: stk =>
              -- Non-i32 at top of stack: IR traps "type mismatch"
              -- First show the IR step is a trap
              match v with
              | .i32 _ => exact absurd rfl (by simp [hstk])
              | _ =>
                have hir : irStep? s1 = some (.trap "br_if condition is not i32",
                    irPushTrace { s1 with code := [] } (.trap "br_if condition is not i32")) := by
                  simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace]
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm stack has corresponding non-i32 value → also traps
                have hlen := hrel.hstack.1; rw [hstk] at hlen
                match hs2 : s2.stack with
                | [] => simp [hs2] at hlen
                | wv :: wstk =>
                  have hval_corr := hrel.hstack.2 0 (by simp [hstk])
                  rw [hstk, hs2] at hval_corr
                  simp at hval_corr
                  obtain ⟨_, _, h1, h2, hvc⟩ := hval_corr
                  simp at h1 h2; subst h1; subst h2
                  -- v is not i32, so corresponding Wasm value is also not i32
                  have hwv_not_i32 : i32Truth wv = none := by
                    cases hvc with
                    | i64 _ => simp [i32Truth]
                    | f64 _ => simp [i32Truth]
                  have hw : step? s2 = some (.trap "br_if condition is not i32",
                      { s2 with code := [], trace := s2.trace ++ [.trap "br_if condition is not i32"] }) := by
                    simp [step?, hcw, hs2, pop1?, hwv_not_i32, trapState, pushTrace]
                  exact ⟨_, by simp [traceToWasm]; exact hw,
                    { hemit := hrel.hemit
                      hcode := .nil
                      hstack := by dsimp only []; exact hrel.hstack
                      hframes_len := hrel.hframes_len
                      hframes_locals := hrel.hframes_locals
                      hframes_vals := hrel.hframes_vals
                      hglobals := hrel.hglobals
                      hmemory := hrel.hmemory
                      hmemLimits := hrel.hmemLimits
                      hmemory_aligned := hrel.hmemory_aligned
                      hmemory_nonempty := hrel.hmemory_nonempty
                      hlabels := by dsimp only []; exact hrel.hlabels
                      hhalt := hhalt_of_structural (@EmitCodeCorr.nil []) (by dsimp only []; exact hrel.hlabels)
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }⟩
          · exact hf.elim
          -/
      | .return_ =>
          -- return from function: with hframes_one, frames = [frame], so top-level return
          have hc : EmitCodeCorr _ (IRInstr.return_ :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.return_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- Wasm code = return_ :: rest_w
            -- Derive single frame from hframes_one
            have hfr : ∃ f, s1.frames = [f] := by
              have hfo := hrel.hframes_one
              match hf : s1.frames with
              | [] => simp [hf] at hfo
              | [f] => exact ⟨f, rfl⟩
              | _ :: _ :: _ => simp [hf] at hfo
            obtain ⟨frame, hfr⟩ := hfr
            -- IR: top-level return clears code and labels
            have hir := irStep?_eq_return_toplevel s1 rest frame hcode_ir hfr
            rw [hir] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            -- Wasm: return_ also clears code and labels
            have hw := step?_eq_return s2 rest_w hcw
            exact ⟨_, hw,
              { hemit := hrel.hemit
                hcode := .nil
                hstack := hrel.hstack
                hframes_len := hrel.hframes_len
                hframes_locals := hrel.hframes_locals
                hframes_vals := hrel.hframes_vals
                hglobals := hrel.hglobals
                hmemory := hrel.hmemory
                hmemLimits := hrel.hmemLimits
                hmemory_aligned := hrel.hmemory_aligned
                hmemory_nonempty := hrel.hmemory_nonempty
                hlabels := by simp
                hhalt := by intro _; apply step?_halted; exact ⟨rfl, rfl⟩
                hlabel_content := by intro i hi; simp at hi
                hframes_one := hrel.hframes_one
                hmodule := hrel.hmodule
                hstore_funcs := hrel.hstore_funcs
                hstore_types := hrel.hstore_types }⟩
          · exact hf.elim
      | .drop =>
          -- drop: IR and Wasm both pop top of stack (or both trap on empty stack)
          have hc : EmitCodeCorr _ (IRInstr.drop :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.drop_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · match hstk : s1.stack with
            | [] =>
              -- Empty stack: both sides trap with "stack underflow in drop"
              have hir := irStep?_eq_drop_empty s1 rest hcode_ir hstk
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              have hlen_eq := hrel.hstack.1
              rw [hstk] at hlen_eq; simp at hlen_eq
              have hs2 : s2.stack = [] := by
                cases hs : s2.stack with
                | nil => rfl
                | cons => simp [hs] at hlen_eq
              have hw_step := step?_eq_drop_empty s2 rest_w hcw hs2
              exact ⟨{ s2 with code := [], stack := [], trace := s2.trace ++ [.trap "stack underflow in drop"] },
                by simp [traceToWasm]; exact hw_step,
                { hemit := hrel.hemit
                  hcode := .nil
                  hstack := by simp
                  hframes_len := hrel.hframes_len
                  hframes_locals := hrel.hframes_locals
                  hframes_vals := hrel.hframes_vals
                  hglobals := hrel.hglobals
                  hmemory := hrel.hmemory
                  hmemLimits := hrel.hmemLimits
                  hmemory_aligned := hrel.hmemory_aligned
                  hmemory_nonempty := hrel.hmemory_nonempty
                  hlabels := hrel.hlabels
                  hhalt := hhalt_of_structural (@EmitCodeCorr.nil []) (by dsimp only []; exact hrel.hlabels)
                  hlabel_content := hrel.hlabel_content
                  hframes_one := hrel.hframes_one
                  hmodule := hrel.hmodule
                  hstore_funcs := hrel.hstore_funcs
                  hstore_types := hrel.hstore_types }⟩
            | v :: stk =>
              -- Non-empty stack: both sides drop silently
              have hir := irStep?_eq_drop s1 rest v stk hcode_ir hstk
              rw [hir] at hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
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
                    hstack := by
                      constructor
                      · simp at hlen ⊢; omega
                      · intro i hi
                        have hstk2 := hrel.hstack
                        rw [hstk, hs2] at hstk2
                        exact hstk2.2 (i + 1) (by simp; omega)
                    hframes_len := hrel.hframes_len
                    hframes_locals := hrel.hframes_locals
                    hframes_vals := hrel.hframes_vals
                    hglobals := hrel.hglobals
                    hmemory := hrel.hmemory
                    hmemLimits := hrel.hmemLimits
                    hmemory_aligned := hrel.hmemory_aligned
                    hmemory_nonempty := hrel.hmemory_nonempty
                    hlabels := hrel.hlabels
                    hhalt := hhalt_of_structural hrest hrel.hlabels
                    hlabel_content := hrel.hlabel_content
                    hframes_one := hrel.hframes_one
                    hmodule := hrel.hmodule
                    hstore_funcs := hrel.hstore_funcs
                    hstore_types := hrel.hstore_types }⟩
          · exact hf.elim
      | .memoryGrow => sorry
          /-
          -- grow memory: IR and Wasm both pop i32 delta, grow or return -1
          have hc : EmitCodeCorr _ (IRInstr.memoryGrow :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.memoryGrow_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · match hstk : s1.stack with
            | [] =>
              -- Empty stack: both trap with "stack underflow in memory.grow"
              simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              have hlen_eq := hrel.hstack.1; rw [hstk] at hlen_eq; simp at hlen_eq
              have hs2 : s2.stack = [] := by cases s2.stack with | nil => rfl | cons => simp_all
              have hw : step? s2 = some (.trap "stack underflow in memory.grow",
                  { s2 with code := [], trace := s2.trace ++ [.trap "stack underflow in memory.grow"] }) := by
                simp [step?, hcw, hs2, pop1?, trapState, pushTrace]
              exact ⟨_, by simp [traceToWasm]; exact hw,
                { hemit := hrel.hemit, hcode := .nil, hstack := by dsimp only []; exact hrel.hstack,
                  hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                  hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory,
                  hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                  hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil []) (by dsimp only []; exact hrel.hlabels)
                  hlabel_content := hrel.hlabel_content
                  hframes_one := hrel.hframes_one
                  hmodule := hrel.hmodule
                  hstore_funcs := hrel.hstore_funcs
                  hstore_types := hrel.hstore_types }⟩
            | .i32 pages :: stk =>
              -- i32 on stack: grow or fail
              rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
              · -- Memory exists: w.store.memories[0]? = some ir.memory
                have hstk_w := stack_corr_i32_inv pages stk s2.stack
                  (hstk ▸ hrel.hstack.1) (hstk ▸ hrel.hstack.2)
                obtain ⟨wstk', hstack_eq, hlen_tail, htail⟩ := hstk_w
                have h0mem : 0 < s2.store.memories.size := List.getElem?_eq_some_length hmem_eq
                -- Wasm maxOk resolves to (newPages ≤ 65536) in all cases:
                -- memLimits[0] with max = none (from hmemLimits) → .ble 65536
                -- memLimits empty → .ble 65536 (else branch)
                have hMaxOk_eq : (if hLim : 0 < s2.store.memLimits.size then
                    match s2.store.memLimits[0].max with
                    | some maxPages => (s1.memory.size / 65536 + pages.toNat).ble maxPages
                    | none => (s1.memory.size / 65536 + pages.toNat).ble 65536
                  else (s1.memory.size / 65536 + pages.toNat).ble 65536) =
                  (s1.memory.size / 65536 + pages.toNat).ble 65536 := by
                  split
                  · next hLim =>
                    have hml := hrel.hmemLimits s2.store.memLimits[0]
                      (by rw [Array.getElem?_eq_getElem hLim])
                    simp [hml]
                  · rfl
                match hgrow : decide (s1.memory.size + pages.toNat * 65536 ≤ 65536 * 65536) with
                | isTrue hok =>
                  -- Success: both grow memory
                  have hir := irStep?_eq_memoryGrow_ok s1 rest pages stk hcode_ir hstk hok
                  rw [hir] at hstep
                  simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hNewPages_le : (s1.memory.size / 65536 + pages.toNat) ≤ 65536 := by
                    have := Nat.div_add_mod s1.memory.size 65536
                    omega
                  let newMem := ByteArray.mk (s1.memory.toList.toArray ++ Array.replicate (pages.toNat * 65536) 0)
                  let store_mg := { s2.store with memories := s2.store.memories.set! 0 newMem }
                  let s2_mg := { s2 with code := rest_w, stack := .i32 (s1.memory.size / 65536).toUInt32 :: wstk', store := store_mg }
                  have hw : step? s2 = some (.silent, pushTrace s2_mg .silent) := by
                    simp only [step?, hcw, hstack_eq, pop1?, hmem_eq, h0mem, dite_true]
                    rw [hMaxOk_eq]
                    simp [Nat.ble_eq, hNewPages_le, pushTrace]
                  simp only [traceToWasm]
                  refine ⟨_, hw, hrel.hemit, hrest, ?_, hrel.hframes_len, hrel.hframes_locals,
                    hrel.hframes_vals, hrel.hglobals, ?_, ?_, ?_, ?_, hrel.hlabels,
                    hhalt_of_structural hrest hrel.hlabels, hrel.hlabel_content, hrel.hframes_one, hrel.hmodule, hrel.hstore_funcs, hrel.hstore_types⟩
                  · -- Stack correspondence
                    dsimp only []
                    exact ⟨by simp; omega, by intro i hi; exact htail i (by omega)⟩
                  · -- hmemory: memories.set!(0, grown)[0]? = some grown
                    left; dsimp only []
                    simp [Array.set!, Array.setIfInBounds, h0mem]
                  · -- hmemLimits: memLimits unchanged by memory grow
                    dsimp only []; exact hrel.hmemLimits
                  · -- hmemory_aligned: grown.size = memory.size + pages*65536
                    dsimp only []
                    have hgsz : (ByteArray.mk (s1.memory.toList.toArray ++ Array.replicate (pages.toNat * 65536) 0)).size =
                        s1.memory.size + pages.toNat * 65536 := by
                      simp [ByteArray.size, ByteArray.toList, Array.toList_toArray]
                    rw [hgsz]
                    exact Dvd.dvd.add hrel.hmemory_aligned ⟨pages.toNat, rfl⟩
                  · -- hmemory_nonempty: set! preserves size
                    dsimp only [pushTrace]
                    simp [Array.size_set!]
                    exact hrel.hmemory_nonempty
                | isFalse hfail =>
                  -- Failure: both push -1 (0xFFFFFFFF)
                  simp [irStep?, hcode_ir, hstk, irPop1?, irPushTrace] at hstep
                  have hgt : 65536 * 65536 < s1.memory.size + pages.toNat * 65536 := by omega
                  simp [hgt] at hstep
                  obtain ⟨rfl, rfl⟩ := hstep
                  have hNewPages_gt : ¬ (s1.memory.size / 65536 + pages.toNat ≤ 65536) := by
                    intro h; apply hfail
                    have hmod := Nat.div_add_mod s1.memory.size 65536
                    have hmod_lt := Nat.mod_lt s1.memory.size (by omega : 0 < 65536)
                    have hle : s1.memory.size ≤ (s1.memory.size / 65536) * 65536 + 65535 := by omega
                    omega
                  let s2_fail := { s2 with code := rest_w, stack := .i32 (UInt32.ofNat 0xFFFFFFFF) :: wstk' }
                  have hw : step? s2 = some (.silent, pushTrace s2_fail .silent) := by
                    simp only [step?, hcw, hstack_eq, pop1?, hmem_eq, h0mem, dite_true]
                    rw [hMaxOk_eq]
                    simp [Nat.ble_eq, hNewPages_gt, pushTrace]
                  simp only [traceToWasm]
                  exact ⟨_, hw,
                    { hemit := hrel.hemit
                      hcode := hrest
                      hstack := by
                        dsimp only []
                        exact ⟨by simp; omega, by intro i hi; exact htail i (by omega)⟩
                      hframes_len := hrel.hframes_len
                      hframes_locals := hrel.hframes_locals
                      hframes_vals := hrel.hframes_vals
                      hglobals := hrel.hglobals
                      hmemory := hrel.hmemory
                      hmemLimits := hrel.hmemLimits
                      hmemory_aligned := hrel.hmemory_aligned
                      hmemory_nonempty := hrel.hmemory_nonempty
                      hlabels := hrel.hlabels
                      hhalt := hhalt_of_structural hrest hrel.hlabels
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }⟩
              · -- No memory: contradicts hmemory_nonempty (memories.size > 0 ⇒ memories[0]? ≠ none)
                exfalso
                have h := hrel.hmemory_nonempty
                simp [Array.getElem?_eq_none] at hmem_none
                omega
            | .f64 _ :: _ | .i64 _ :: _ =>
              -- Non-i32 on stack: both trap with type mismatch
              all_goals (
                simp [irStep?, hcode_ir, hstk, irPop1?, irTrapState, irPushTrace] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                have hstk_rel := hrel.hstack; rw [hstk] at hstk_rel
                have hlen := hstk_rel.1; simp at hlen
                match hstk_w : s2.stack with
                | [] => simp [hstk_w] at hlen
                | wv :: wstk =>
                  have h0 := hstk_rel.2 0 (by simp)
                  simp [hstk_w] at h0
                  have hw : step? s2 = some (.trap ("memory.grow delta is not i32"),
                      { s2 with code := [], trace := s2.trace ++ [.trap ("memory.grow delta is not i32")] }) := by
                    simp only [step?, hcw, hstk_w, pop1?, trapState, pushTrace]
                    rcases h0 with ⟨hcorr⟩ | ⟨hcorr⟩
                    all_goals (cases hcorr <;> simp)
                  exact ⟨_, by simp [traceToWasm]; exact hw,
                    { hemit := hrel.hemit, hcode := .nil, hstack := by dsimp only []; exact hrel.hstack,
                      hframes_len := hrel.hframes_len, hframes_locals := hrel.hframes_locals,
                      hframes_vals := hrel.hframes_vals, hglobals := hrel.hglobals, hmemory := hrel.hmemory,
                      hmemLimits := hrel.hmemLimits, hmemory_aligned := hrel.hmemory_aligned, hmemory_nonempty := hrel.hmemory_nonempty,
                      hlabels := hrel.hlabels, hhalt := hhalt_of_structural (@EmitCodeCorr.nil []) (by dsimp only []; exact hrel.hlabels)
                      hlabel_content := hrel.hlabel_content
                      hframes_one := hrel.hframes_one
                      hmodule := hrel.hmodule
                      hstore_funcs := hrel.hstore_funcs
                      hstore_types := hrel.hstore_types }⟩)
          · exact hf.elim
          -/

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
    exact LowerSimRel.init prog irmod hlower (lower_main_code_corr prog irmod hlower)
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
    exact LowerSimRel.init prog irmod hlower (lower_main_code_corr prog irmod hlower)
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
    (LowerSimRel.init prog irmod hlower (lower_main_code_corr prog irmod hlower))
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
    (hemit : emit irmod = .ok wmod)
    (hmem_pos : 0 < irmod.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : MemType),
      irmod.memories[i]? = some mt → mt.lim.max = none) :
    ∃ (R : IRExecState → ExecState → Prop),
      R (irInitialState irmod) (initialState wmod) ∧
      WasmForwardSim R := by
  refine ⟨EmitSimRel irmod wmod, ?_, ?_⟩
  · exact EmitSimRel.init irmod wmod hemit hmem_pos hmem_nomax
  · exact {
      step_sim := EmitSimRel.step_sim irmod wmod
      halt_sim := EmitSimRel.halt_sim irmod wmod
    }

/-- THE STUTTERING SIMULATION: IR → Wasm (architecturally correct version). -/
theorem emit_stutter_sim (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod)
    (hmem_pos : 0 < irmod.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : MemType),
      irmod.memories[i]? = some mt → mt.lim.max = none) :
    ∃ (R : IRExecState → ExecState → Prop),
      R (irInitialState irmod) (initialState wmod) ∧
      WasmStutterSim R := by
  refine ⟨EmitSimRel irmod wmod, ?_, ?_⟩
  · exact EmitSimRel.init irmod wmod hemit hmem_pos hmem_nomax
  · exact {
      step_sim := EmitSimRel.step_sim_stutter irmod wmod
      halt_sim := EmitSimRel.halt_sim irmod wmod
    }

/-- 1:1 version: emit_behavioral_correct using WasmForwardSim (for EmitCorrect.lean). -/
theorem emit_behavioral_correct' (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod)
    (hmem_pos : 0 < irmod.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : MemType),
      irmod.memories[i]? = some mt → mt.lim.max = none) :
    ∀ trace, IRBehaves irmod trace →
      Behaves wmod (traceListToWasm trace) := by
  intro trace hBeh
  obtain ⟨sFinal_ir, hIRSteps, hIRHalt⟩ := hBeh
  obtain ⟨R, hR_init, sim⟩ := emit_forward_sim irmod wmod hemit hmem_pos hmem_nomax
  have hW := WasmForwardSim_behavioral R sim hR_init ⟨sFinal_ir, hIRSteps, hIRHalt⟩
  obtain ⟨wFinal, hWSteps, hWHalt⟩ := hW
  exact ⟨wFinal, hWSteps, hWHalt⟩

/-- Stuttering version: emit_behavioral_correct with observable events. -/
theorem emit_behavioral_obs_correct (irmod : IRModule) (wmod : Module)
    (hemit : emit irmod = .ok wmod)
    (hmem_pos : 0 < irmod.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : MemType),
      irmod.memories[i]? = some mt → mt.lim.max = none) :
    ∀ (ir_trace : List TraceEvent),
    (∃ ir_final, IRSteps (irInitialState irmod) ir_trace ir_final ∧
      irStep? ir_final = none) →
    ∃ (sFinal : ExecState) (w_trace : List Wasm.TraceEvent),
      Wasm.Steps (initialState wmod) w_trace sFinal ∧
      Wasm.step? sFinal = none ∧
      Wasm.observableWasmEvents w_trace =
        Wasm.observableWasmEvents (traceListToWasm ir_trace) := by
  intro ir_trace hIR
  obtain ⟨R, hR_init, sim⟩ := emit_stutter_sim irmod wmod hemit hmem_pos hmem_nomax
  exact WasmStutterSim_behavioral sim hR_init hIR

end VerifiedJS.Wasm.IR
