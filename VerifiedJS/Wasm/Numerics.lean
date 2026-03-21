/-
  VerifiedJS — Wasm Numeric Operations
  Complete i32/i64/f32/f64 operations per WebAssembly 1.0 spec §4.3.
  SPEC: WebAssembly 1.0 §4.3 (Numerics), WasmCert-Coq `theories/operations.v`.
-/

namespace VerifiedJS.Wasm.Numerics

/-- IEEE 754 NaN value. -/
private def nan : Float := 0.0 / 0.0

/-- IEEE 754 positive infinity. -/
private def inf : Float := 1.0 / 0.0

/-! ## Signed integer helpers
    SPEC §4.3.1: Wasm integers are unsigned; signed interpretation is defined
    by two's complement reinterpretation. -/

/-- Interpret a UInt32 as a signed Int via two's complement (§4.3.1). -/
def i32ToSigned (n : UInt32) : Int :=
  let v := n.toNat
  if v < 2^31 then Int.ofNat v else Int.ofNat v - Int.ofNat (2^32)

/-- Interpret a UInt64 as a signed Int via two's complement (§4.3.1). -/
def i64ToSigned (n : UInt64) : Int :=
  let v := n.toNat
  if v < 2^63 then Int.ofNat v else Int.ofNat v - Int.ofNat (2^64)

/-! ## i32 arithmetic (§4.3.2) -/

@[simp] def i32Add (a b : UInt32) : UInt32 := a + b
@[simp] def i32Sub (a b : UInt32) : UInt32 := a - b
@[simp] def i32Mul (a b : UInt32) : UInt32 := a * b

/-- SPEC §4.3.2 i32.div_s: signed division, traps on zero or overflow. -/
def i32DivS? (a b : UInt32) : Option UInt32 :=
  if b == 0 then none
  else
    let sa := i32ToSigned a
    let sb := i32ToSigned b
    let q := sa / sb
    if q < -(Int.ofNat (2^31)) || q >= Int.ofNat (2^31) then none
    else some (UInt32.ofInt q)

/-- SPEC §4.3.2 i32.div_u: unsigned division, traps on zero. -/
def i32DivU? (a b : UInt32) : Option UInt32 :=
  if b == 0 then none else some (a / b)

/-- SPEC §4.3.2 i32.rem_s: signed remainder, traps on zero. -/
def i32RemS? (a b : UInt32) : Option UInt32 :=
  if b == 0 then none
  else some (UInt32.ofInt (Int.emod (i32ToSigned a) (i32ToSigned b)))

/-- SPEC §4.3.2 i32.rem_u: unsigned remainder, traps on zero. -/
def i32RemU? (a b : UInt32) : Option UInt32 :=
  if b == 0 then none else some (a % b)

@[simp] def i32And (a b : UInt32) : UInt32 := a &&& b
@[simp] def i32Or  (a b : UInt32) : UInt32 := a ||| b
@[simp] def i32Xor (a b : UInt32) : UInt32 := a ^^^ b

/-- SPEC §4.3.2 i32.shl: shift left, shift count modulo 32. -/
def i32Shl (a b : UInt32) : UInt32 :=
  UInt32.shiftLeft a (UInt32.ofNat (b.toNat % 32))

/-- SPEC §4.3.2 i32.shr_s: arithmetic shift right, shift count modulo 32. -/
def i32ShrS (a b : UInt32) : UInt32 :=
  let shift := b.toNat % 32
  Int32.toUInt32 (Int32.ofInt (i32ToSigned a / Int.ofNat (Nat.pow 2 shift)))

/-- SPEC §4.3.2 i32.shr_u: logical shift right, shift count modulo 32. -/
def i32ShrU (a b : UInt32) : UInt32 :=
  UInt32.shiftRight a (UInt32.ofNat (b.toNat % 32))

/-- SPEC §4.3.2 i32.rotl: rotate left. -/
def i32Rotl (a b : UInt32) : UInt32 :=
  let k := b.toNat % 32
  let lo := UInt32.shiftLeft a (UInt32.ofNat k)
  let hi := UInt32.shiftRight a (UInt32.ofNat (32 - k))
  lo ||| hi

/-- SPEC §4.3.2 i32.rotr: rotate right. -/
def i32Rotr (a b : UInt32) : UInt32 :=
  let k := b.toNat % 32
  let lo := UInt32.shiftRight a (UInt32.ofNat k)
  let hi := UInt32.shiftLeft a (UInt32.ofNat (32 - k))
  lo ||| hi

/-! ## i32 unary (§4.3.2) -/

/-- SPEC §4.3.2 i32.clz: count leading zeros. -/
def i32Clz (n : UInt32) : UInt32 :=
  let v := n.toNat
  if v == 0 then 32
  else
    -- Simple iterative approach via fold
    let result := List.range 32 |>.find? (fun i => v &&& (2^(31 - i)) != 0)
    UInt32.ofNat (result.getD 32)

/-- SPEC §4.3.2 i32.ctz: count trailing zeros. -/
def i32Ctz (n : UInt32) : UInt32 :=
  let v := n.toNat
  if v == 0 then 32
  else
    let result := List.range 32 |>.find? (fun i => v &&& (2^i) != 0)
    UInt32.ofNat (result.getD 32)

/-- SPEC §4.3.2 i32.popcnt: population count (number of 1-bits). -/
def i32Popcnt (n : UInt32) : UInt32 :=
  let v := n.toNat
  let count := List.range 32 |>.foldl (fun acc i => if v &&& (2^i) != 0 then acc + 1 else acc) 0
  UInt32.ofNat count

/-- SPEC §4.3.2 i32.eqz: test for zero. -/
@[simp] def i32Eqz (n : UInt32) : Bool := n == 0

/-! ## i32 comparison (§4.3.3) -/

@[simp] def i32Eq  (a b : UInt32) : Bool := a == b
@[simp] def i32Ne  (a b : UInt32) : Bool := a != b
@[simp] def i32Ltu (a b : UInt32) : Bool := a < b
@[simp] def i32Gtu (a b : UInt32) : Bool := a > b
@[simp] def i32Leu (a b : UInt32) : Bool := a <= b
@[simp] def i32Geu (a b : UInt32) : Bool := a >= b
@[simp] def i32Lts (a b : UInt32) : Bool := i32ToSigned a < i32ToSigned b
@[simp] def i32Gts (a b : UInt32) : Bool := i32ToSigned a > i32ToSigned b
@[simp] def i32Les (a b : UInt32) : Bool := i32ToSigned a <= i32ToSigned b
@[simp] def i32Ges (a b : UInt32) : Bool := i32ToSigned a >= i32ToSigned b

/-! ## i64 arithmetic (§4.3.2) -/

@[simp] def i64Add (a b : UInt64) : UInt64 := a + b
@[simp] def i64Sub (a b : UInt64) : UInt64 := a - b
@[simp] def i64Mul (a b : UInt64) : UInt64 := a * b

/-- SPEC §4.3.2 i64.div_s: signed division, traps on zero or overflow. -/
def i64DivS? (a b : UInt64) : Option UInt64 :=
  if b == 0 then none
  else
    let sa := i64ToSigned a
    let sb := i64ToSigned b
    let q := sa / sb
    if q < -(Int.ofNat (2^63)) || q >= Int.ofNat (2^63) then none
    else some (UInt64.ofInt q)

/-- SPEC §4.3.2 i64.div_u: unsigned division, traps on zero. -/
def i64DivU? (a b : UInt64) : Option UInt64 :=
  if b == 0 then none else some (a / b)

/-- SPEC §4.3.2 i64.rem_s: signed remainder, traps on zero. -/
def i64RemS? (a b : UInt64) : Option UInt64 :=
  if b == 0 then none
  else some (UInt64.ofInt (Int.emod (i64ToSigned a) (i64ToSigned b)))

/-- SPEC §4.3.2 i64.rem_u: unsigned remainder, traps on zero. -/
def i64RemU? (a b : UInt64) : Option UInt64 :=
  if b == 0 then none else some (a % b)

@[simp] def i64And (a b : UInt64) : UInt64 := a &&& b
@[simp] def i64Or  (a b : UInt64) : UInt64 := a ||| b
@[simp] def i64Xor (a b : UInt64) : UInt64 := a ^^^ b

/-- SPEC §4.3.2 i64.shl: shift left, shift count modulo 64. -/
def i64Shl (a b : UInt64) : UInt64 :=
  UInt64.shiftLeft a (UInt64.ofNat (b.toNat % 64))

/-- SPEC §4.3.2 i64.shr_s: arithmetic shift right, shift count modulo 64. -/
def i64ShrS (a b : UInt64) : UInt64 :=
  let shift := b.toNat % 64
  Int64.toUInt64 (Int64.ofInt (i64ToSigned a / Int.ofNat (Nat.pow 2 shift)))

/-- SPEC §4.3.2 i64.shr_u: logical shift right, shift count modulo 64. -/
def i64ShrU (a b : UInt64) : UInt64 :=
  UInt64.shiftRight a (UInt64.ofNat (b.toNat % 64))

/-- SPEC §4.3.2 i64.rotl: rotate left. -/
def i64Rotl (a b : UInt64) : UInt64 :=
  let k := b.toNat % 64
  let lo := UInt64.shiftLeft a (UInt64.ofNat k)
  let hi := UInt64.shiftRight a (UInt64.ofNat (64 - k))
  lo ||| hi

/-- SPEC §4.3.2 i64.rotr: rotate right. -/
def i64Rotr (a b : UInt64) : UInt64 :=
  let k := b.toNat % 64
  let lo := UInt64.shiftRight a (UInt64.ofNat k)
  let hi := UInt64.shiftLeft a (UInt64.ofNat (64 - k))
  lo ||| hi

/-! ## i64 unary (§4.3.2) -/

/-- SPEC §4.3.2 i64.clz: count leading zeros. -/
def i64Clz (n : UInt64) : UInt64 :=
  let v := n.toNat
  if v == 0 then 64
  else
    let result := List.range 64 |>.find? (fun i => v &&& (2^(63 - i)) != 0)
    UInt64.ofNat (result.getD 64)

/-- SPEC §4.3.2 i64.ctz: count trailing zeros. -/
def i64Ctz (n : UInt64) : UInt64 :=
  let v := n.toNat
  if v == 0 then 64
  else
    let result := List.range 64 |>.find? (fun i => v &&& (2^i) != 0)
    UInt64.ofNat (result.getD 64)

/-- SPEC §4.3.2 i64.popcnt: population count (number of 1-bits). -/
def i64Popcnt (n : UInt64) : UInt64 :=
  let v := n.toNat
  let count := List.range 64 |>.foldl (fun acc i => if v &&& (2^i) != 0 then acc + 1 else acc) 0
  UInt64.ofNat count

/-- SPEC §4.3.2 i64.eqz: test for zero. -/
@[simp] def i64Eqz (n : UInt64) : Bool := n == 0

/-! ## i64 comparison (§4.3.3) -/

@[simp] def i64Eq  (a b : UInt64) : Bool := a == b
@[simp] def i64Ne  (a b : UInt64) : Bool := a != b
@[simp] def i64Ltu (a b : UInt64) : Bool := a < b
@[simp] def i64Gtu (a b : UInt64) : Bool := a > b
@[simp] def i64Leu (a b : UInt64) : Bool := a <= b
@[simp] def i64Geu (a b : UInt64) : Bool := a >= b
@[simp] def i64Lts (a b : UInt64) : Bool := i64ToSigned a < i64ToSigned b
@[simp] def i64Gts (a b : UInt64) : Bool := i64ToSigned a > i64ToSigned b
@[simp] def i64Les (a b : UInt64) : Bool := i64ToSigned a <= i64ToSigned b
@[simp] def i64Ges (a b : UInt64) : Bool := i64ToSigned a >= i64ToSigned b

/-! ## f32 arithmetic (§4.3.3)
    Note: Lean `Float` is IEEE 754 f64. We use Float for both f32 and f64
    at the specification level; precision semantics can be refined later. -/

def f32Add (a b : Float) : Float := a + b
def f32Sub (a b : Float) : Float := a - b
def f32Mul (a b : Float) : Float := a * b
def f32Div (a b : Float) : Float := a / b

/-- SPEC §4.3.3 f32.min: NaN-propagating minimum. -/
def f32Min (a b : Float) : Float :=
  if a != a || b != b then nan  -- NaN propagation
  else if a <= b then a else b

/-- SPEC §4.3.3 f32.max: NaN-propagating maximum. -/
def f32Max (a b : Float) : Float :=
  if a != a || b != b then nan
  else if a >= b then a else b

/-- SPEC §4.3.3 f32.copysign: magnitude of a with sign of b. -/
def f32Copysign (a b : Float) : Float :=
  if b < 0 then -(a.abs) else a.abs

/-! ## f32 unary (§4.3.3) -/

def f32Abs     (n : Float) : Float := n.abs
def f32Neg     (n : Float) : Float := -n
def f32Ceil    (n : Float) : Float := n.ceil
def f32Floor   (n : Float) : Float := n.floor
def f32Sqrt    (n : Float) : Float := n.sqrt
def f32Nearest (n : Float) : Float := n.round

/-- SPEC §4.3.3 f32.trunc: round towards zero. -/
def f32Trunc (n : Float) : Float :=
  if n < 0 then n.ceil else n.floor

/-! ## f32 comparison (§4.3.4) -/

def f32Eq (a b : Float) : Bool := a == b
def f32Ne (a b : Float) : Bool := a != b
def f32Lt (a b : Float) : Bool := a < b
def f32Gt (a b : Float) : Bool := a > b
def f32Le (a b : Float) : Bool := a <= b
def f32Ge (a b : Float) : Bool := a >= b

/-! ## f64 arithmetic (§4.3.3) -/

@[simp] def f64Add (a b : Float) : Float := a + b
@[simp] def f64Sub (a b : Float) : Float := a - b
@[simp] def f64Mul (a b : Float) : Float := a * b
@[simp] def f64Div (a b : Float) : Float := a / b

/-- SPEC §4.3.3 f64.min: NaN-propagating minimum. -/
def f64Min (a b : Float) : Float :=
  if a != a || b != b then nan
  else if a <= b then a else b

/-- SPEC §4.3.3 f64.max: NaN-propagating maximum. -/
def f64Max (a b : Float) : Float :=
  if a != a || b != b then nan
  else if a >= b then a else b

/-- SPEC §4.3.3 f64.copysign: magnitude of a with sign of b. -/
def f64Copysign (a b : Float) : Float :=
  if b < 0 then -(a.abs) else a.abs

/-! ## f64 unary (§4.3.3) -/

@[simp] def f64Abs     (n : Float) : Float := n.abs
@[simp] def f64Neg     (n : Float) : Float := -n
@[simp] def f64Ceil    (n : Float) : Float := n.ceil
@[simp] def f64Floor   (n : Float) : Float := n.floor
@[simp] def f64Sqrt    (n : Float) : Float := n.sqrt
@[simp] def f64Nearest (n : Float) : Float := n.round

/-- SPEC §4.3.3 f64.trunc: round towards zero. -/
def f64Trunc (n : Float) : Float :=
  if n < 0 then n.ceil else n.floor

/-! ## f64 comparison (§4.3.4) -/

@[simp] def f64Eq (a b : Float) : Bool := a == b
@[simp] def f64Ne (a b : Float) : Bool := a != b
@[simp] def f64Lt (a b : Float) : Bool := a < b
@[simp] def f64Gt (a b : Float) : Bool := a > b
@[simp] def f64Le (a b : Float) : Bool := a <= b
@[simp] def f64Ge (a b : Float) : Bool := a >= b

/-! ## Conversion operations (§4.3.4)
    SPEC: WebAssembly 1.0 §4.3.4 (Conversions). -/

/-- Helper: truncate a Float towards zero, returning none for NaN/infinity. -/
def truncFloatToInt? (n : Float) : Option Int :=
  if n != n then none  -- NaN
  else if n == inf || n == -inf then none
  else
    let truncated := if n < 0 then n.ceil else n.floor
    some (Int.ofFloat truncated)
where
  /-- Convert Float to Int (implementation helper). -/
  Int.ofFloat (f : Float) : Int :=
    if f < 0 then -(Int.ofNat ((-f).toUInt64.toNat))
    else Int.ofNat f.toUInt64.toNat

/-- SPEC §4.3.4 i32.wrap_i64: wrap i64 to i32 (mod 2^32). -/
@[simp] def i32WrapI64 (n : UInt64) : UInt32 := UInt32.ofNat n.toNat

/-- SPEC §4.3.4 i64.extend_i32_s: sign-extending extend. -/
@[simp] def i64ExtendI32s (n : UInt32) : UInt64 := UInt64.ofInt (i32ToSigned n)

/-- SPEC §4.3.4 i64.extend_i32_u: zero-extending extend. -/
@[simp] def i64ExtendI32u (n : UInt32) : UInt64 := UInt64.ofNat n.toNat

/-- SPEC §4.3.4 i32.trunc_f*_s: truncate float to signed i32, traps on overflow/NaN. -/
def i32TruncFS? (n : Float) : Option UInt32 :=
  match truncFloatToInt? n with
  | some i =>
    if i >= -(Int.ofNat (2^31)) && i < Int.ofNat (2^31) then some (UInt32.ofInt i)
    else none
  | none => none

/-- SPEC §4.3.4 i32.trunc_f*_u: truncate float to unsigned i32, traps on overflow/NaN. -/
def i32TruncFU? (n : Float) : Option UInt32 :=
  match truncFloatToInt? n with
  | some i =>
    if i >= 0 && i < Int.ofNat (2^32) then some (UInt32.ofInt i)
    else none
  | none => none

/-- SPEC §4.3.4 i64.trunc_f*_s: truncate float to signed i64, traps on overflow/NaN. -/
def i64TruncFS? (n : Float) : Option UInt64 :=
  match truncFloatToInt? n with
  | some i =>
    if i >= -(Int.ofNat (2^63)) && i < Int.ofNat (2^63) then some (UInt64.ofInt i)
    else none
  | none => none

/-- SPEC §4.3.4 i64.trunc_f*_u: truncate float to unsigned i64, traps on overflow/NaN. -/
def i64TruncFU? (n : Float) : Option UInt64 :=
  match truncFloatToInt? n with
  | some i =>
    if i >= 0 then some (UInt64.ofInt i)
    else none
  | none => none

/-- SPEC §4.3.4 f32.convert_i32_s: convert signed i32 to f32. -/
def f32ConvertI32s (n : UInt32) : Float := Float.ofInt (i32ToSigned n)
/-- SPEC §4.3.4 f32.convert_i32_u: convert unsigned i32 to f32. -/
def f32ConvertI32u (n : UInt32) : Float := Float.ofNat n.toNat
/-- SPEC §4.3.4 f32.convert_i64_s: convert signed i64 to f32. -/
def f32ConvertI64s (n : UInt64) : Float := Float.ofInt (i64ToSigned n)
/-- SPEC §4.3.4 f32.convert_i64_u: convert unsigned i64 to f32. -/
def f32ConvertI64u (n : UInt64) : Float := Float.ofNat n.toNat

/-- SPEC §4.3.4 f64.convert_i32_s: convert signed i32 to f64. -/
@[simp] def f64ConvertI32s (n : UInt32) : Float := Float.ofInt (i32ToSigned n)
/-- SPEC §4.3.4 f64.convert_i32_u: convert unsigned i32 to f64. -/
@[simp] def f64ConvertI32u (n : UInt32) : Float := Float.ofNat n.toNat
/-- SPEC §4.3.4 f64.convert_i64_s: convert signed i64 to f64. -/
def f64ConvertI64s (n : UInt64) : Float := Float.ofInt (i64ToSigned n)
/-- SPEC §4.3.4 f64.convert_i64_u: convert unsigned i64 to f64. -/
def f64ConvertI64u (n : UInt64) : Float := Float.ofNat n.toNat

/-- SPEC §4.3.4 f32.demote_f64: demote f64 to f32 (precision loss). -/
def f32DemoteF64 (n : Float) : Float := n  -- both represented as Float in Lean

/-- SPEC §4.3.4 f64.promote_f32: promote f32 to f64 (lossless). -/
def f64PromoteF32 (n : Float) : Float := n

/-- SPEC §4.3.4 i32.reinterpret_f32: bit reinterpretation. -/
def i32ReinterpretF32 (n : Float) : UInt32 := UInt32.ofNat n.toUInt64.toNat

/-- SPEC §4.3.4 f32.reinterpret_i32: bit reinterpretation. -/
def f32ReinterpretI32 (n : UInt32) : Float := Float.ofNat n.toNat

/-- SPEC §4.3.4 i64.reinterpret_f64: bit reinterpretation. -/
def i64ReinterpretF64 (n : Float) : UInt64 := n.toUInt64

/-- SPEC §4.3.4 f64.reinterpret_i64: bit reinterpretation. -/
def f64ReinterpretI64 (n : UInt64) : Float := Float.ofNat n.toNat

/-! ## Sign extension operations (§4.3.2, sign-extension proposal)
    SPEC: WebAssembly sign-extension operators proposal. -/

/-- i32.extend8_s: sign-extend from 8 bits. -/
def i32Extend8s (n : UInt32) : UInt32 :=
  let v := n.toNat % 256
  if v < 128 then UInt32.ofNat v
  else UInt32.ofInt (Int.ofNat v - Int.ofNat 256)

/-- i32.extend16_s: sign-extend from 16 bits. -/
def i32Extend16s (n : UInt32) : UInt32 :=
  let v := n.toNat % 65536
  if v < 32768 then UInt32.ofNat v
  else UInt32.ofInt (Int.ofNat v - Int.ofNat 65536)

/-- i64.extend8_s: sign-extend from 8 bits. -/
def i64Extend8s (n : UInt64) : UInt64 :=
  let v := n.toNat % 256
  if v < 128 then UInt64.ofNat v
  else UInt64.ofInt (Int.ofNat v - Int.ofNat 256)

/-- i64.extend16_s: sign-extend from 16 bits. -/
def i64Extend16s (n : UInt64) : UInt64 :=
  let v := n.toNat % 65536
  if v < 32768 then UInt64.ofNat v
  else UInt64.ofInt (Int.ofNat v - Int.ofNat 65536)

/-- i64.extend32_s: sign-extend from 32 bits. -/
def i64Extend32s (n : UInt64) : UInt64 :=
  let v := n.toNat % (2^32)
  if v < 2^31 then UInt64.ofNat v
  else UInt64.ofInt (Int.ofNat v - Int.ofNat (2^32))

/-! ## Algebraic properties for proof automation -/

/-- i32.add is commutative. -/
theorem i32Add_comm (a b : UInt32) : i32Add a b = i32Add b a := by
  simp [i32Add, UInt32.add_comm]

/-- i32.add identity: adding 0. -/
@[simp] theorem i32Add_zero (a : UInt32) : i32Add a 0 = a := by
  simp [i32Add]

/-- i32.mul is commutative. -/
theorem i32Mul_comm (a b : UInt32) : i32Mul a b = i32Mul b a := by
  simp [i32Mul, UInt32.mul_comm]

/-- i32.mul identity: multiplying by 1. -/
@[simp] theorem i32Mul_one (a : UInt32) : i32Mul a 1 = a := by
  simp [i32Mul]

/-- i32.eqz on 0 is true. -/
@[simp] theorem i32Eqz_zero : i32Eqz 0 = true := by native_decide

/-- i32.eqz on 1 is false. -/
@[simp] theorem i32Eqz_one : i32Eqz 1 = false := by native_decide

/-- i64.add is commutative. -/
theorem i64Add_comm (a b : UInt64) : i64Add a b = i64Add b a := by
  simp [i64Add, UInt64.add_comm]

/-- i64.add identity: adding 0. -/
@[simp] theorem i64Add_zero (a : UInt64) : i64Add a 0 = a := by
  simp [i64Add]

/-- i64.mul is commutative. -/
theorem i64Mul_comm (a b : UInt64) : i64Mul a b = i64Mul b a := by
  simp [i64Mul, UInt64.mul_comm]

/-- i32.eq is reflexive. -/
@[simp] theorem i32Eq_refl (a : UInt32) : i32Eq a a = true := by
  simp [i32Eq]

/-- i64.eq is reflexive. -/
@[simp] theorem i64Eq_refl (a : UInt64) : i64Eq a a = true := by
  simp [i64Eq]

/-- i32.ne is irreflexive. -/
@[simp] theorem i32Ne_refl (a : UInt32) : i32Ne a a = false := by
  simp [i32Ne]

/-- i64.ne is irreflexive. -/
@[simp] theorem i64Ne_refl (a : UInt64) : i64Ne a a = false := by
  simp [i64Ne]

/-! ## Concrete evaluation sanity checks -/

example : i32Add 3 5 = 8 := by native_decide
example : i32Sub 10 3 = 7 := by native_decide
example : i32Mul 4 5 = 20 := by native_decide
example : i64Add 100 200 = 300 := by native_decide
example : i32Eq 42 42 = true := by native_decide
example : i32Eq 1 2 = false := by native_decide
example : i32Ltu 1 2 = true := by native_decide
example : i32Ltu 2 1 = false := by native_decide
example : i32WrapI64 (UInt64.ofNat (2^32 + 5)) = 5 := by native_decide
example : i64ExtendI32u 42 = 42 := by native_decide

end VerifiedJS.Wasm.Numerics
