/-
  VerifiedJS — Runtime Value Representation
  NaN-boxing in f64, or tagged pointers in i64.
-/

namespace VerifiedJS.Runtime

/-- NaN-boxed value representation.
    Uses the NaN payload bits of IEEE 754 f64 to tag different value types.
    - f64 values: any non-NaN f64 (or the canonical NaN)
    - Tagged values: NaN with specific bit patterns in the payload -/
structure NanBoxed where
  bits : UInt64
  deriving Repr, BEq

namespace NanBoxed

-- Tag constants for NaN-boxing
-- Quiet NaN mask: bit 51 set, exponent all 1s
def nanMask : UInt64 := 0x7FF8000000000000
-- Tag bits occupy bits 48-50
def tagMask : UInt64 := 0x0007000000000000
def payloadMask : UInt64 := 0x0000FFFFFFFFFFFF

def tagNull : UInt64 := 0x0001000000000000
def tagUndefined : UInt64 := 0x0002000000000000
def tagBool : UInt64 := 0x0003000000000000
def tagInt32 : UInt64 := 0x0004000000000000
def tagString : UInt64 := 0x0005000000000000
def tagObject : UInt64 := 0x0006000000000000
def tagSymbol : UInt64 := 0x0007000000000000

/-- Canonical numeric NaN used for JS `Number` NaN values (`ECMA-262 §6.1.6.1`). -/
def canonicalNaNBits : UInt64 := nanMask

/-- Runtime tags for non-number JS values (ECMA-262 §6.1). -/
inductive Tag where
  | null
  | undefined
  | bool
  | int32
  | string
  | object
  | symbol
  deriving Repr, BEq, DecidableEq

def tagToBits : Tag → UInt64
  | .null => tagNull
  | .undefined => tagUndefined
  | .bool => tagBool
  | .int32 => tagInt32
  | .string => tagString
  | .object => tagObject
  | .symbol => tagSymbol

def bitsToTag? : UInt64 → Option Tag
  | b =>
      if b == tagNull then
        some .null
      else if b == tagUndefined then
        some .undefined
      else if b == tagBool then
        some .bool
      else if b == tagInt32 then
        some .int32
      else if b == tagString then
        some .string
      else if b == tagObject then
        some .object
      else if b == tagSymbol then
        some .symbol
      else
        none

/-- Builds a boxed non-number value with a 48-bit payload. -/
def mkTagged (tag : Tag) (payload : UInt64) : NanBoxed :=
  { bits := nanMask ||| tagToBits tag ||| (payload &&& payloadMask) }

/-- A value is boxed if it is a quiet NaN payload with one of our runtime tags. -/
def isBoxed (v : NanBoxed) : Bool :=
  (v.bits &&& nanMask) == nanMask &&
    match bitsToTag? (v.bits &&& tagMask) with
    | some _ => true
    | none => false

def getTag? (v : NanBoxed) : Option Tag :=
  if (v.bits &&& nanMask) == nanMask then
    bitsToTag? (v.bits &&& tagMask)
  else
    none

def getPayload (v : NanBoxed) : UInt64 :=
  v.bits &&& payloadMask

/-- Numbers are carried as IEEE-754 bit patterns. All NaNs are canonicalized. -/
def encodeNumber (n : Float) : NanBoxed :=
  if n.isNaN then
    { bits := canonicalNaNBits }
  else
    { bits := Float.toBits n }

def encodeNull : NanBoxed :=
  mkTagged .null 0

def encodeUndefined : NanBoxed :=
  mkTagged .undefined 0

def encodeBool (b : Bool) : NanBoxed :=
  mkTagged .bool (if b then 1 else 0)

def encodeInt32 (i : Int32) : NanBoxed :=
  mkTagged .int32 i.toUInt32.toUInt64

/-- `sid` is a runtime string table identifier (ECMA-262 §6.1.4). -/
def encodeStringRef (sid : Nat) : NanBoxed :=
  mkTagged .string (UInt64.ofNat sid)

/-- `oid` is a runtime heap object identifier (ECMA-262 §6.1.7). -/
def encodeObjectRef (oid : Nat) : NanBoxed :=
  mkTagged .object (UInt64.ofNat oid)

def encodeSymbolRef (sid : Nat) : NanBoxed :=
  mkTagged .symbol (UInt64.ofNat sid)

/-- Decoded view of runtime values for interpreters and tests. -/
inductive Decoded where
  | number (n : Float)
  | null
  | undefined
  | bool (b : Bool)
  | int32 (i : Int32)
  | stringRef (sid : Nat)
  | objectRef (oid : Nat)
  | symbolRef (sid : Nat)
  deriving Repr, BEq

def decode (v : NanBoxed) : Decoded :=
  match getTag? v with
  | none => .number (Float.ofBits v.bits)
  | some .null => .null
  | some .undefined => .undefined
  | some .bool => .bool (getPayload v != 0)
  | some .int32 => .int32 (getPayload v).toUInt32.toInt32
  | some .string => .stringRef (getPayload v).toNat
  | some .object => .objectRef (getPayload v).toNat
  | some .symbol => .symbolRef (getPayload v).toNat

def decodeToNumber? (v : NanBoxed) : Option Float :=
  match decode v with
  | .number n => some n
  | _ => none

def decodeToBool? (v : NanBoxed) : Option Bool :=
  match decode v with
  | .bool b => some b
  | _ => none

def decodeToInt32? (v : NanBoxed) : Option Int32 :=
  match decode v with
  | .int32 i => some i
  | _ => none

/-- Extract a string reference ID, or `none` if not a string. -/
def decodeToStringRef? (v : NanBoxed) : Option Nat :=
  match decode v with
  | .stringRef sid => some sid
  | _ => none

/-- Extract an object reference ID, or `none` if not an object. -/
def decodeToObjectRef? (v : NanBoxed) : Option Nat :=
  match decode v with
  | .objectRef oid => some oid
  | _ => none

/-- Extract a symbol reference ID, or `none` if not a symbol. -/
def decodeToSymbolRef? (v : NanBoxed) : Option Nat :=
  match decode v with
  | .symbolRef sid => some sid
  | _ => none

/-- Is this value truthy? (ECMA-262 §7.1.2 ToBoolean) -/
def isTruthy (v : NanBoxed) : Bool :=
  match decode v with
  | .undefined | .null => false
  | .bool b => b
  | .number n => !n.isNaN && n != 0.0
  | .int32 i => i != 0
  | .stringRef _ | .objectRef _ | .symbolRef _ => true

/-- Is this value a string reference? -/
def isString (v : NanBoxed) : Bool := getTag? v == some .string

/-- Is this value an object reference? -/
def isObject (v : NanBoxed) : Bool := getTag? v == some .object

/-- Is this value null or undefined? -/
def isNullish (v : NanBoxed) : Bool :=
  match getTag? v with
  | some .null | some .undefined => true
  | _ => false

/-! Sanity checks for the NaN-box encoding. -/
example : decode encodeNull = .null := rfl
example : decode encodeUndefined = .undefined := rfl
example : decode (encodeBool true) = .bool true := rfl
example : decode (encodeBool false) = .bool false := rfl
example : decode (encodeStringRef 42) = .stringRef 42 := rfl
example : decode (encodeObjectRef 7) = .objectRef 7 := rfl
example : decode (encodeSymbolRef 999) = .symbolRef 999 := rfl
example : decode (encodeInt32 (Int32.ofInt (-12345))) = .int32 (Int32.ofInt (-12345)) := rfl
example : decodeToNumber? encodeNull = none := rfl
example : decodeToBool? (encodeBool true) = some true := rfl
example : decodeToInt32? (encodeInt32 (Int32.ofInt (-1))) = some (Int32.ofInt (-1)) := rfl
example : decodeToStringRef? (encodeStringRef 42) = some 42 := rfl
example : decodeToObjectRef? (encodeObjectRef 7) = some 7 := rfl
example : decodeToSymbolRef? (encodeSymbolRef 99) = some 99 := rfl
example : isTruthy encodeNull = false := rfl
example : isTruthy encodeUndefined = false := rfl
example : isTruthy (encodeBool false) = false := rfl
example : isTruthy (encodeBool true) = true := rfl
example : isTruthy (encodeStringRef 0) = true := rfl
example : isTruthy (encodeObjectRef 1) = true := rfl
example : isString (encodeStringRef 5) = true := rfl
example : isObject (encodeObjectRef 3) = true := rfl
example : isNullish encodeNull = true := rfl
example : isNullish encodeUndefined = true := rfl
example : isNullish (encodeBool false) = false := rfl

/-! ## Round-trip theorems for NaN-boxing.
    These prove that encode→decode is the identity for all non-number tags.
    The proof agent can use these to reason about value preservation across
    the compiler pipeline. -/

@[simp] theorem decode_encodeNull : decode encodeNull = .null := rfl
@[simp] theorem decode_encodeUndefined : decode encodeUndefined = .undefined := rfl
@[simp] theorem decode_encodeBool (b : Bool) : decode (encodeBool b) = .bool b := by cases b <;> rfl

/-- Bool round-trip: decodeToBool? ∘ encodeBool = some -/
@[simp] theorem decodeToBool_encodeBool (b : Bool) : decodeToBool? (encodeBool b) = some b := by
  cases b <;> rfl

/-- Truthiness of booleans matches the boolean value. -/
@[simp] theorem isTruthy_encodeBool (b : Bool) : isTruthy (encodeBool b) = b := by
  cases b <;> rfl

/-- Null is always falsy. -/
@[simp] theorem isTruthy_encodeNull : isTruthy encodeNull = false := rfl
/-- Undefined is always falsy. -/
@[simp] theorem isTruthy_encodeUndefined : isTruthy encodeUndefined = false := rfl

/-- isBoxed is true for all tagged values. -/
@[simp] theorem isBoxed_encodeNull : isBoxed encodeNull = true := rfl
@[simp] theorem isBoxed_encodeUndefined : isBoxed encodeUndefined = true := rfl
@[simp] theorem isBoxed_encodeBool (b : Bool) : isBoxed (encodeBool b) = true := by cases b <;> rfl

/-- Tag extraction for tagged values. -/
@[simp] theorem getTag_encodeNull : getTag? encodeNull = some .null := rfl
@[simp] theorem getTag_encodeUndefined : getTag? encodeUndefined = some .undefined := rfl
@[simp] theorem getTag_encodeBool (b : Bool) : getTag? (encodeBool b) = some .bool := by cases b <;> rfl

/-- String ref round-trip: decodeToStringRef? ∘ encodeStringRef = some -/
theorem decodeToStringRef_encodeStringRef (sid : Nat) :
    decodeToStringRef? (encodeStringRef sid) = some sid := by sorry -- TODO: bit-level round-trip

/-- Object ref round-trip: decodeToObjectRef? ∘ encodeObjectRef = some -/
theorem decodeToObjectRef_encodeObjectRef (oid : Nat) :
    decodeToObjectRef? (encodeObjectRef oid) = some oid := by sorry -- TODO: bit-level round-trip

/-- isString detects encoded string refs. -/
theorem isString_encodeStringRef (sid : Nat) :
    isString (encodeStringRef sid) = true := by sorry -- TODO: bit-level round-trip

/-- isObject detects encoded object refs. -/
theorem isObject_encodeObjectRef (oid : Nat) :
    isObject (encodeObjectRef oid) = true := by sorry -- TODO: bit-level round-trip

/-- isNullish is true for null. -/
@[simp] theorem isNullish_encodeNull : isNullish encodeNull = true := rfl
/-- isNullish is true for undefined. -/
@[simp] theorem isNullish_encodeUndefined : isNullish encodeUndefined = true := rfl
/-- isNullish is false for booleans. -/
@[simp] theorem isNullish_encodeBool (b : Bool) : isNullish (encodeBool b) = false := by
  cases b <;> rfl

/-- String refs are truthy. -/
@[simp] theorem isTruthy_encodeStringRef (sid : Nat) :
    isTruthy (encodeStringRef sid) = true := rfl

/-- Object refs are truthy. -/
@[simp] theorem isTruthy_encodeObjectRef (oid : Nat) :
    isTruthy (encodeObjectRef oid) = true := rfl

/-- String refs are not nullish. -/
@[simp] theorem isNullish_encodeStringRef (sid : Nat) :
    isNullish (encodeStringRef sid) = false := rfl

/-- Object refs are not nullish. -/
@[simp] theorem isNullish_encodeObjectRef (oid : Nat) :
    isNullish (encodeObjectRef oid) = false := rfl

/-- Tag extraction for string refs. -/
@[simp] theorem getTag_encodeStringRef (sid : Nat) :
    getTag? (encodeStringRef sid) = some .string := rfl

/-- Tag extraction for object refs. -/
@[simp] theorem getTag_encodeObjectRef (oid : Nat) :
    getTag? (encodeObjectRef oid) = some .object := rfl

/-- Tag extraction for int32 values. -/
@[simp] theorem getTag_encodeInt32 (i : Int32) :
    getTag? (encodeInt32 i) = some .int32 := rfl

/-- Int32 round-trip: decodeToInt32? ∘ encodeInt32 = some -/
@[simp] theorem decodeToInt32_encodeInt32 (i : Int32) :
    decodeToInt32? (encodeInt32 i) = some i := by
  simp [decodeToInt32?, decode, encodeInt32, mkTagged, getTag?, getPayload,
        isBoxed, nanMask, tagMask, payloadMask, tagInt32, bitsToTag?,
        tagNull, tagUndefined, tagBool, tagString, tagObject, tagSymbol]

end NanBoxed

end VerifiedJS.Runtime
