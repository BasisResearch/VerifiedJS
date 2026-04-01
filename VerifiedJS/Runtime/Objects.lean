/-
  VerifiedJS — Object Representation
  Property maps as linked hash tables in linear memory.
  SPEC: ECMA-262 §9.1 Ordinary Object Internal Methods, §6.1.7 The Object Type.
  REF: WasmCert-Coq `theories/datatypes.v` (store structure).

  This module defines the *specification-level* object model that the compiler
  targets when lowering to Wasm linear memory.  It is NOT the Core/Flat heap
  abstraction (which uses `Array (List (PropName × Value))`), but rather the
  concrete layout the Wasm runtime uses.
-/

import VerifiedJS.Runtime.Values

namespace VerifiedJS.Runtime

/-! ## Property Descriptors (ECMA-262 §6.1.7.1) -/

/-- Simplified property attributes.  We model the data-descriptor subset
    of ECMA-262 §6.1.7.1 Property Descriptor that the compiler currently emits. -/
structure PropertyFlags where
  writable     : Bool := true
  enumerable   : Bool := true
  configurable : Bool := true
  deriving Repr, BEq, DecidableEq

/-- A single property slot in an object.
    Keys are strings (interned string IDs); computed/symbol keys are future work. -/
structure Property where
  key   : Nat            -- interned string ID
  value : NanBoxed       -- NaN-boxed runtime value
  flags : PropertyFlags
  deriving Repr, BEq

/-! ## Object Header Layout (linear memory)

    In Wasm linear memory an object is laid out as:
    ```
    offset 0:  proto_ptr   (i32)  — pointer to prototype object (0 = null)
    offset 4:  prop_count  (i32)  — number of own properties
    offset 8:  capacity    (i32)  — allocated slots
    offset 12: hash_shift  (i32)  — log₂(capacity) for hash table sizing
    offset 16: props_start        — inline property entries begin here
    ```
    Each property entry is 20 bytes:
    ```
    +0:  key_sid   (i32) — interned string ID
    +4:  value     (i64) — NaN-boxed value (8 bytes)
    +12: flags     (i32) — packed property flags
    +16: next      (i32) — hash chain link (-1 = end)
    ```
-/

/-- Byte offsets within the object header. -/
def objHeaderProtoOff   : Nat := 0
def objHeaderCountOff   : Nat := 4
def objHeaderCapOff     : Nat := 8
def objHeaderShiftOff   : Nat := 12
def objHeaderPropsStart : Nat := 16

/-- Size of each property entry in bytes. -/
def propEntrySize : Nat := 20

/-! ## Abstract Object Model

    The spec-level model mirrors the linear-memory layout but uses Lean
    data structures so that the proof agent can reason symbolically. -/

/-- An abstract JS object in the runtime.
    SPEC: ECMA-262 §9.1 OrdinaryObject. -/
structure ObjectRecord where
  /-- Pointer to prototype (none = null prototype). -/
  prototype  : Option Nat
  /-- Own properties in insertion order. -/
  properties : List Property
  deriving Repr, BEq

/-- The runtime object heap — maps addresses to object records. -/
structure ObjectHeap where
  objects  : Array ObjectRecord
  nextAddr : Nat
  deriving Repr

def ObjectHeap.empty : ObjectHeap :=
  { objects := #[], nextAddr := 0 }

/-- Allocate a fresh object with a given prototype.
    SPEC: §9.1.12 OrdinaryObjectCreate (p, additionalInternalSlotsList). -/
def ObjectHeap.alloc (heap : ObjectHeap) (proto : Option Nat) : Nat × ObjectHeap :=
  let addr := heap.nextAddr
  let obj : ObjectRecord := { prototype := proto, properties := [] }
  (addr, { objects := heap.objects.push obj, nextAddr := addr + 1 })

/-! ## Property Access (ECMA-262 §9.1.7, §9.1.8, §9.1.9) -/

/-- Look up an own property by key (string ID).
    SPEC: §9.1.1 [[GetOwnProperty]] (O, P). -/
def ObjectRecord.getOwnProperty? (obj : ObjectRecord) (key : Nat) : Option Property :=
  obj.properties.find? (fun p => p.key == key)

/-- Look up a property by key, traversing the prototype chain.
    SPEC: §9.1.8 [[Get]] (P, Receiver) — simplified (no Receiver proxy logic).
    Terminates by decreasing fuel (max prototype chain depth). -/
def ObjectHeap.get? (heap : ObjectHeap) (addr : Nat) (key : Nat) (fuel : Nat := 256) : Option NanBoxed :=
  match fuel with
  | 0 => none  -- prototype chain too deep (defensive bound)
  | fuel' + 1 =>
    if h : addr < heap.objects.size then
      let obj := heap.objects[addr]
      match obj.getOwnProperty? key with
      | some prop => some prop.value
      | none =>
        match obj.prototype with
        | some protoAddr => heap.get? protoAddr key fuel'
        | none => none
    else
      none

/-- Set a property on an own object (does not traverse prototype chain for writes).
    SPEC: §9.1.9 [[Set]] (P, V, Receiver) — simplified data property set. -/
def ObjectHeap.set (heap : ObjectHeap) (addr : Nat) (key : Nat) (value : NanBoxed) : ObjectHeap :=
  if h : addr < heap.objects.size then
    let obj := heap.objects[addr]
    let props' :=
      if obj.properties.any (fun p => p.key == key) then
        obj.properties.map (fun p => if p.key == key then { p with value } else p)
      else
        obj.properties ++ [{ key, value, flags := {} }]
    let obj' := { obj with properties := props' }
    { heap with objects := heap.objects.set! addr obj' }
  else
    heap

/-- Delete an own property by key.
    SPEC: §9.1.10 [[Delete]] (P). -/
def ObjectHeap.delete (heap : ObjectHeap) (addr : Nat) (key : Nat) : ObjectHeap :=
  if h : addr < heap.objects.size then
    let obj := heap.objects[addr]
    let props' := obj.properties.filter (fun p => !(p.key == key))
    let obj' := { obj with properties := props' }
    { heap with objects := heap.objects.set! addr obj' }
  else
    heap

/-- Check if an object has an own property.
    SPEC: §9.1.7 [[HasProperty]] for own check. -/
def ObjectHeap.hasOwn (heap : ObjectHeap) (addr : Nat) (key : Nat) : Bool :=
  if h : addr < heap.objects.size then
    let obj := heap.objects[addr]
    obj.properties.any (fun p => p.key == key)
  else
    false

/-- Check if a property exists anywhere in the prototype chain.
    SPEC: §9.1.7 [[HasProperty]] (P). -/
def ObjectHeap.has (heap : ObjectHeap) (addr : Nat) (key : Nat) (fuel : Nat := 256) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if h : addr < heap.objects.size then
      let obj := heap.objects[addr]
      if obj.properties.any (fun p => p.key == key) then true
      else match obj.prototype with
        | some protoAddr => heap.has protoAddr key fuel'
        | none => false
    else
      false

/-- Enumerate own enumerable property keys in insertion order.
    SPEC: §9.1.11 [[OwnPropertyKeys]] (filtered to enumerable). -/
def ObjectRecord.ownKeys (obj : ObjectRecord) : List Nat :=
  (obj.properties.filter (fun p => p.flags.enumerable)).map (fun p => p.key)

end VerifiedJS.Runtime
