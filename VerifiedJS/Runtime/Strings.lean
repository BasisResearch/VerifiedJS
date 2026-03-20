/-
  VerifiedJS — String Representation
  Interned, UTF-16, stored in linear memory.
  SPEC: ECMA-262 §6.1.4 The String Type, §21.1 String Objects.

  Strings are sequences of 16-bit code units (UTF-16).  At the Wasm level
  they live in linear memory and are interned: two strings with identical
  content share the same string ID.  The specification model below captures
  the interning invariant and the key string operations the compiler emits.
-/

namespace VerifiedJS.Runtime

/-! ## UTF-16 Code Units (ECMA-262 §6.1.4) -/

/-- A UTF-16 code unit (16-bit unsigned). -/
abbrev CodeUnit := UInt16

/-- A JS string is a finite ordered sequence of zero or more 16-bit code units.
    SPEC: §6.1.4 "a finite ordered sequence of zero or more 16-bit unsigned
    integer values". -/
abbrev JSString := List CodeUnit

/-! ## String Interning Table

    The runtime maintains a table mapping interned string IDs to their
    content.  Two strings with the same content always receive the same ID,
    which enables O(1) string equality (pointer comparison). -/

/-- The interning table maps IDs to string content. -/
structure StringTable where
  /-- Forward map: ID → content. -/
  strings : Array JSString
  deriving Repr

def StringTable.empty : StringTable :=
  { strings := #[] }

/-- Look up string content by ID. -/
def StringTable.get? (tbl : StringTable) (sid : Nat) : Option JSString :=
  tbl.strings[sid]?

/-- Intern a string: if it already exists, return existing ID; otherwise allocate a new one.
    SPEC: interning invariant — `intern s1 = intern s2 ↔ s1 = s2`. -/
def StringTable.intern (tbl : StringTable) (s : JSString) : Nat × StringTable :=
  -- Check for existing entry
  match tbl.strings.toList.findIdx? (· == s) with
  | some idx => (idx, tbl)
  | none =>
    let sid := tbl.strings.size
    (sid, { strings := tbl.strings.push s })

/-- The number of interned strings. -/
def StringTable.size (tbl : StringTable) : Nat :=
  tbl.strings.size

/-! ## String Operations (ECMA-262 §21.1.3)

    These are the specification-level operations the compiler may emit calls
    to.  They operate on `JSString` (lists of code units). -/

/-- String length in code units (§21.1.3.3 String.prototype.length). -/
def jsStringLength (s : JSString) : Nat :=
  s.length

/-- Character at index (§21.1.3.1 String.prototype.charAt).
    Returns empty string if out of bounds. -/
def jsStringCharAt (s : JSString) (idx : Nat) : JSString :=
  match s[idx]? with
  | some cu => [cu]
  | none => []

/-- Code unit at index (§21.1.3.2 String.prototype.charCodeAt).
    Returns none (NaN in JS) if out of bounds. -/
def jsStringCharCodeAt (s : JSString) (idx : Nat) : Option UInt16 :=
  s[idx]?

/-- String concatenation (§21.1.3.4 String.prototype.concat). -/
def jsStringConcat (a b : JSString) : JSString :=
  a ++ b

/-- Substring extraction (§21.1.3.22 String.prototype.slice — simplified).
    `start` and `end_` are clamped to [0, len]. -/
def jsStringSlice (s : JSString) (start end_ : Int) : JSString :=
  let len := s.length
  let clamp (i : Int) : Nat :=
    if i < 0 then
      let adjusted := Int.ofNat len + i
      if adjusted < 0 then 0 else adjusted.toNat
    else
      min i.toNat len
  let start' := clamp start
  let end' := clamp end_
  if start' >= end' then []
  else (s.drop start').take (end' - start')

/-- String equality (ECMA-262 §7.2.12 SameValueNonNumber for strings).
    Since we use interning, this can be done by ID comparison at runtime. -/
def jsStringEqual (a b : JSString) : Bool :=
  a == b

/-- String comparison (§7.2.13 IsLessThan for strings). Lexicographic
    comparison of code unit sequences. -/
def jsStringLessThan : JSString → JSString → Bool
  | [], _ :: _ => true
  | [], [] => false
  | _ :: _, [] => false
  | a :: as_, b :: bs =>
    if a.toNat < b.toNat then true
    else if a.toNat > b.toNat then false
    else jsStringLessThan as_ bs

/-- indexOf (§21.1.3.9 String.prototype.indexOf — simplified). -/
def jsStringIndexOf (haystack needle : JSString) (fromIdx : Nat := 0) : Int :=
  let hLen := haystack.length
  let nLen := needle.length
  if nLen == 0 then Int.ofNat (min fromIdx hLen)
  else
    -- Use List.range to avoid termination issues
    let candidates := (List.range (hLen - nLen + 1)).drop fromIdx
    match candidates.find? (fun i => (haystack.drop i).take nLen == needle) with
    | some i => Int.ofNat i
    | none => -1

/-! ## Encoding Helpers

    Conversion between Lean `String` (UTF-8) and `JSString` (UTF-16) for
    test/interop convenience. -/

/-- Encode a single Unicode scalar value to UTF-16 code units. -/
def charToUTF16 (c : Char) : List CodeUnit :=
  let cp := c.toNat
  if cp < 0x10000 then
    [UInt16.ofNat cp]
  else
    -- Surrogate pair: ECMA-262 §6.1.4 Note 2
    let cp' := cp - 0x10000
    let hi := 0xD800 + (cp' / 0x400)
    let lo := 0xDC00 + (cp' % 0x400)
    [UInt16.ofNat hi, UInt16.ofNat lo]

/-- Convert a Lean String to JSString (UTF-16). -/
def stringToJSString (s : String) : JSString :=
  s.toList.flatMap charToUTF16

/-- Convert a JSString back to a Lean String (lossy for unpaired surrogates).
    Only handles BMP characters; surrogate pairs are replaced with U+FFFD. -/
def jsStringToString (s : JSString) : String :=
  -- Simplified: treat each code unit as a BMP character
  -- Full surrogate pair decoding would require more complex state tracking
  let chars := s.map fun cu =>
    let v := cu.toNat
    if v >= 0xD800 && v <= 0xDFFF then Char.ofNat 0xFFFD  -- surrogate → replacement
    else Char.ofNat v
  String.ofList chars

/-! ## Linear Memory Layout

    In Wasm linear memory, strings are stored as:
    ```
    offset 0: length  (i32)  — number of code units
    offset 4: data    (u16[length]) — code unit array
    ```
    Total size: 4 + 2 * length bytes, padded to 4-byte alignment.
-/

/-- Size in bytes of a string in linear memory (header + data, 4-byte aligned). -/
def jsStringMemSize (s : JSString) : Nat :=
  let dataBytes := 2 * s.length
  let total := 4 + dataBytes
  -- Round up to 4-byte alignment
  (total + 3) / 4 * 4

end VerifiedJS.Runtime
