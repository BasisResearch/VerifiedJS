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

end NanBoxed

end VerifiedJS.Runtime
