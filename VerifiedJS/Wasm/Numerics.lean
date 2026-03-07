/-
  VerifiedJS — Wasm Numeric Operations
  i32/i64/f32/f64 operations.
-/

namespace VerifiedJS.Wasm.Numerics

-- i32 operations
def i32Add (a b : UInt32) : UInt32 := a + b
def i32Sub (a b : UInt32) : UInt32 := a - b
def i32Mul (a b : UInt32) : UInt32 := a * b

-- i64 operations
def i64Add (a b : UInt64) : UInt64 := a + b
def i64Sub (a b : UInt64) : UInt64 := a - b
def i64Mul (a b : UInt64) : UInt64 := a * b

-- f64 operations
def f64Add (a b : Float) : Float := a + b
def f64Sub (a b : Float) : Float := a - b
def f64Mul (a b : Float) : Float := a * b
def f64Div (a b : Float) : Float := a / b

-- TODO: Complete numeric operations per Wasm spec

end VerifiedJS.Wasm.Numerics
