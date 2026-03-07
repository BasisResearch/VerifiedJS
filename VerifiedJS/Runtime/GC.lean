/-
  VerifiedJS — Garbage Collector
  Bump allocator + mark-sweep GC compiled into the Wasm module.
-/

namespace VerifiedJS.Runtime

/-- GC metadata — part of the runtime linked into every output module -/
structure GCState where
  heapBase : Nat
  heapEnd : Nat
  allocPtr : Nat
  markBitsSize : Nat  -- size of mark bitmap in bytes

-- TODO: Implement mark-sweep GC in Wasm IR
-- The GC is part of the runtime and its semantics are axiomatic (TCB boundary).

end VerifiedJS.Runtime
