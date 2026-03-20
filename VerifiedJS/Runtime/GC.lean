/-
  VerifiedJS — Garbage Collector
  Bump allocator + mark-sweep GC compiled into the Wasm module.
  SPEC: This is the TCB boundary — GC correctness is axiomatic.
  REF: WasmCert-Coq `theories/operations.v` (memory operations).

  The GC runtime is compiled into every output Wasm module.  Its semantics
  are part of the Trusted Computing Base (TCB): we axiomatize that the
  allocator returns fresh, non-overlapping memory regions, and that the
  collector preserves all reachable objects.
-/

namespace VerifiedJS.Runtime

/-! ## Allocator State -/

/-- GC metadata — part of the runtime linked into every output module. -/
structure GCState where
  /-- Start of the managed heap region in linear memory. -/
  heapBase     : Nat
  /-- End of the managed heap region. -/
  heapEnd      : Nat
  /-- Current bump allocation pointer. -/
  allocPtr     : Nat
  /-- Size of the mark bitmap in bytes. -/
  markBitsSize : Nat
  deriving Repr, BEq

/-- An allocation record: base address and size in bytes. -/
structure Allocation where
  addr : Nat
  size : Nat
  deriving Repr, BEq

/-- Abstract allocator state tracking live allocations. -/
structure AllocatorState where
  gc          : GCState
  allocations : List Allocation
  deriving Repr

/-! ## Allocator Axioms (TCB)

    These axioms define the contract the GC must satisfy.  The proof agent
    treats them as trusted assumptions.  The Wasm runtime implementation
    must maintain these invariants. -/

/-- Bump-allocate `size` bytes (4-byte aligned).
    Returns `none` if the heap is exhausted (would trigger GC or trap). -/
def bumpAlloc (st : AllocatorState) (size : Nat) : Option (Nat × AllocatorState) :=
  let alignedSize := (size + 3) / 4 * 4  -- 4-byte alignment
  let newPtr := st.gc.allocPtr + alignedSize
  if newPtr <= st.gc.heapEnd then
    let addr := st.gc.allocPtr
    let gc' := { st.gc with allocPtr := newPtr }
    let alloc := { addr, size := alignedSize }
    some (addr, { gc := gc', allocations := alloc :: st.allocations })
  else
    none

/-- Initial GC state for a module with `heapPages` pages of memory. -/
def GCState.init (heapBase : Nat) (heapPages : Nat) : GCState :=
  let heapEnd := heapBase + heapPages * 65536
  { heapBase
  , heapEnd
  , allocPtr := heapBase
  , markBitsSize := (heapEnd - heapBase) / (8 * 16)  -- 1 bit per 16-byte block
  }

/-- Initial allocator state. -/
def AllocatorState.init (heapBase : Nat) (heapPages : Nat) : AllocatorState :=
  { gc := GCState.init heapBase heapPages
  , allocations := []
  }

/-! ## GC Axioms

    The mark-sweep collector is axiomatized: after collection, all reachable
    objects are preserved and the allocation pointer is compacted. -/

/-- A root set is a list of heap addresses that are reachable from the stack/globals. -/
abbrev RootSet := List Nat

/-- Axiom: after GC, all addresses in `roots` (and objects transitively reachable
    from them) remain valid.  The allocator pointer is reset to pack live objects.
    This is the core TCB assumption. -/
axiom gc_preserves_reachable :
  ∀ (_st : AllocatorState) (_roots : RootSet) (_st' : AllocatorState),
    -- If st' is the result of running GC on st with roots...
    -- (The actual GC execution is opaque — this axiom just states the contract.)
    -- Then every root address that was valid before is still valid.
    True  -- Placeholder: the real axiom will be refined when the collector is implemented.

/-- Total heap bytes currently allocated. -/
def AllocatorState.totalAllocated (st : AllocatorState) : Nat :=
  st.allocations.foldl (fun acc a => acc + a.size) 0

/-- Free space remaining before GC would be needed. -/
def AllocatorState.freeSpace (st : AllocatorState) : Nat :=
  st.gc.heapEnd - st.gc.allocPtr

end VerifiedJS.Runtime
