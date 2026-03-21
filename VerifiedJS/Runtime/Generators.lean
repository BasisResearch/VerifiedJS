/-
  VerifiedJS — Generators and Async
  State machine representation for generators and async/await.
  SPEC: ECMA-262 §14.4 Generator Function Definitions
  SPEC: ECMA-262 §14.7 Async Function Definitions
  SPEC: ECMA-262 §25.4 Promise Objects
  SPEC: ECMA-262 §27.3 GeneratorFunction Objects
-/

import VerifiedJS.Flat.Syntax

namespace VerifiedJS.Runtime.Generators

open VerifiedJS.Flat

/-! ## Generator State Machine

    Generators are compiled to state machines with explicit suspension points.
    Each `yield` becomes a state transition that saves the current local
    environment and returns a value to the caller. On resumption (`.next(v)`),
    the state machine advances from the saved state with `v` as the yield result.

    REF: ECMA-262 §27.5.3 GeneratorResume -/

/-- Generator execution state per ECMA-262 §27.5.3. -/
inductive GeneratorState where
  | suspended     -- created but not started, or paused at yield
  | executing     -- currently running (re-entrance forbidden)
  | completed     -- returned or threw (terminal)
  deriving Repr, BEq

/-- A single suspension point in the compiled state machine.
    Each yield in the source becomes one of these. -/
structure SuspensionPoint where
  stateId : Nat              -- unique state machine state index
  savedLocals : List VarName -- local variables to save/restore
  resumeExpr : Expr          -- expression to evaluate on resume
  deriving Repr

/-- Compiled generator: a state machine with suspension points. -/
structure GeneratorDef where
  name : String
  params : List VarName
  initialExpr : Expr                     -- entry-point expression
  suspensions : Array SuspensionPoint    -- yield points (indexed by stateId)
  deriving Repr

/-- Result of a single `.next(v)` call on a generator.
    SPEC: ECMA-262 §27.5.3.3 GeneratorYield / §27.5.3.4 GeneratorResumeAbrupt -/
structure IteratorResult where
  value : Value    -- yielded or returned value
  done : Bool      -- true when generator has completed
  deriving Repr, BEq

/-- Runtime generator instance: the live execution state. -/
structure GeneratorInstance where
  def_ : GeneratorDef
  state : GeneratorState
  currentStateId : Nat           -- which suspension point we're at (0 = initial)
  locals : List (VarName × Value) -- saved local environment
  deriving Repr

/-- Create a fresh generator instance from a definition. -/
def GeneratorInstance.create (gd : GeneratorDef) (args : List Value) : GeneratorInstance :=
  { def_ := gd
    state := .suspended
    currentStateId := 0
    locals := gd.params.zip args }

/-! ## Async/Await

    Async functions are desugared into generators + promise wrappers.
    `await expr` becomes `yield expr` in the generator, with the driver
    resolving the yielded promise before resuming.

    REF: ECMA-262 §27.7.5.1 AsyncFunctionStart -/

/-- Promise state per ECMA-262 §25.6.1. -/
inductive PromiseState where
  | pending
  | fulfilled (value : Value)
  | rejected (reason : Value)
  deriving Repr, BEq

/-- A promise object reference. In the Wasm runtime, promises are heap-allocated
    objects; here we model them by their resolution state. -/
structure Promise where
  state : PromiseState
  deriving Repr, BEq

end VerifiedJS.Runtime.Generators
