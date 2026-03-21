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

/-! ## Generator Operations

    The `.next(v)`, `.return(v)`, and `.throw(v)` methods on generator instances.
    REF: ECMA-262 §27.5.3.3 GeneratorResume -/

/-- Outcome of a generator step: either yields/returns a result, or throws. -/
inductive GeneratorOutcome where
  | result (r : IteratorResult) (gen : GeneratorInstance)
  | throw (reason : Value) (gen : GeneratorInstance)
  deriving Repr

/-- Execute `.next(v)` on a generator instance.
    SPEC: ECMA-262 §27.5.3.3 GeneratorResume
    - If suspended: transition to executing, look up suspension point,
      evaluate resume expression (modeled abstractly), yield/return result.
    - If executing: throw TypeError (re-entrance forbidden).
    - If completed: return { value: undefined, done: true }. -/
def GeneratorInstance.next (gen : GeneratorInstance) (arg : Value) :
    GeneratorOutcome :=
  match gen.state with
  | .executing =>
      -- §27.5.3.3 step 5: if state is executing, throw TypeError
      .throw (.string "TypeError: generator is already executing")
        gen
  | .completed =>
      -- §27.5.3.3 step 8: if state is completed, return { undefined, done: true }
      .result { value := .undefined, done := true } gen
  | .suspended =>
      -- §27.5.3.3 step 9-11: resume from suspension point
      match gen.def_.suspensions[gen.currentStateId]? with
      | none =>
          -- No more suspension points: generator completes
          let gen' := { gen with state := .completed }
          .result { value := .undefined, done := true } gen'
      | some sp =>
          -- Found suspension point: advance to next state
          -- In a full implementation, we'd evaluate sp.resumeExpr with arg
          -- bound as the yield result. Here we model the state transition.
          let gen' := { gen with
            state := .suspended
            currentStateId := sp.stateId + 1
            locals := sp.savedLocals.map (fun n => (n, arg)) }
          .result { value := arg, done := false } gen'

/-- Execute `.return(v)` on a generator instance.
    SPEC: ECMA-262 §27.5.3.4 GeneratorResumeAbrupt (return completion)
    Forces the generator to complete with the given value. -/
def GeneratorInstance.return_ (gen : GeneratorInstance) (val : Value) :
    GeneratorOutcome :=
  match gen.state with
  | .executing =>
      .throw (.string "TypeError: generator is already executing") gen
  | .completed =>
      .result { value := val, done := true } gen
  | .suspended =>
      let gen' := { gen with state := .completed }
      .result { value := val, done := true } gen'

/-- Execute `.throw(v)` on a generator instance.
    SPEC: ECMA-262 §27.5.3.4 GeneratorResumeAbrupt (throw completion)
    Forces an exception into the generator. -/
def GeneratorInstance.throw_ (gen : GeneratorInstance) (reason : Value) :
    GeneratorOutcome :=
  match gen.state with
  | .executing =>
      .throw (.string "TypeError: generator is already executing") gen
  | .completed =>
      .throw reason { gen with state := .completed }
  | .suspended =>
      -- Generator receives the exception; if no try/catch, it completes
      .throw reason { gen with state := .completed }

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

/-- Resolve a pending promise with a value.
    SPEC: ECMA-262 §25.6.1.4 FulfillPromise -/
def Promise.resolve (p : Promise) (val : Value) : Promise :=
  match p.state with
  | .pending => { state := .fulfilled val }
  | _ => p  -- already settled, no-op

/-- Reject a pending promise with a reason.
    SPEC: ECMA-262 §25.6.1.7 RejectPromise -/
def Promise.reject (p : Promise) (reason : Value) : Promise :=
  match p.state with
  | .pending => { state := .rejected reason }
  | _ => p  -- already settled, no-op

/-- Check if a promise is settled (fulfilled or rejected). -/
def Promise.isSettled (p : Promise) : Bool :=
  match p.state with
  | .pending => false
  | _ => true

/-- Extract the value from a fulfilled promise. -/
def Promise.value? (p : Promise) : Option Value :=
  match p.state with
  | .fulfilled v => some v
  | _ => none

end VerifiedJS.Runtime.Generators
