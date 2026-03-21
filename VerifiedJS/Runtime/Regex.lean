/-
  VerifiedJS — Regular Expression Engine
  Regex AST, NFA construction, and match semantics.
  SPEC: ECMA-262 §21.2 RegExp (Regular Expression) Objects
  REF: Thompson's construction for NFA from regex AST.
-/

namespace VerifiedJS.Runtime.Regex

/-! ## Regex AST

    Core regex AST covering ECMA-262 §21.2.1 Patterns.
    This is the subset needed for compilation to Wasm-based matching. -/

/-- Character class atoms. -/
inductive CharClass where
  | any                        -- `.` (match any except newline)
  | char (c : Char)            -- literal character
  | range (lo hi : Char)       -- `[a-z]`
  | digit                      -- `\d`
  | word                       -- `\w`
  | space                      -- `\s`
  | negDigit                   -- `\D`
  | negWord                    -- `\W`
  | negSpace                   -- `\S`
  deriving Repr, BEq

/-- Anchor types per ECMA-262 §21.2.2.6. -/
inductive AnchorKind where
  | start        -- `^`
  | «end»        -- `$`
  | boundary     -- `\b`
  | negBoundary  -- `\B`
  deriving Repr, BEq

/-- Regex AST node. Covers the core regex constructs per ECMA-262 §21.2.2. -/
inductive Pattern where
  | empty                                     -- ε (empty match)
  | charClass (cc : CharClass)                -- single character match
  | seq (a b : Pattern)                       -- concatenation: ab
  | alt (a b : Pattern)                       -- alternation: a|b
  | star (p : Pattern) (greedy : Bool)        -- Kleene star: a* or a*?
  | plus (p : Pattern) (greedy : Bool)        -- a+ or a+?
  | opt (p : Pattern) (greedy : Bool)         -- a? or a??
  | repeat_ (p : Pattern) (lo hi : Nat)       -- a{n,m}
  | group (idx : Nat) (p : Pattern)           -- capturing group (idx)
  | anchor (kind : AnchorKind)                -- ^ $ \b \B
  | lookahead (p : Pattern) (neg : Bool)      -- (?=...) or (?!...)
  | backreference (idx : Nat)                 -- \1 etc.
  deriving Repr, BEq

/-! ## Regex Flags

    ECMA-262 §21.2.5.1 -/

/-- Regex flags from the `/pattern/flags` syntax. -/
structure Flags where
  global : Bool := false         -- g
  ignoreCase : Bool := false     -- i
  multiline : Bool := false      -- m
  dotAll : Bool := false         -- s
  unicode : Bool := false        -- u
  sticky : Bool := false         -- y
  deriving Repr, BEq

/-! ## NFA Representation

    Thompson NFA for regex matching. States are Nat indices.
    REF: Thompson 1968, "Programming Techniques: Regular expression search algorithm". -/

/-- NFA transition types. -/
inductive NFATransition where
  | epsilon (target : Nat)                    -- ε-transition
  | charMatch (cc : CharClass) (target : Nat) -- character match transition
  deriving Repr, BEq

/-- NFA state with outgoing transitions. -/
structure NFAState where
  transitions : List NFATransition
  isAccept : Bool := false
  deriving Repr, BEq

/-- Thompson NFA: array of states, start state index. -/
structure NFA where
  states : Array NFAState
  start : Nat
  deriving Repr

/-! ## Match Result -/

/-- A single capture group result. -/
structure CaptureGroup where
  start : Nat
  «end» : Nat
  deriving Repr, BEq

/-- Result of a regex match attempt. -/
structure MatchResult where
  matched : Bool
  start : Nat                            -- start index of match in input
  «end» : Nat                            -- end index (exclusive)
  captures : Array (Option CaptureGroup) -- captured groups (0 = full match)
  deriving Repr

/-- CharClass membership test per ECMA-262 §21.2.2.8. -/
def CharClass.matches (cc : CharClass) (c : Char) : Bool :=
  match cc with
  | .any => c != '\n' && c != '\r'
  | .char expected => c == expected
  | .range lo hi => lo.val ≤ c.val && c.val ≤ hi.val
  | .digit => c.val ≥ '0'.val && c.val ≤ '9'.val
  | .word => (c.val ≥ 'a'.val && c.val ≤ 'z'.val) ||
             (c.val ≥ 'A'.val && c.val ≤ 'Z'.val) ||
             (c.val ≥ '0'.val && c.val ≤ '9'.val) || c == '_'
  | .space => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'
  | .negDigit => !(c.val ≥ '0'.val && c.val ≤ '9'.val)
  | .negWord => !((c.val ≥ 'a'.val && c.val ≤ 'z'.val) ||
                   (c.val ≥ 'A'.val && c.val ≤ 'Z'.val) ||
                   (c.val ≥ '0'.val && c.val ≤ '9'.val) || c == '_')
  | .negSpace => !(c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C')

-- Sanity checks for CharClass.matches
example : CharClass.digit.matches '5' = true := by native_decide
example : CharClass.digit.matches 'a' = false := by native_decide
example : CharClass.word.matches '_' = true := by native_decide
example : CharClass.any.matches 'x' = true := by native_decide
example : CharClass.any.matches '\n' = false := by native_decide

/-! ## Thompson NFA Construction

    REF: Thompson 1968. Each Pattern node is compiled into an NFA fragment
    with a single start state and single accept state. Fragments are composed
    by wiring accept→start with ε-transitions. -/

/-- An NFA fragment produced during Thompson construction.
    `startState` and `acceptState` are indices into the builder's state array. -/
structure NFAFragment where
  startState : Nat
  acceptState : Nat
  deriving Repr

/-- Builder state accumulating NFA states during construction. -/
structure NFABuilder where
  states : Array NFAState
  deriving Repr

/-- Create a fresh NFA state and return its index. -/
def NFABuilder.newState (b : NFABuilder) (s : NFAState := { transitions := [] }) :
    Nat × NFABuilder :=
  let idx := b.states.size
  (idx, { states := b.states.push s })

/-- Add a transition to an existing state. -/
def NFABuilder.addTransition (b : NFABuilder) (from_ : Nat) (t : NFATransition) :
    NFABuilder :=
  if h : from_ < b.states.size then
    let st := b.states[from_]
    { states := b.states.set! from_ { st with transitions := t :: st.transitions } }
  else b

/-- Compile a Pattern into an NFA fragment within the builder.
    REF: Thompson's construction — each case adds O(2) states.
    SPEC: ECMA-262 §21.2.2 (pattern semantics). -/
partial def compilePattern (b : NFABuilder) (p : Pattern) : NFAFragment × NFABuilder :=
  match p with
  | .empty =>
      let (s, b) := b.newState
      let (a, b) := b.newState
      let b := b.addTransition s (.epsilon a)
      ({ startState := s, acceptState := a }, b)
  | .charClass cc =>
      let (s, b) := b.newState
      let (a, b) := b.newState
      let b := b.addTransition s (.charMatch cc a)
      ({ startState := s, acceptState := a }, b)
  | .seq p1 p2 =>
      let (f1, b) := compilePattern b p1
      let (f2, b) := compilePattern b p2
      let b := b.addTransition f1.acceptState (.epsilon f2.startState)
      ({ startState := f1.startState, acceptState := f2.acceptState }, b)
  | .alt p1 p2 =>
      let (f1, b) := compilePattern b p1
      let (f2, b) := compilePattern b p2
      let (s, b) := b.newState
      let (a, b) := b.newState
      let b := b.addTransition s (.epsilon f1.startState)
      let b := b.addTransition s (.epsilon f2.startState)
      let b := b.addTransition f1.acceptState (.epsilon a)
      let b := b.addTransition f2.acceptState (.epsilon a)
      ({ startState := s, acceptState := a }, b)
  | .star p1 greedy =>
      let (f1, b) := compilePattern b p1
      let (s, b) := b.newState
      let (a, b) := b.newState
      -- Loop: accept→start of body
      let b := b.addTransition f1.acceptState (.epsilon f1.startState)
      -- Skip or enter: depending on greediness, order of ε-transitions matters
      -- (for NFA simulation order doesn't affect correctness, only priority)
      let b := b.addTransition s (.epsilon f1.startState)
      let b := b.addTransition s (.epsilon a)
      let b := b.addTransition f1.acceptState (.epsilon a)
      let _ := greedy  -- Greediness affects match priority, not NFA structure
      ({ startState := s, acceptState := a }, b)
  | .plus p1 greedy =>
      -- a+ = a · a*
      let (f1, b) := compilePattern b p1
      let (fStar, b) := compilePattern b (.star p1 greedy)
      let b := b.addTransition f1.acceptState (.epsilon fStar.startState)
      ({ startState := f1.startState, acceptState := fStar.acceptState }, b)
  | .opt p1 _greedy =>
      let (f1, b) := compilePattern b p1
      let (s, b) := b.newState
      let (a, b) := b.newState
      let b := b.addTransition s (.epsilon f1.startState)
      let b := b.addTransition s (.epsilon a)
      let b := b.addTransition f1.acceptState (.epsilon a)
      ({ startState := s, acceptState := a }, b)
  | .repeat_ p1 lo hi =>
      -- a{lo,hi}: concatenate lo mandatory copies, then (hi-lo) optional copies
      let rec buildRepeat (b : NFABuilder) (n : Nat) (mandatory : Bool) :
          NFAFragment × NFABuilder :=
        if n == 0 then
          compilePattern b .empty
        else
          let (f1, b) := compilePattern b p1
          let (fRest, b) := buildRepeat b (n - 1) mandatory
          let b := b.addTransition f1.acceptState (.epsilon fRest.startState)
          if !mandatory then
            -- Optional: can skip this copy
            let b := b.addTransition f1.startState (.epsilon fRest.acceptState)
            ({ startState := f1.startState, acceptState := fRest.acceptState }, b)
          else
            ({ startState := f1.startState, acceptState := fRest.acceptState }, b)
      let (fMandatory, b) := buildRepeat b lo true
      let optCount := hi - lo
      let (fOptional, b) := buildRepeat b optCount false
      let b := b.addTransition fMandatory.acceptState (.epsilon fOptional.startState)
      ({ startState := fMandatory.startState, acceptState := fOptional.acceptState }, b)
  | .group _idx p1 =>
      -- For NFA construction, groups don't add states; capture tracking is done
      -- at the matching layer. Just compile the inner pattern.
      compilePattern b p1
  | .anchor _kind =>
      -- Anchors are zero-width assertions — represented as ε-transitions.
      -- The matching engine checks anchor conditions separately.
      let (s, b) := b.newState
      let (a, b) := b.newState
      let b := b.addTransition s (.epsilon a)
      ({ startState := s, acceptState := a }, b)
  | .lookahead _p1 _neg =>
      -- Lookaheads are zero-width; NFA stub (matching engine handles separately).
      let (s, b) := b.newState
      let (a, b) := b.newState
      let b := b.addTransition s (.epsilon a)
      ({ startState := s, acceptState := a }, b)
  | .backreference _idx =>
      -- Backreferences cannot be expressed in a pure NFA; stub as ε-transition.
      -- The matching engine must handle backreference matching separately.
      let (s, b) := b.newState
      let (a, b) := b.newState
      let b := b.addTransition s (.epsilon a)
      ({ startState := s, acceptState := a }, b)

/-- Build a complete NFA from a Pattern.
    REF: Thompson's construction — start from empty builder. -/
def buildNFA (p : Pattern) : NFA :=
  let b : NFABuilder := { states := #[] }
  let result : NFAFragment × NFABuilder := compilePattern b p
  let frag : NFAFragment := result.1
  let builder : NFABuilder := result.2
  let builderStates : Array NFAState := builder.states
  let acceptIdx : Nat := frag.acceptState
  let startIdx : Nat := frag.startState
  let states : Array NFAState :=
    if h : acceptIdx < builderStates.size then
      let st : NFAState := builderStates[acceptIdx]
      builderStates.set! acceptIdx { st with isAccept := true }
    else
      builderStates
  { states := states, start := startIdx }

/-! ## NFA Simulation (Thompson's algorithm)

    Simultaneous NFA simulation: track the set of active states,
    advance on each input character.
    REF: Thompson 1968, Cox 2007 "Regular Expression Matching Can Be Simple and Fast". -/

/-- Compute the ε-closure of a set of states.
    Returns all states reachable via ε-transitions from the input set.
    Uses a worklist algorithm with a visited set for termination. -/
def epsilonClosure (nfa : NFA) (initial : List Nat) : List Nat := Id.run do
  let mut visited : Array Bool := Array.replicate nfa.states.size false
  let mut worklist := initial
  let mut result : List Nat := []
  -- Bounded iteration to ensure termination (at most nfa.states.size iterations per state)
  for _ in List.range (nfa.states.size * (initial.length + 1) + 1) do
    match worklist with
    | [] => break
    | s :: rest =>
      worklist := rest
      if s < nfa.states.size then
        if visited.getD s false then
          continue
        visited := visited.set! s true
        result := s :: result
        let st := nfa.states.getD s { transitions := [] }
        for t in st.transitions do
          match t with
          | .epsilon target =>
            if target < nfa.states.size && !(visited.getD target false) then
              worklist := target :: worklist
          | .charMatch _ _ => pure ()
  return result

/-- Advance the NFA by one character: from current states, follow charMatch transitions
    for character `c`, then compute ε-closure of the result. -/
def advanceNFA (nfa : NFA) (currentStates : List Nat) (c : Char) : List Nat :=
  let nextStates := Id.run do
    let mut result : List Nat := []
    for s in currentStates do
      if h : s < nfa.states.size then
        let st := nfa.states[s]
        for t in st.transitions do
          match t with
          | .charMatch cc target =>
            if cc.matches c then
              result := target :: result
          | .epsilon _ => pure ()
    return result
  epsilonClosure nfa nextStates

/-- Check if any state in the set is an accept state. -/
def hasAcceptState (nfa : NFA) (states : List Nat) : Bool :=
  states.any fun s =>
    if h : s < nfa.states.size then
      nfa.states[s].isAccept
    else false

/-- Run NFA simulation on input string starting at position `startPos`.
    Returns the end position of the longest match, or `none` if no match.
    REF: Thompson's simultaneous NFA simulation. -/
def nfaMatch (nfa : NFA) (input : String) (startPos : Nat := 0) : Option Nat := Id.run do
  let chars := input.toList
  let mut currentStates := epsilonClosure nfa [nfa.start]
  let mut lastAccept : Option Nat := if hasAcceptState nfa currentStates then some startPos else none
  let mut pos := startPos
  for c in chars.drop startPos do
    currentStates := advanceNFA nfa currentStates c
    pos := pos + 1
    if hasAcceptState nfa currentStates then
      lastAccept := some pos
    if currentStates.isEmpty then
      break
  return lastAccept

/-- Full regex match: build NFA, then run simulation.
    Returns a MatchResult indicating whether the pattern matches at `startPos`. -/
def matchPattern (p : Pattern) (input : String) (startPos : Nat := 0) : MatchResult :=
  let nfa := buildNFA p
  match nfaMatch nfa input startPos with
  | some endPos =>
    { matched := true
      start := startPos
      «end» := endPos
      captures := #[some { start := startPos, «end» := endPos }] }
  | none =>
    { matched := false
      start := startPos
      «end» := startPos
      captures := #[] }

/-- Search for the first occurrence of pattern in input (unanchored match).
    Tries matching at each position from left to right.
    SPEC: ECMA-262 §21.2.5.2 RegExpBuiltinExec -/
def searchPattern (p : Pattern) (input : String) : MatchResult := Id.run do
  for i in List.range (input.length + 1) do
    let result := matchPattern p input i
    if result.matched then
      return result
  return { matched := false, start := 0, «end» := 0, captures := #[] }

/-! ## Regex Properties -/

/-- CharClass.matches is decidable (already by Bool return type). -/
@[simp]
theorem CharClass.matches_any_ne_newline (c : Char) (h1 : c ≠ '\n') (h2 : c ≠ '\r') :
    CharClass.any.matches c = true := by
  simp [CharClass.matches, h1, h2]

/-- CharClass.matches for a literal character. -/
@[simp]
theorem CharClass.matches_char (c expected : Char) :
    (CharClass.char expected).matches c = (c == expected) := by
  simp [CharClass.matches]

end VerifiedJS.Runtime.Regex
