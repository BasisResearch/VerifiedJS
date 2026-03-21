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

end VerifiedJS.Runtime.Regex
