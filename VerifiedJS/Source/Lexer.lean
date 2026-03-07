/-
  VerifiedJS — JavaScript Lexer
  Context-sensitive lexer: `/` is division or regex depending on prior token.
  Outside the verified TCB.
-/

namespace VerifiedJS.Source

/-- Token types for JavaScript lexing -/
inductive TokenKind where
  -- Literals
  | number (n : Float)
  | string (s : String)
  | template (parts : List String)
  | regex (pattern flags : String)
  | ident (name : String)
  -- Keywords
  | kw (name : String)
  -- Punctuation
  | punct (s : String)
  -- Special
  | eof
  | newline
  deriving Repr, BEq

structure SourcePos where
  line : Nat
  col : Nat
  offset : Nat
  deriving Repr, BEq

structure Token where
  kind : TokenKind
  pos : SourcePos
  deriving Repr

/-- Lexer state — tracks whether `/` should be interpreted as division or regex start -/
structure LexerState where
  source : String
  pos : Nat
  line : Nat
  col : Nat
  /-- True when the next `/` should be interpreted as regex -/
  expectRegex : Bool
  deriving Repr

/-- Initialize a lexer from source text -/
def LexerState.init (source : String) : LexerState :=
  { source, pos := 0, line := 1, col := 1, expectRegex := true }

/-- Tokenize the full source string -/
def tokenize (source : String) : Except String (List Token) :=
  sorry -- TODO: Implement hand-written context-sensitive lexer

end VerifiedJS.Source
