/-
  VerifiedJS — JavaScript Parser
  Recursive descent parser for ECMAScript 2020.
  Outside the verified TCB — validated by Test262 + differential testing.
-/

import VerifiedJS.Source.Lexer
import VerifiedJS.Source.AST

namespace VerifiedJS.Source

/-- Parser state -/
structure ParserState where
  tokens : Array Token
  pos : Nat
  deriving Repr

/-- Parser monad -/
abbrev Parser (α : Type) := ParserState → Except String (α × ParserState)

/-- Parse a JavaScript source string into a Program AST -/
def parse (source : String) : Except String Program :=
  sorry -- TODO: Implement recursive descent parser

/-- Parse a single expression (useful for testing) -/
def parseExpr (source : String) : Except String Expr :=
  sorry -- TODO: Implement

end VerifiedJS.Source
