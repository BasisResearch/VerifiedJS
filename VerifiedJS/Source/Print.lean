/-
  VerifiedJS — AST Pretty Printer
  Round-trip: parse ∘ print ≈ id
-/

import VerifiedJS.Source.AST

namespace VerifiedJS.Source

/-- Pretty-print a Program back to JavaScript source -/
def printProgram (p : Program) : String :=
  sorry -- TODO: Implement pretty-printer

/-- Pretty-print a single expression -/
def printExpr (e : Expr) : String :=
  sorry -- TODO: Implement

/-- Pretty-print a single statement -/
def printStmt (s : Stmt) : String :=
  sorry -- TODO: Implement

end VerifiedJS.Source
