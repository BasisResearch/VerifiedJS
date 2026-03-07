/-
  VerifiedJS — Full ECMAScript 2020 Abstract Syntax Tree
  SPEC: §11–15 (Expressions, Statements, Functions, Scripts, Modules)
-/

namespace VerifiedJS.Source

/-- ECMA-262 §12.1 Identifiers -/
abbrev Ident := String

/-- ECMA-262 §12.8 Unary Operators -/
inductive UnaryOp where
  | typeof | void | delete
  | neg | pos | bitNot | logNot
  | preInc | preDec | postInc | postDec
  deriving Repr, BEq, Hashable

/-- ECMA-262 §12.5–12.13 Binary Operators -/
inductive BinOp where
  | add | sub | mul | div | mod | exp
  | eq | neq | strictEq | strictNeq
  | lt | gt | le | ge
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  | logAnd | logOr | nullishCoalesce
  | instanceof | «in»
  deriving Repr, BEq, Hashable

/-- ECMA-262 §13.15.1 Assignment Operators -/
inductive AssignOp where
  | assign | addAssign | subAssign | mulAssign | divAssign | modAssign
  | expAssign | shlAssign | shrAssign | ushrAssign
  | bitAndAssign | bitOrAssign | bitXorAssign
  | logAndAssign | logOrAssign | nullishAssign
  deriving Repr, BEq, Hashable

inductive MethodKind where
  | method | get | set
  deriving Repr, BEq

inductive VarKind where
  | var | let_ | const_
  deriving Repr, BEq

/-- ECMA-262 §12.8.3–§12.8.5 Literals -/
inductive Literal where
  | null
  | bool (b : Bool)
  | number (n : Float)
  | string (s : String)
  | regex (pattern flags : String)
  | undefined
  deriving Repr, BEq

-- All mutually recursive AST types.
-- Lean 4 requires mutual blocks for cross-referencing inductive types.
mutual

inductive Expr where
  | lit (v : Literal)
  | ident (name : Ident)
  | this
  | array (elems : List (Option Expr))
  | object (props : List Property)
  | function (name : Option Ident) (params : List Pattern) (body : List Stmt)
  | arrowFunction (params : List Pattern) (body : ArrowBody)
  | «class» (name : Option Ident) (superClass : Option Expr) (body : List ClassMember)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinOp) (lhs rhs : Expr)
  | assign (op : AssignOp) (lhs : AssignTarget) (rhs : Expr)
  | conditional (cond thenE elseE : Expr)
  | call (callee : Expr) (args : List Expr)
  | «new» (callee : Expr) (args : List Expr)
  | member (obj : Expr) (prop : Ident)
  | index (obj : Expr) (prop : Expr)
  | optionalChain (expr : Expr) (chain : List ChainElem)
  | template (tag : Option Expr) (parts : List TemplatePart)
  | spread (arg : Expr)
  | yield (arg : Option Expr) (delegate : Bool)
  | await (arg : Expr)
  | sequence (exprs : List Expr)
  | metaProperty (metaName propName : Ident)

inductive Property where
  | keyValue (key : PropertyKey) (value : Expr)
  | shorthand (name : Ident)
  | method (kind : MethodKind) (key : PropertyKey) (params : List Pattern) (body : List Stmt)
  | spread (expr : Expr)

inductive PropertyKey where
  | ident (name : Ident)
  | string (s : String)
  | number (n : Float)
  | computed (expr : Expr)

inductive Pattern where
  | ident (name : Ident) (init : Option Expr)
  | array (elems : List (Option Pattern)) (rest : Option Pattern)
  | object (props : List PatternProp) (rest : Option Pattern)
  | assign (pat : Pattern) (init : Expr)

inductive PatternProp where
  | keyValue (key : PropertyKey) (value : Pattern)
  | shorthand (name : Ident) (init : Option Expr)

inductive Stmt where
  | expr (e : Expr)
  | block (stmts : List Stmt)
  | varDecl (kind : VarKind) (decls : List VarDeclarator)
  | «if» (cond : Expr) (then_ : Stmt) (else_ : Option Stmt)
  | while_ (cond : Expr) (body : Stmt)
  | doWhile (body : Stmt) (cond : Expr)
  | «for» (init : Option ForInit) (cond : Option Expr) (update : Option Expr) (body : Stmt)
  | forIn (kind : Option VarKind) (lhs : ForLHS) (rhs : Expr) (body : Stmt)
  | forOf (kind : Option VarKind) (lhs : ForLHS) (rhs : Expr) (body : Stmt)
  | «switch» (disc : Expr) (cases : List SwitchCase)
  | «try» (body : List Stmt) (catch_ : Option CatchClause) (finally_ : Option (List Stmt))
  | throw (arg : Expr)
  | «return» (arg : Option Expr)
  | «break» (label : Option Ident)
  | «continue» (label : Option Ident)
  | labeled (label : Ident) (body : Stmt)
  | with (obj : Expr) (body : Stmt)
  | debugger
  | empty
  | functionDecl (name : Ident) (params : List Pattern) (body : List Stmt)
    (isAsync : Bool) (isGenerator : Bool)
  | classDecl (name : Ident) (superClass : Option Expr) (body : List ClassMember)
  | import_ (specifiers : List ImportSpecifier) (source : String)
  | export_ (decl : ExportDecl)

inductive VarDeclarator where
  | mk (pat : Pattern) (init : Option Expr)

inductive ForInit where
  | varDecl (kind : VarKind) (decls : List VarDeclarator)
  | expr (e : Expr)

inductive ForLHS where
  | pattern (p : Pattern)
  | varDecl (kind : VarKind) (pat : Pattern)

inductive SwitchCase where
  | case_ (test : Expr) (body : List Stmt)
  | default_ (body : List Stmt)

inductive CatchClause where
  | mk (param : Option Pattern) (body : List Stmt)

inductive ClassMember where
  | method (isStatic : Bool) (kind : MethodKind) (key : PropertyKey)
    (params : List Pattern) (body : List Stmt) (isAsync : Bool) (isGenerator : Bool)
  | property (isStatic : Bool) (key : PropertyKey) (value : Option Expr)

inductive ArrowBody where
  | expr (e : Expr)
  | block (stmts : List Stmt)

inductive AssignTarget where
  | ident (name : Ident)
  | member (obj : Expr) (prop : Ident)
  | index (obj : Expr) (prop : Expr)
  | pattern (pat : Pattern)

inductive ChainElem where
  | member (prop : Ident)
  | index (prop : Expr)
  | call (args : List Expr)

inductive TemplatePart where
  | string (s : String)
  | expr (e : Expr)

inductive ImportSpecifier where
  | named (imported localName : Ident)
  | default_ (localName : Ident)
  | namespace (localName : Ident)

inductive ExportSpecifier where
  | mk (localName exported : Ident)

inductive ExportDecl where
  | named (specifiers : List ExportSpecifier) (source : Option String)
  | default_ (expr : Expr)
  | decl (stmt : Stmt)
  | all (source : String) (alias_ : Option Ident)

end

/-- Top-level program -/
inductive Program where
  | script (stmts : List Stmt)
  | module_ (stmts : List Stmt)

end VerifiedJS.Source
