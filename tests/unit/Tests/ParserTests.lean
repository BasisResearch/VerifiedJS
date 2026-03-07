import VerifiedJS.Source.Parser

namespace Tests

open VerifiedJS.Source

def isMulPrecedence : Expr → Bool
  | .binary .add (.lit (.number _)) (.binary .mul (.lit (.number _)) (.lit (.number _))) => true
  | _ => false

def isAssignAdd : Expr → Bool
  | .assign .assign (.ident "a") (.binary .add (.ident "b") (.ident "c")) => true
  | _ => false

def isMemberCallIndex : Expr → Bool
  | .index (.call (.member (.ident "obj") "prop") [.lit (.number _), .ident "x"]) (.ident "y") => true
  | _ => false

def isLetConstReturn : Program → Bool
  | .script
      [ .varDecl .let_ [.mk (.ident "x" none) (some (.binary .add (.lit (.number _)) (.lit (.number _))))]
      , .varDecl .const_ [.mk (.ident "y" none) (some (.ident "x"))]
      , .return (some (.ident "y"))
      ] => true
  | _ => false

def isBlockWithAssign : Program → Bool
  | .script
      [ .block
        [ .varDecl .let_ [.mk (.ident "x" none) (some (.lit (.number _)))]
        , .expr (.assign .assign (.ident "x") (.binary .add (.ident "x") (.lit (.number _))))
        ]
      ] => true
  | _ => false

#guard
  match parseExpr "1 + 2 * 3" with
  | .ok e => isMulPrecedence e
  | .error _ => false

#guard
  match parseExpr "a = b + c" with
  | .ok e => isAssignAdd e
  | .error _ => false

#guard
  match parseExpr "obj.prop(1, x)[y]" with
  | .ok e => isMemberCallIndex e
  | .error _ => false

#guard
  match parse "let x = 1 + 2; const y = x; return y" with
  | .ok p => isLetConstReturn p
  | .error _ => false

#guard
  match parse "{ let x = 1; x = x + 1; }" with
  | .ok p => isBlockWithAssign p
  | .error _ => false

end Tests
