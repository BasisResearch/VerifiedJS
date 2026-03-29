# proof — FIX BUILD (10 ERRORS), THEN CC OBJECTLIT

## STATUS: BUILD BROKEN. 10 errors in ClosureConvertCorrect.lean. FIX BEFORE ANYTHING ELSE.

## PRIORITY 0: FIX ALL BUILD ERRORS (DO THIS FIRST)

### Error 1 (ROOT CAUSE): L902 — doc comment before `mutual`

```
ClosureConvertCorrect.lean:902:65: error: unexpected token 'mutual'
```

**Fix**: Move the doc comment from before `mutual` to after it:

```lean
-- CURRENT (BROKEN — line 901-903):
/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
mutual
def ExprAddrWF : Core.Expr → Nat → Prop

-- FIXED:
mutual
/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
def ExprAddrWF : Core.Expr → Nat → Prop
```

### Error 2: L1885-1887 — Type mismatch / unsolved goals

Check the code around L1885. Likely from a recent edit. Fix the type mismatch.

### Errors 3-8: L3243-3278 — objectLit/arrayLit proof errors

```
L3243:15: unsolved goals
L3270:8: Missing cases
L3272:23: unsolved goals
L3273:15: Missing cases
L3274:23: Fields missing: `env`, `heap`, `trace`
L3278:98: unexpected identifier; expected '}'
```

These are in the arrayLit proof area. If you can't fix them quickly, sorry the broken cases to restore the build.

### VERIFICATION:
```
lake env lean VerifiedJS/Proofs/ClosureConvertCorrect.lean 2>&1 | grep error | head -20
```

Must show ZERO errors before proceeding to P1.

## PRIORITY 1: CC objectLit non-value case (L3247)

Same pattern as arrayLit. Only attempt AFTER build passes.

## PRIORITY 2: CC var captured case (L1981)

## DO NOT ATTEMPT: ANF sorries, Wasm sorries, CC value sub-cases (heap), newObj, functionDef, tryCatch, while_

## FILES: `VerifiedJS/Proofs/*.lean` (rw)
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
