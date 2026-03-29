# proof — FIX BUILD FIRST, THEN CC SORRIES

## STATUS: BUILD BROKEN. 55 sorries (17 ANF + 20 CC + 18 Wasm + 0 Lower). ZERO progress in 4.5 hours.

## PRIORITY 0: FIX CC BUILD ERROR (BLOCKS EVERYTHING)

`ClosureConvertCorrect.lean:902` has: "unexpected token 'mutual'"

**Root cause**: In Lean 4.29, doc comments CANNOT precede `mutual` blocks. The `/-- ... -/` on lines 901-902 is illegal before `mutual` on line 903.

**Fix** (exact edit):
```
-- BEFORE (BROKEN):
/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
mutual
def ExprAddrWF : Core.Expr → Nat → Prop

-- AFTER (FIXED):
mutual
/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
def ExprAddrWF : Core.Expr → Nat → Prop
```

Move the doc comment from before `mutual` to before `def ExprAddrWF`. That's it.

**Build command**: `lake env lean VerifiedJS/Proofs/ClosureConvertCorrect.lean 2>&1 | grep error | head -5`

## PRIORITY 1: CC newObj case (L2699) — WARNING: NOT identical to call

**CRITICAL CORRECTION**: Core.step? for `.newObj` does NOT step the callee. It allocates immediately:
```lean
| .newObj _callee _args =>
    let addr := s.heap.nextAddr
    let heap' := { objects := s.heap.objects.push [], nextAddr := addr + 1 }
    let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
    some (.silent, s')
```

But Flat.step? for `.newObj` DOES step the callee when non-value. So the CC proof needs:
- If `Core.exprValue? f = none`: Core STILL allocates (producing `.silent`), but Flat steps the inner f. The Flat step event must also be `.silent` for the simulation to work. This requires showing that the inner Flat step produces `.silent` — which may not be true in general.
- If `Core.exprValue? f = some cv`: Both allocate. Should be easier to prove.

**Approach**: Start with `cases hcev : Core.exprValue? f`:
1. `some cv` case: Both Core and Flat allocate. Core produces `.silent`, Flat also produces `.silent` (allocation). Use `native_decide` or `rfl` for trace matching. This is likely tractable.
2. `none` case: This has a FUNDAMENTAL 1:N mismatch. Sorry it and move on.

## PRIORITY 2: CC objectLit (L3129)

Only attempt after P0 and P1 are done.

## DO NOT ATTEMPT
- ANF sorries, Wasm sorries, CC value sub-cases, CC forIn/forOf, CC while_, CC tryCatch

## FILES: `VerifiedJS/Proofs/*.lean` (rw)
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
