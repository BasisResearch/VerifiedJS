# proof — FIX BUILD FIRST (1 LINE), THEN CLOSE ARRAYLIT SORRIES

## ABSOLUTE PRIORITY 0: FIX L902 BUILD ERROR (DO THIS BEFORE ANYTHING ELSE)

**THIS HAS BEEN BROKEN FOR 2+ RUNS. FIX IT NOW.**

The build fails because a doc comment precedes `mutual` on L901-903. In Lean 4.29, doc comments CANNOT precede `mutual` blocks.

**Exact fix** — swap lines 901-903 from:
```lean
/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
mutual
def ExprAddrWF : Core.Expr → Nat → Prop
```
To:
```lean
mutual
/-- All object addresses in a Core expression are valid heap addresses.
    Fully recursive to propagate through compound expressions. -/
def ExprAddrWF : Core.Expr → Nat → Prop
```

After fixing, verify:
```
lake env lean VerifiedJS/Proofs/ClosureConvertCorrect.lean 2>&1 | grep "error" | head -5
```
Must show ZERO errors. If any remain, sorry broken code to restore build.

## PRIORITY 1: Close arrayLit sorries (3 tractable, 1 hard)

The arrayLit non-value case (L3237-3324) has great proof structure but 4 remaining sorries:

### L3269 — Flat sub-step extraction (MOST TRACTABLE)
Need: `Flat.step? {sf with expr = .arrayLit flatElems} = some (ev, sa)` when `firstNonValueExpr` finds a non-value element.
Strategy: Unfold `Flat.step?` for `.arrayLit`. It checks `valuesFromExprList?`. Since `firstNonValueExpr` returns `some`, `valuesFromExprList?` returns `none` (use `valuesFromExprList_none_of_firstNonValueExpr` at L1872). Then it calls `firstNonValueExpr` on the flat list (use `convertExprList_firstNonValueExpr_some` at L1851). Then it steps the target sub-expression. The result state has the stepped element in place.

```lean
-- Try this approach:
simp [Flat.step?]
rw [valuesFromExprList_none_of_firstNonValueExpr hffnv]
simp [hffnv]
exact ⟨_, hstep, rfl⟩  -- or similar
```

### L3277 — ExprAddrWF propagation
Need: `ExprAddrWF target_c sc.heap.objects.size` from `ExprAddrWF (.arrayLit elems) sc.heap.objects.size`.
Strategy: `ExprAddrWF (.arrayLit elems) n = True` by definition (check the mutual def). So this is just `trivial` or `simp [ExprAddrWF]`.

Actually check: does `ExprAddrWF` have a case for `.arrayLit`? Look at the mutual def starting L904. If `.arrayLit` maps to `True`, then `hexprwf` gives `True` which says nothing about elements. You may need to strengthen the invariant or use `sorry` and move on.

### L3324 — CCState threading
Need: CCState agreement after convertExprList over concatenated `done ++ [stepped] ++ rest`.
This is the hardest one. If you can't close it in < 30 min, leave it sorry'd and move to objectLit.

### L3243 — all-values case (heap reasoning)
Same class as other value sub-cases (L2812, L2870, etc.). Skip for now.

## PRIORITY 2: CC objectLit (L3236)

Copy the arrayLit pattern. Structure:
1. `rw [hsc] at hconv hncfr hexprwf hd; simp [Flat.convertExpr] at hconv`
2. Case split on `Core.firstNonValueProp` (analogous to `firstNonValueExpr`)
3. Value case: sorry (heap reasoning)
4. Non-value case: use IH on target property expression

## DO NOT ATTEMPT: ANF sorries, Wasm sorries, newObj, functionDef, tryCatch, while_
## FILES: `VerifiedJS/Proofs/*.lean` (rw)
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
