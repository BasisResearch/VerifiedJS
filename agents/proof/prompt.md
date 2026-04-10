# proof — EXTEND ERROR PROPAGATION NOW (BUILD PASSES)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- **BUILD PASSES** — all your build fixes landed. Good work.
- ANF: 43 sorries. CC: 15. Lower: 0. **Total: 58** (down from 75).
- File is 16,240 lines. Fits in memory.

## P0: EXTEND ERROR PROPAGATION IN Flat/Semantics.lean — DO THIS NOW

This has been the #1 blocker for 3 runs. Build is fixed. No more excuses. DO IT.

Error propagation currently exists ONLY at L357 (.let), L373 (.assign), L401 (.seq). You need to add it to ALL 28 remaining compound stepping cases.

### THE EXACT PATTERN
Currently `.unary` at L414-417 reads:
```lean
match step? { s with expr := arg } with
| some (t, sa) =>
    let s' := pushTrace { s with expr := .unary op sa.expr, env := sa.env, heap := sa.heap } t
    some (t, s')
| none => none
```
Change to:
```lean
match step? { s with expr := arg } with
| some (t, sa) =>
    match t with
    | .error _ =>
        let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
        some (t, s')
    | _ =>
        let s' := pushTrace { s with expr := .unary op sa.expr, env := sa.env, heap := sa.heap } t
        some (t, s')
| none => none
```

### ALL 28 LOCATIONS TO CHANGE (exact current line numbers):
1. **L389** — `.if` cond stepping (pushTrace has `.«if» sc.expr then_ else_`)
2. **L415** — `.unary` arg stepping
3. **L423** — `.binary` lhs stepping
4. **L431** — `.binary` rhs stepping
5. **L447** — `.call` funcExpr stepping
6. **L456** — `.call` envExpr stepping
7. Find `.call` args stepping (firstNonValueExpr pattern)
8. Find `.newObj` funcExpr stepping
9. Find `.newObj` envExpr stepping
10. Find `.newObj` args stepping
11. Find `.getProp` obj stepping
12. Find `.setProp` obj stepping
13. Find `.setProp` value stepping
14. Find `.setProp` value (non-obj) stepping
15. Find `.getIndex` obj stepping
16. Find `.getIndex` idx stepping
17. Find `.getIndex` idx (string) stepping
18. Find `.getIndex` idx (other) stepping
19. Find `.setIndex` obj stepping
20. Find `.setIndex` idx stepping
21. Find `.setIndex` value stepping
22. Find `.setIndex` idx (non-obj) stepping
23. Find `.setIndex` value (non-obj) stepping
24. Find `.deleteProp` obj stepping
25. Find `.typeof` arg stepping
26. Find `.throw` arg stepping
27. Find `.makeClosure` envExpr stepping
28. Find `.getEnv` envExpr stepping
(Plus `.makeEnv`, `.objectLit`, `.arrayLit` firstNonValue stepping if they exist)

### APPROACH — DO ALL EDITS FIRST, THEN VERIFY
1. Search for all `pushTrace.*env :=.*heap :=` in Flat/Semantics.lean to find every compound stepping site
2. For each that doesn't already have `match t with | .error _ =>`, add it
3. After ALL edits, check Flat/Semantics.lean with LSP
4. Then fix cascading errors in ANFConvertCorrect.lean (sorry anything you can't fix in this run)

### IMPACT
This unblocks:
- ~9 compound throw/return/await/yield sorries in ANF
- ~3 error-case sorries in CC (jsspec's restructured hne callers)
- ~28 break/continue Cat B cases (wasmspec's territory)
- That's potentially -12 to -20 sorries in the NEXT round

## P1: FIX CASCADING ERRORS (after P0)

Adding error propagation will break proofs in ANFConvertCorrect.lean that unfold `Flat.step?`. For each broken proof:
1. If it's a `sorry` already → leave it
2. If it was working → add `hne` hypothesis or `match t with` split, or sorry it

## CONCURRENCY
- wasmspec works on break/continue at ~L15284, L15355 only
- jsspec works on ClosureConvertCorrect.lean only
- YOU own ALL of Flat/Semantics.lean and the rest of ANFConvertCorrect.lean

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — EXTENDING ERROR PROPAGATION" >> agents/proof/log.md`
2. Edit ALL 28+ locations in Flat/Semantics.lean
3. Verify Flat/Semantics.lean compiles with LSP
4. Fix cascading ANF errors (sorry what you can't fix)
5. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`

## NON-NEGOTIABLE: This MUST happen this run. Every run without it is wasted.
