# wasmspec — Close CC arrayLit all-values heap sorry

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 sorry lines. You closed objectLit all-values last run. EXCELLENT.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 02:05)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3346: HeapInj refactor (SKIP)
L3674, L3697 x2: CCStateAgree (SKIP)
L4215: call function (BLOCKED)
L4413: newObj (SKIP)
L5003: getIndex string (SKIP)
L5998: objectLit CCState sub-step (jsspec TARGET)
L6005: arrayLit all-values heap (YOUR TARGET 1)
L6101: arrayLit CCState sub-step (YOUR TARGET 2 — or jsspec's)
L6102: functionDef (SKIP)
L6229: tryCatch body (jsspec TARGET)
L6261: while_ CCState (SKIP)
```

## YOUR TARGETS

### Target 1: arrayLit all-values heap (L6005)
**This is the EXACT same pattern as objectLit all-values heap that you just proved!**

When all elements are values: Core allocates array on heap, Flat does matching allocation.

1. `lean_goal` at L6005
2. Your objectLit proof used:
   - `HeapInj_alloc_both` for the heap injection
   - `convertPropList_filterMap_eq` for prop list equivalence
   - Value list helpers from Core.firstNonValueProp/Expr
3. For arrayLit, you need:
   - The array analogue: `Core.firstNonValueExpr elems = none` means all elements are values
   - Heap allocation for array (similar to object but using `arrayLit` allocation)
   - Same `HeapInj_alloc_both` pattern
4. Look at the objectLit proof at L5830-5901 for the exact template.
   Copy the structure: Core step → trace → HeapInj → EnvCorrInj → ... → CCState.
5. The array case may use different helpers (`convertExprList` vs `convertPropList`).
   Search for `convertExprList_filterMap` or similar.

### Target 2: objectLit CCState sub-step (L5998) — BACKUP
If arrayLit is harder than expected, try the objectLit CCState sub-step.
Standard pattern: IH gives CCState agreement, thread through conversion structure.

### COLLISION AVOIDANCE
jsspec works on L5998-6270. You work on L5000-5999. Do NOT edit L6000+.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
