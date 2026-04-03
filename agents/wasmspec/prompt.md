# wasmspec — Close arrayLit all-values (L6040), then objectLit sub-step output (L6033)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## YOU HAVE BEEN CRASHING OR IDLE FOR 2+ DAYS. PRODUCE OUTPUT THIS RUN.
If you see auth errors or exit code 1: log it and try the build command. If that fails, log the error and exit cleanly.

## STATE: CC 14 actual sorries.

## YOUR TARGET: arrayLit all-values (LINE 6040)

```lean
| none =>
  sorry -- all elements are values: heap allocation (same class as other value sub-cases)
```

Context: This is inside `arrayLit elems` at L6034. `Core.firstNonValueExpr elems = none` means ALL element expressions are values.

### How to prove it:
1. `lean_goal` at line 6040, column 6 of ClosureConvertCorrect.lean
2. Since all elems are values, `Core.step?` on `arrayLit elems` allocates an array on the heap
3. `Flat.step?` on the converted form does the same with converted values
4. Pattern to follow: look at the PROVED `objectLit` sub-step case nearby (lines 5946-6033) — it shows the pattern for heap allocation with converted values
5. Key steps:
   - Show `Flat.firstNonValueExpr (convertExprList elems ...) = none` (converted values are also values)
   - Look for existing helper: `convertExprList_firstNonValueExpr_none` or similar
   - Show both sides allocate: Core at `sc.heap.nextAddr`, Flat at `sf.heap.nextAddr`
   - Use HeapInj to bridge the new heap entries
6. Search: `lean_local_search "firstNonValueExpr_none"`, `lean_local_search "convertExprList"`, `lean_local_search "allValues"`

### If L6040 is blocked, try getIndex string (L5014):
```lean
sorry -- getIndex string both-values: Flat/Core semantic mismatch in .number else branch
```
Case split on whether index represents "length".

### COLLISION AVOIDANCE
You work on L5000-6053. jsspec works on L3000-5000 and L6100+.
Do NOT edit L6100+.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
