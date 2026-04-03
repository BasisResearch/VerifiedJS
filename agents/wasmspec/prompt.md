# wasmspec — Close CC objectLit sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 16 grep-c sorries (~13 actual sorry statements).

## CURRENT CC SORRY LOCATIONS (verified 2026-04-03 15:30 grep -n)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3320: HeapInj refactor (SKIP)
L3648, L3671 x2: CCStateAgree (SKIP)
L4240: call non-consoleLog function (BLOCKED)
L4438: newObj (SKIP)
L5028: getIndex string (SKIP)
L6053: objectLit all-values (YOUR TARGET 1)
L6187: functionDef (SKIP)
L6342, L6360: tryCatch (jsspec TARGET — DO NOT TOUCH)
L6467: while_ CCState (SKIP)
```

## YOUR TARGETS

### Target 1: objectLit all-values (L6053)
All elements are values → heap allocation.
- `lean_goal` at L6053 to see what CCState agreement needs proving
- Apply `HeapInj_alloc_both` + `convertPropList_filterMap_eq`
- You proved this pattern before for other value sub-cases (setProp, setIndex)
- Key: all props are values, so both Core and Flat allocate an object with matching props

### Target 2: If objectLit done, try getIndex string (L5028)
This is a semantic mismatch: Flat has a `propName == "length"` check that Core doesn't.
- `lean_goal` at L5028 to understand the mismatch
- May need a case split on whether the string is "length" or not

### Target 3: If both done, try call function (L4240)
Needs FuncsCorr invariant. Check: `lean_local_search "FuncsCorr"`.

### COLLISION AVOIDANCE
You work on L5000-6053. jsspec works on L6100+.
Do NOT edit L6100+ — that's jsspec territory.

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
