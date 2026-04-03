# wasmspec — Close CC objectLit sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 15 actual sorry statements.

## CURRENT CC SORRY LOCATIONS (verified 2026-04-03 grep -n)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3320: HeapInj refactor (SKIP)
L3648, L3671 x2: CCStateAgree (SKIP)
L4189: call function (BLOCKED)
L4387: newObj (SKIP)
L4977: getIndex string (SKIP)
L5958: objectLit sub-step (YOUR TARGET 1)
L5965: objectLit all-values (YOUR TARGET 2)
L6099: functionDef (SKIP)
L6254, L6257: tryCatch (jsspec TARGET — DO NOT TOUCH)
L6289: while_ CCState (SKIP)
```

## YOUR TARGETS

### Target 1: objectLit sub-step sorry (L5958)
A property sub-expression steps. You need:
- `lean_goal` at L5958 to see what CCState agreement needs proving
- This is the CCStateAgree sub-goal for the objectLit case where a property sub-expr steps
- Pattern: the IH gives you CCStateAgree for the sub-expression stepping; you need to lift it to the full objectLit context
- Try: `exact ih_ccstate_agree` or reconstruct from IH output + `CCStateAgree_trans`

### Target 2: objectLit all-values (L5965)
All elements are values → heap allocation.
- `lean_goal` at L5965
- Apply `HeapInj_alloc_both` + `convertPropList_filterMap_eq`
- You proved this pattern before for other value cases

### IF BOTH DONE: Help jsspec
If you close both objectLit sorries, move to the call function sorry at L4189.
Search for `FuncsCorr` infrastructure first: `lean_local_search "FuncsCorr"`.

### COLLISION AVOIDANCE
You work on L5000-5989. jsspec works on L6000-6400.
Do NOT edit L6000+ — that's jsspec territory.

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
