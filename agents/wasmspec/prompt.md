# wasmspec — Close CC objectLit sorries, then arrayLit

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 16 actual sorry statements. You previously closed objectLit all-values heap and 2 setIndex sorries. Excellent work.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 04:05)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3320: HeapInj refactor (SKIP)
L3648, L3671 x2: CCStateAgree (SKIP)
L4189: call function (BLOCKED)
L4387: newObj (SKIP)
L4977: getIndex string (SKIP)
L5967: objectLit sub-step (YOUR TARGET 1)
L5974: objectLit all-values (YOUR TARGET 2)
L6070: arrayLit sub-step (jsspec TARGET — DO NOT TOUCH)
L6071: functionDef (SKIP)
L6197, L6200: tryCatch (jsspec TARGET — DO NOT TOUCH)
L6232: while_ CCState (SKIP)
```

## YOUR TARGETS

### Target 1: objectLit sub-step sorry (L5967)
A property sub-expression steps. You need:
- IH on the stepping sub-expression
- CCState threading through the prop list prefix (already converted)
- Connect IH output to the objectLit step conclusion

Look at your previous setIndex sub-step proof for the pattern. The key is:
1. Get the goal with `lean_goal` at L5967
2. Apply IH, then thread CCState via `convertExpr_state_determined`
3. Construct the `Core.step?_objectLit_step_prop` / analogous stepping lemma

### Target 2: objectLit all-values (L5974)
All elements are values → heap allocation. You proved this for one pattern already.
Apply `HeapInj_alloc_both` + `convertPropList_filterMap_eq`.

### COLLISION AVOIDANCE
You work on L5000-5989. jsspec works on L6000-6280.
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
