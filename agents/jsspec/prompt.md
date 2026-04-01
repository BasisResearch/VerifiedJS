# jsspec — Close CC tryCatch + objectLit/arrayLit CCState sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 17 actual sorry lines (20 grep-c, 3 are comments). Agents actively decomposing proofs.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 03:05)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3320: HeapInj refactor (SKIP)
L3648: CCStateAgree if-then (SKIP - architecturally blocked)
L3671 x2: CCStateAgree if-else (SKIP - architecturally blocked)
L4189: call function (BLOCKED - needs FuncsCorr)
L4387: newObj (SKIP)
L4977: getIndex string semantic mismatch (SKIP)
L5807: objectLit all-values (wasmspec TARGET — DO NOT TOUCH)
L5982: objectLit CCState sub-step (YOUR TARGET 1)
L5989: arrayLit all-values heap (wasmspec TARGET — DO NOT TOUCH)
L6085: arrayLit CCState sub-step (YOUR TARGET 2)
L6086: functionDef (SKIP)
L6213: tryCatch body-value no finally (YOUR TARGET 3 — you have DEBUG2 here)
L6243: tryCatch body-value with finally (YOUR TARGET 4)
L6246: tryCatch body non-value error (BLOCKED — CCState threading)
L6278: while_ CCState (SKIP - architecturally blocked)
```

## YOUR TARGETS (in priority order)

### Target 1: objectLit CCState sub-step (L5982)
When a prop needs stepping: show CCState agreement after the IH.
Pattern: IH gives `st_a, st_a', hconv', hAgreeIn, hAgreeOut`. Thread CCState through
`convertPropList` for done props, then `convertExpr` for target, using
`convertExpr_state_determined` and the IH's `hAgreeOut`.

### Target 2: arrayLit CCState sub-step (L6085)
Same pattern as Target 1 but for arrayLit.

### Target 3: tryCatch body-value no-finally (L6213)
You have DEBUG2 here. Finish this proof.

### Target 4: tryCatch body-value with-finally (L6243)
Similar structure to Target 3.

### COLLISION AVOIDANCE
wasmspec works on L5000-5989. You work on L5982-6280.
Overlap at L5982-5989 — if wasmspec is editing there, skip to Target 3.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
