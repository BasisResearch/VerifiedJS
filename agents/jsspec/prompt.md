# jsspec — Close CC tryCatch + arrayLit CCState sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 16 actual sorry statements. You closed tryCatch body-value none ✓. Great work!

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 04:05)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3320: HeapInj refactor (SKIP)
L3648: CCStateAgree if-then (SKIP - architecturally blocked)
L3671 x2: CCStateAgree if-else (SKIP - architecturally blocked)
L4189: call function (BLOCKED - needs FuncsCorr)
L4387: newObj (SKIP)
L4977: getIndex string semantic mismatch (SKIP)
L5967: objectLit sub-step (wasmspec TARGET — DO NOT TOUCH)
L5974: objectLit all-values (wasmspec TARGET — DO NOT TOUCH)
L6070: arrayLit sub-step (YOUR TARGET 1)
L6071: functionDef (SKIP)
L6197: tryCatch body-value with finally (YOUR TARGET 2)
L6200: tryCatch body non-value error (YOUR TARGET 3)
L6232: while_ CCState (SKIP - architecturally blocked)
```

## YOUR TARGETS (in priority order)

### Target 1: arrayLit CCState sub-step (L6070)
When an element needs stepping: show CCState agreement after the IH.
Pattern: IH gives `st_a, st_a', hconv', hAgreeIn, hAgreeOut`. Thread CCState through
`convertExprList` for done elements, then `convertExpr` for target, using
`convertExpr_state_determined` and the IH's `hAgreeOut`.

### Target 2: tryCatch body-value with finally (L6197)
You proved the `finally_ = none` case. Now handle `finally_ = some fin`.
The body is a value, so you need to show the tryCatch resolves with the finally block.
CCStateAgree may be blocked — if so, document and move to Target 3.

### Target 3: tryCatch body non-value error (L6200)
Body is not a value → it steps. Show stepping simulation via IH on the body sub-expression.

### COLLISION AVOIDANCE
wasmspec works on L5000-5989. You work on L6000-6280.
Do NOT edit L5967-5989 — that's wasmspec territory.

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
