# jsspec — Close CC tryCatch + objectLit CCState sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 19 sorry lines (down from 21 last run — wasmspec closed 2 setIndex).

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 01:05)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3280: HeapInj refactor (SKIP)
L3608: CCStateAgree if-then (SKIP)
L3631 x2: CCStateAgree if-else (SKIP)
L4149: call function (BLOCKED - needs FuncsCorr)
L4347: newObj (SKIP)
L4937: getIndex string semantic mismatch (SKIP)
L5750: objectLit all-values heap (wasmspec TARGET)
L5846: objectLit CCState sub-step (YOUR TARGET 1)
L5853: arrayLit all-values heap (wasmspec TARGET)
L5949: tryCatch some-fin (YOUR TARGET 2)
L5950: functionDef (SKIP)
L6129: tryCatch body non-value (YOUR TARGET 3)
L6132: CCState for tryCatch (YOUR TARGET 4)
L6164: while_ CCState (SKIP)
```

## YOUR TARGETS (in priority order)

### Target 1: objectLit CCState sub-step (L5846)
When a prop needs stepping: show CCState agreement after convertExpr on the stepped prop.
1. `lean_goal` at L5846
2. Pattern: IH on the non-value prop, thread CCState through convertExprList for done props then convertExpr for target
3. Key: `convertExpr_state_determined` for the literal props, IH for stepping prop

### Target 2: tryCatch some-fin (L5949)
The tryCatch case when finally is `some fin`.
1. `lean_goal` at L5949
2. This is the body-stepping case when a finally block exists
3. May need to decompose the Flat tryCatch step into body sub-step + reconstruct

### Target 3: tryCatch body non-value (L6129)
When body is not a value, step it via IH.
1. `lean_goal` at L6129
2. Standard: extract Flat sub-step, apply IH, reconstruct

### Target 4: tryCatch CCState (L6132)
CCState agreement for the tryCatch case.
1. `lean_goal` at L6132

### COLLISION AVOIDANCE
wasmspec works on L5000-5800. You work on L5800-6200. Do NOT edit overlapping regions.

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
