# jsspec — Close CC tryCatch sorries (L5949, L6122, L6125)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC ~17 sorry usages (down from 21 last run). Many are architecturally blocked.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 00:05)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3280: HeapInj refactor (SKIP)
L3608: CCStateAgree if-then (SKIP)
L3631 x2: CCStateAgree if-else (SKIP)
L4149: call function (BLOCKED - needs FuncsCorr invariant, NOT IN CODEBASE)
L4347: newObj (SKIP)
L4937: getIndex string semantic mismatch (SKIP)
L5750: objectLit all-values heap (SKIP)
L5846: objectLit CCState sub-step (YOUR TARGET 1)
L5853: arrayLit all-values heap (SKIP)
L5949: tryCatch (YOUR TARGET 2)
L5950: functionDef (SKIP)
L6122: tryCatch body non-value (YOUR TARGET 3)
L6125: CCState for tryCatch some-fin (YOUR TARGET 4)
L6157: while_ CCState (SKIP)
```

## YOUR TARGETS (in priority order)

### Target 1: objectLit CCState sub-step (L5846)
`lean_goal` at L5846. This is the CCState agreement bullet for objectLit when a prop needs stepping.
Pattern: Use IH on the non-value prop, thread CCState through convertExprList for done props then convertExpr for target.

### Target 2: tryCatch body stepping (L5949)
The tryCatch `some fin` case. `lean_goal` at L5949 to understand the proof obligation.
Previous work proved the non-error body-step case. This may be the error case or the `some fin` case.

### Target 3: tryCatch body non-value (L6122)
When body is not a value, step it via IH. Standard pattern: extract Flat sub-step, apply IH, reconstruct.

### Target 4: tryCatch CCState (L6125)
CCState agreement for the some-fin tryCatch case.

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
