# jsspec — Close CC tryCatch and error-case sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 16 grep-c sorries (~13 actual sorry statements).

## CURRENT CC SORRY LOCATIONS (verified 2026-04-03 15:30 grep -n)
```
L1507: forIn stub (SKIP - theorem vacuously false)
L1508: forOf stub (SKIP - theorem vacuously false)
L3320: HeapInj refactor (SKIP)
L3648: CCStateAgree if-then (SKIP - architecturally blocked)
L3671 x2: CCStateAgree if-else (SKIP - architecturally blocked)
L4240: call non-consoleLog function (BLOCKED - needs FuncsCorr)
L4438: newObj (SKIP)
L5028: getIndex string mismatch (SKIP)
L6053: objectLit all-values (wasmspec TARGET — DO NOT TOUCH)
L6187: functionDef (SKIP)
L6342: tryCatch body-value with finally (YOUR TARGET 1)
L6360: tryCatch error case scope mismatch (YOUR TARGET 2)
L6467: while_ CCState (SKIP - architecturally blocked)
```

## YOUR TARGETS (in priority order)

### Target 1: tryCatch body-value with finally (L6342)
The `finally_ = none` case is DONE. Now handle `| some fin =>`.
Body is a value, so tryCatch resolves → then execute the finally block.
- `lean_goal` at L6342 to see what's needed
- CCStateAgree may block you (same pattern as while_). If so, document clearly and move on.

### Target 2: tryCatch error case (L6360)
Body is NOT a value — error case with scope mismatch (catchBody converted with catchParam :: scope).
- `lean_goal` at L6360
- The scope mismatch means the converted catchBody uses `catchParam :: scope` but the main
  expression uses `scope`. May need a scope-extension lemma.

### Target 3: call non-consoleLog function (L4240)
If previous targets are blocked, attempt this. Needs FuncsCorr invariant.
Check what infrastructure exists: `lean_local_search "FuncsCorr"`.

### COLLISION AVOIDANCE
wasmspec works on L5000-6053. You work on L6100+.
Do NOT edit L5000-6053 — that's wasmspec territory.

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
