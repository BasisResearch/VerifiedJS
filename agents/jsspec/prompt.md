# jsspec — Close CC tryCatch sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 15 actual sorry statements.

## CURRENT CC SORRY LOCATIONS (verified 2026-04-03 grep -n)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3320: HeapInj refactor (SKIP)
L3648: CCStateAgree if-then (SKIP - architecturally blocked)
L3671 x2: CCStateAgree if-else (SKIP - architecturally blocked)
L4189: call function (BLOCKED - needs FuncsCorr)
L4387: newObj (SKIP)
L4977: getIndex string semantic mismatch (SKIP)
L5958: objectLit sub-step (wasmspec TARGET — DO NOT TOUCH)
L5965: objectLit all-values (wasmspec TARGET — DO NOT TOUCH)
L6099: functionDef (SKIP)
L6254: tryCatch body-value with finally (YOUR TARGET 1)
L6257: tryCatch body non-value (YOUR TARGET 2)
L6289: while_ CCState (SKIP - architecturally blocked)
```

## YOUR TARGETS (in priority order)

### Target 1: tryCatch body-value with finally (L6254)
The `finally_ = none` case is DONE (see L6240-6253). Now handle `| some fin =>`.
Body is a value, so tryCatch resolves → then execute the finally block.
- `lean_goal` at L6254 to see what's needed
- CCStateAgree may block you (same pattern as while_). If so, document clearly and move on.

### Target 2: tryCatch body non-value (L6257)
Body is NOT a value. Flat.step? steps the body sub-expression.
- `lean_goal` at L6257
- Apply the IH on the body sub-expression
- Thread CCState through (same pattern as objectLit sub-step, arrayLit sub-step)
- Need: `Flat.step?_tryCatch_step_body` or similar lemma for Flat tryCatch stepping

### Target 3: call function (L4189)
If previous targets are blocked, attempt this. Needs FuncsCorr invariant.
Check what infrastructure exists: `lean_local_search "FuncsCorr"`.

### COLLISION AVOIDANCE
wasmspec works on L5000-5989. You work on L6000-6400.
Do NOT edit L5955-5975 — that's wasmspec territory.

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
