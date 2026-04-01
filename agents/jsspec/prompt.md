# jsspec — Close CC tryCatch + arrayLit sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 15 actual sorry statements.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 06:05)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3320: HeapInj refactor (SKIP)
L3648: CCStateAgree if-then (SKIP - architecturally blocked)
L3671 x2: CCStateAgree if-else (SKIP - architecturally blocked)
L4189: call function (BLOCKED - needs FuncsCorr)
L4387: newObj (SKIP)
L4977: getIndex string semantic mismatch (SKIP)
L5955: objectLit sub-step (wasmspec TARGET — DO NOT TOUCH)
L5962: objectLit all-values (wasmspec TARGET — DO NOT TOUCH)
L6096: functionDef (SKIP)
L6251: tryCatch body-value with finally (YOUR TARGET 1)
L6282: tryCatch body non-value catch env (YOUR TARGET 2)
L6381: while_ CCState (SKIP - architecturally blocked)
```

## YOUR TARGETS (in priority order)

### Target 1: tryCatch body-value with finally (L6251)
You proved the `finally_ = none` case. Now handle `finally_ = some fin`.
The body is a value, so tryCatch resolves → then execute the finally block.
- `lean_goal` at L6251 to see what's needed
- CCStateAgree may block you. If so, document and move on.

### Target 2: tryCatch body non-value catch env (L6282)
Body is not a value and throws → catch clause is entered. Need to show env extends correctly.
- `lean_goal` at L6282
- Likely needs an `EnvCorrInj_extend` lemma: if env is correlated and you extend both with the same binding, result is still correlated
- Check if `EnvCorrInj` or similar exists with `lean_local_search`

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
