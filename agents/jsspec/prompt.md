# jsspec — Close CC L4140 (call) and L5891 (tryCatch body-value)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 21 grep-sorry hits. You closed 1 sorry last run. Good work.

## CURRENT CC SORRY LOCATIONS (as of 22:05)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3271: captured var (SKIP - HeapInj)
L3599: CCStateAgree if-then (SKIP)
L3622 x2: CCStateAgree if-else (SKIP)
L4140: call consoleLogIdx/non-consoleLogIdx (YOUR TARGET 1)
L4338: newObj (SKIP)
L4928: getIndex string (SKIP)
L5248, L5251: setIndex (wasmspec TARGET)
L5583: objectLit values (SKIP)
L5679, L5686: arrayLit (SKIP)
L5782, L5783: arrayLit CCState + functionDef (SKIP)
L5891, L5894: tryCatch body (YOUR TARGET 2 = L5891)
L5926: while_ CCState (SKIP)
```

## YOUR TARGETS (in priority order)

### Target 1: call non-closure (L4140) — MEDIUM

At L4140, the consoleLogIdx + non-consoleLogIdx case. Callee is not a function.
1. `lean_goal` at L4140 to see full state
2. Check if `Flat_step?_call_consoleLog_vals` fix you did last run enables this
3. `lean_multi_attempt` with candidates
4. May need to case-split on whether callee is consoleLog index or not

### Target 2: tryCatch body-value (L5891) — MEDIUM

When body is a value, tryCatch immediately produces the value.
1. `lean_goal` at L5891
2. `hbv : Core.exprValue? body = some v` — prove body = .lit v
3. Both Core and Flat step tryCatch of literal directly
4. `lean_multi_attempt` with candidates

### COLLISION AVOIDANCE
wasmspec works on L5000-5650. You work on L4100-4200 and L5800-5950. Do NOT edit the same regions.

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
