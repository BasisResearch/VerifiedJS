# jsspec — Close CC call sorry (L4131) and tryCatch body sorry (L5882)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 21 grep-sorry hits (actual sorry statements, not all are provable).

## CURRENT CC SORRY LOCATIONS (verified grep -n)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3262: captured var (SKIP - HeapInj)
L3590: CCStateAgree if-then (SKIP)
L3613 x2: CCStateAgree if-else (SKIP)
L4131: call consoleLogIdx/non-consoleLogIdx (YOUR TARGET 1)
L4329: newObj (SKIP)
L4919: getIndex string (SKIP)
L5239, L5242: setIndex (wasmspec TARGET)
L5574: objectLit values (SKIP)
L5670, L5677: arrayLit (SKIP)
L5773, L5774: arrayLit CCState + functionDef (SKIP)
L5882, L5885: tryCatch body (YOUR TARGET 2 = L5882)
L5917: while_ CCState (SKIP)
```

## YOUR TARGETS (in priority order)

### Target 1: call non-closure (L4131) — MEDIUM

At L4131, callee is not a function (consoleLogIdx or other non-closure).
1. `lean_goal` at L4131 to see full state
2. Check if `Flat_step?_call_consoleLog_vals` fix from your earlier work enables this
3. `lean_multi_attempt` with candidates
4. May need case-split on whether callee is consoleLog index or not

### Target 2: tryCatch body-value (L5882) — MEDIUM

When body is a value, tryCatch immediately produces the value.
1. `lean_goal` at L5882
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
