# jsspec — consoleLog is CLOSED. Focus on newObj + captured var.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️⚠️⚠️ DO NOT TOUCH CCStateAgree ⚠️⚠️⚠️
The CCStateAgree-blocked sorries are PARKED. DO NOT WORK ON THEM.

## STATE: CC has 14 real sorry tokens. consoleLog (L4280) is DONE — good work!

## SORRY MAP (14 tokens):

### UNPROVABLE (3) — SKIP:
- L1507: forIn stub
- L1508: forOf stub
- L5144: getIndex string (Float.toString opaque)

### CCStateAgree BLOCKED (6) — PARKED:
- L3715: if-then
- L3738: if-else (2 sorries on one line)
- L6382: functionDef
- L6537: tryCatch finally
- L6608: tryCatch error
- L6715: while_

### ACTIONABLE (5):
- **L4498**: newObj f not a value ← TARGET #1
- **L4506**: newObj non-value arg ← TARGET #2
- **L3387**: captured var (multi-step gap) ← TARGET #3
- **L4292**: non-consoleLog call (needs FuncsCorr) ← TARGET #4 (stretch)

## YOUR TASKS (in priority order):

### TASK 1: Close newObj non-value sorries (L4498, L4506)

These are about Core.newObj where f or arg is not a value:
- Core allocates immediately (newObj evaluates args eagerly in Core semantics)
- Flat needs to step f/arg first before allocating

Use `lean_goal` at L4498 to see the exact goal. The pattern should be similar to what you did for arrayLit.

If these are fundamentally a semantic mismatch (Core vs Flat evaluation order), document WHY and mark as UNPROVABLE with a clear comment explaining the mismatch.

### TASK 2: Close captured var sorry at L3387

Use `lean_goal` at L3387 to understand the proof obligation. This is about a multi-step gap where a captured variable needs environment lookup correspondence.

### TASK 3: Build FuncsCorr for L4292

Only START if Tasks 1-2 are done. The call sorry at L4292 needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. This might need a new invariant `FuncsCorr` added to CC_SimRel.

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5144 getIndex string — UNPROVABLE
- L3715, L3738, L6382, L6537, L6608, L6715 — CCStateAgree blocked, PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
