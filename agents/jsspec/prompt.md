# jsspec — BUILD IS BROKEN. Fix L4280 type mismatch FIRST, then tryCatch errors.

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

## STATE: CC has 14 real sorry tokens. BUILD IS BROKEN with 10 errors.

## ⚠️ BUILD ERRORS (10 errors, must fix):
```
L4280: error: Type mismatch (consoleLog proof)
L6536: error: Application type mismatch
L6544: error: unsolved goals
L6556: error: `simp` made no progress
L6564: error: unsolved goals
L6615: error: `simp` made no progress
L6623: error: unsolved goals
L6647: error: Type mismatch
L6650: error: Application type mismatch
L6678: error: Tactic `rewrite` failed
```

## YOUR TASKS (in strict priority order):

### TASK 0: FIX THE BUILD (MUST DO FIRST)

#### L4280 — consoleLog type mismatch
`exact Core_step?_call_consoleLog_flat_msg args argVals sc.env sc.heap sc.trace sc.funcs sc.callStack hallv` doesn't typecheck. Use `lean_goal` at L4280 to see what the goal expects vs what the lemma provides. Fix the type mismatch — likely needs a `show` annotation or argument reordering.

If you cannot fix it, replace with `sorry` temporarily so the build unbreaks and other proofs can be verified.

#### L6536-6678 — tryCatch area errors
These are in the tryCatch body-not-value case (L6538+). The errors cascade. Check if they're caused by a signature change or a prior edit that broke the proof structure. Use `lean_goal` at each error site.

**The build MUST compile (possibly with sorries) before you work on anything else.**

### TASK 1: Close newObj non-value sorries (L4498, L4506)

Only after build is fixed. These are about Core.newObj where f or arg is not a value. Use `lean_goal` to understand the proof obligation.

### TASK 2: Close captured var sorry at L3387

Only after build is fixed. Multi-step gap where captured variable needs environment lookup correspondence.

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5144 getIndex string — UNPROVABLE
- L3715, L3738, L6382, L6537, L6608, L6715 — CCStateAgree blocked, PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
