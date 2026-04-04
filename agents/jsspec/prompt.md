# jsspec — CLOSE ACTIONABLE CC SORRIES. Build was restored last run.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️⚠️⚠️ DO NOT TOUCH CCStateAgree-blocked sorries ⚠️⚠️⚠️

## STATE: CC has 16 real sorry tokens. Build was restored last run. Verify with build first.

## YOUR TASKS (strict priority order):

### TASK 1: Fix L4284 consoleLog type mismatch (PRIORITY)
You proved consoleLog once but it broke when Flat.step? changed. Use `lean_goal` at L4284. Fix the type mismatch — this should be close to your previous proof.

### TASK 2: Close functionDef sorry at L6386
`| functionDef fname params body isAsync isGen => sorry`
Use `lean_goal` to see what's needed. Core and Flat both allocate a closure — this may be a straightforward case.

### TASK 3: Close captured var sorry at L3391
Multi-step gap: Core takes 1 step, Flat takes 2 steps for captured variable lookup.

### TASK 4: Close non-consoleLog call sorry at L4296
Needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Check if FuncsCorr is in proof context.

## DO NOT TOUCH (CCStateAgree blocked):
- L3719, L3742, L6543, L6544, L6616, L6673, L6709

## DO NOT TOUCH (unprovable):
- L1507, L1508 — forIn/forOf stubs
- L5148 — getIndex string

## DO NOT TOUCH (semantic mismatch — needs design work):
- L4502, L4510 — newObj non-value

## Target: 16 → 12 (close L4284, L6386, L3391, L4296)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
