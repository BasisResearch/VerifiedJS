# jsspec — FIX BUILD FIRST, then close actionable sorries. CC has 15 sorry tokens.

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

## STATE: CC has 15 real sorry tokens. BUILD MAY BE BROKEN.

## ⚠️ BUILD — CHECK AND FIX FIRST:

Run `lake build VerifiedJS.Proofs.ClosureConvertCorrect` to check build status. If broken:

### L4280 — consoleLog sorry
Type mismatch with `Core_step?_call_consoleLog_flat_msg`. Use `lean_goal` at L4280 to see what the goal expects. Fix the type mismatch or ensure sorry is clean so build passes.

### L6539 area — tryCatch
The tryCatch body-value area was decomposed (L6539 sorry inside tuple, L6540 sorry for finally case). If build errors cascade from here, fix the ROOT error first.

**The build MUST compile (possibly with sorries) before you work on anything else.**

## YOUR TASKS (strict priority after build fix):

### TASK 1: Close newObj non-value sorries (L4498, L4506)
Core.newObj where f or arg is not a value. Use `lean_goal` at each to understand proof obligation. These are semantic mismatches — Core allocates immediately, Flat steps f/arg first.

### TASK 2: Close captured var sorry at L3387
Multi-step gap: Core takes 1 step, Flat takes 2 steps for captured variable lookup.

### TASK 3: Close L4292 (non-consoleLog call)
Needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence (FuncsCorr).

## DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5144 getIndex string — UNPROVABLE
- L3715, L3738 — CCStateAgree blocked (if-true/false)
- L6382 — CCStateAgree blocked (functionDef)
- L6539, L6540 — CCStateAgree blocked (tryCatch)
- L6614 — CCStateAgree blocked (tryCatch catch)
- L6726 — CCStateAgree blocked (while_)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
