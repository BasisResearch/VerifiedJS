# jsspec — BUILD IS BROKEN. Fix it. CC has 15 sorry tokens.

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

## STATE: CC has 15 real sorry tokens. BUILD IS BROKEN.

## ⚠️ BUILD ERRORS — FIX THESE FIRST:
```
L4280: exact sorry — type mismatch (consoleLog proof broke)
L6536-6678: tryCatch cascade errors (~9 errors)
```

## YOUR TASKS (strict priority order):

### TASK 0: FIX THE BUILD (MUST DO FIRST)

#### L4280 — consoleLog sorry
The previous consoleLog proof (closed at L4269 in earlier run) broke due to a type mismatch with `Core_step?_call_consoleLog_flat_msg`. Use `lean_goal` at L4280 to see what the goal expects. Options:
1. Fix the type mismatch if it's a simple argument reorder or `show` annotation
2. If unfixable quickly, ensure `sorry` is clean so the build unbreaks

#### L6536-6678 — tryCatch cascade
These are in the tryCatch body-not-value area. Check if the `.tryCatch` structure update syntax needs parentheses. The errors cascade — fix the ROOT error first (L6536) and the rest may resolve.

**The build MUST compile (possibly with sorries) before you work on anything else.**

### TASK 1: Close newObj non-value sorries (L4498, L4506)

After build is fixed. Core.newObj where f or arg is not a value. Use `lean_goal` at each to understand the proof obligation.

### TASK 2: Close captured var sorry at L3387

After build is fixed. Multi-step gap where captured variable needs env lookup correspondence.

### TASK 3: Close L4292 (non-consoleLog call)

Needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence (FuncsCorr).

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5144 getIndex string — UNPROVABLE
- L3715, L3738, L6382, L6539, L6540, L6611, L6718 — CCStateAgree blocked, PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
