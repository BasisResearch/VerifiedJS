# jsspec — ABORT CCStateAgree invariant change. Focus on closable targets.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️⚠️⚠️ ABORT CCStateAgree INVARIANT CHANGE ⚠️⚠️⚠️

Your OWN analysis from last run found:
> "The change would close 2-3 of the 6 blocked sorries but would BREAK 14 currently-working USES-OUTPUT cases"

**DO NOT attempt the invariant change.** The 6 CCStateAgree-blocked sorries (if-then, if-else, tryCatch×2, while_, functionDef) are PARKED. We will revisit when we have a better strategy.

## STATE: CC has 14 actual sorries. You closed consoleLog — EXCELLENT.

## YOUR TASKS (in priority order):

### TASK 1: newObj all-values case (L4498/L4506)

This is the same pattern as arrayLit (which you already proved). The `f not a value` sorry at L4498 and `non-value arg` sorry at L4506 deal with the sub-stepping cases where Core allocates immediately but Flat needs to step first.

For the ALL-VALUES sub-case within newObj (if it exists separately):
- Both Core and Flat allocate the object in one step
- HeapInj via `alloc_both`
- Same as your arrayLit proof

Read L4490-4510 to see what the actual proof state looks like. If there's a sub-case where both f and arg are values, that's your target.

### TASK 2: Investigate tryCatch error (L6608)

Read around L6600-6615. This sorry is in the tryCatch error handling case. Your previous analysis (run at 16:55) showed you proved 9/10 goals — only CCStateAgree remained. But check: is the CCStateAgree needed here truly blocked, or is there a way to provide it?

If tryCatch error creates a NEW scope (entering catch block), the CC state threading might be simpler — the catch block's CCState might agree with the input.

### TASK 3: Survey remaining non-blocked sorries

After Task 1, do `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` and categorize:
- Which sorries are genuinely CCStateAgree-blocked?
- Which might have alternative approaches?
- Are there any new opportunities you haven't explored?

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5144 getIndex string — UNPROVABLE (Float.toString opaque)
- L4292 non-consoleLog call — BLOCKED no FuncsCorr
- L3387 captured var — multi-step gap, needs closure env correspondence
- L3715, L3738, L6537, L6715 — CCStateAgree blocked, PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
