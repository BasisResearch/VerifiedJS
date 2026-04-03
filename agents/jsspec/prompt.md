# jsspec — newObj (L4486), then getIndex (L5076)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC ~12 actual sorries. You closed consoleLog AND arrayLit — EXCELLENT.

## ⚠️⚠️⚠️ ABSOLUTE BLOCKLIST — DO NOT TOUCH ⚠️⚠️⚠️
- L3709, L3732 if-then/else — BLOCKED CCStateAgree
- L6464 tryCatch finally — BLOCKED CCStateAgree
- L6535 tryCatch error — BLOCKED CCStateAgree (9/10 goals done, last = CCStateAgree)
- L6642 while_ — BLOCKED CCStateAgree
- L4288 non-consoleLog call — BLOCKED no FuncsCorr
- L6309 functionDef — NOT a leaf case! Multi-step + CCStateAgree blocker. DO NOT ATTEMPT.
- L3381 captured var — multi-step simulation gap
- L1507/L1508 forIn/forOf — stubs, unprovable

## YOUR TARGETS (in priority order):

### TARGET 1: newObj (LINE 4486)
```lean
| newObj f args => sorry
```
This is structurally similar to arrayLit which you already proved. Both allocate heap objects.

1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line number
2. `lean_goal` at the newObj sorry line
3. Read your arrayLit proof (~200 lines above) for the pattern
4. Split on whether `f` and `args` are all values:
   - All-values case: both Core and Flat allocate, prove correspondence. HeapInj via `alloc_both`.
   - Non-value case: find first non-value, step it, use IH
5. CCStateAgree: should be trivial for all-values case since convertExprList of lit elements doesn't change st

### TARGET 2: getIndex string (LINE 5076)
```lean
sorry -- getIndex string both-values: Flat/Core semantic mismatch
```
MAY be unprovable. Investigate first:
1. `lean_goal` at L5076
2. Check if Flat and Core agree on getIndex string semantics
3. If mismatch is real, add comment and MOVE ON to other targets

### IF BOTH DONE: Look at L3326 staging sorry
Line 3326 says "STAGING: proof temporarily sorry'd during HeapInj refactor".
Check if the HeapInj refactor is done and this can be restored from git history.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. Build proof
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
