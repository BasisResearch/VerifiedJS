# jsspec — newObj (L4469) is YOUR #1 TARGET

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC ~14 actual sorries. You closed arrayLit and fixed consoleLog — EXCELLENT.

## ⚠️⚠️⚠️ ABSOLUTE BLOCKLIST — DO NOT TOUCH ⚠️⚠️⚠️
- L3715, L3738 if-then/else — BLOCKED CCStateAgree
- L6452 tryCatch finally — BLOCKED CCStateAgree
- L6523 tryCatch error — BLOCKED CCStateAgree
- L6630 while_ — BLOCKED CCStateAgree
- L4271 non-consoleLog call — BLOCKED no FuncsCorr
- L6297 functionDef — NOT a leaf case! Multi-step + CCStateAgree. DO NOT ATTEMPT.
- L3387 captured var — multi-step simulation gap
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5059 getIndex string — UNPROVABLE (Float.toString opaque)

## YOUR TARGETS (in priority order):

### TARGET 1: newObj (CURRENT LINE ~4469)
```lean
| newObj f args => sorry
```
**This is your PRIMARY target. Do NOT skip it.**

Similar to arrayLit (which you already proved). Both involve constructor + args list.

1. `grep -n "newObj.*sorry" VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line
2. `lean_goal` at the sorry line
3. Read the arrayLit proof above it for patterns — you wrote it, reuse the same approach
4. Pattern:
   - Check if all args are values (`Core.exprValue?`)
   - All-values: both Core and Flat allocate new object, prove HeapInj via `alloc_both`
   - Non-value: find first non-value, step it, use IH
   - CCStateAgree: trivial for all-values since convertExprList of literals doesn't change st

### TARGET 2: consoleLog sorry (CURRENT LINE ~4269)
```lean
sorry -- consoleLog call: all infrastructure proven, blocked on dependent match normalization
```
wasmspec's prior run set up infrastructure (Core_step?_call_consoleLog_flat_msg). The type mismatch you found was about dependent match on hfvals. Try:
1. `lean_goal` at the sorry
2. Use `show` to normalize the goal type, avoiding dependent match patterns
3. Then `exact Core_step?_call_consoleLog_flat_msg ...`

### IF BOTH DONE: Look at L3332 staging sorry
Check git history for what was there before the HeapInj refactor.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. Build proof
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
