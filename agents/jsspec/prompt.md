# jsspec — newObj (L4492), then getIndex (L5082)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC ~13 actual sorries. You closed consoleLog AND arrayLit — EXCELLENT.

## ⚠️⚠️⚠️ ABSOLUTE BLOCKLIST — DO NOT TOUCH ⚠️⚠️⚠️
- L3715, L3738 if-then/else — BLOCKED CCStateAgree
- L6475 tryCatch finally — BLOCKED CCStateAgree
- L6546 tryCatch error — BLOCKED CCStateAgree
- L6653 while_ — BLOCKED CCStateAgree
- L4294 non-consoleLog call — BLOCKED no FuncsCorr
- L6320 functionDef — NOT a leaf case! Multi-step + CCStateAgree. DO NOT ATTEMPT.
- L3387 captured var — multi-step simulation gap
- L1507/L1508 forIn/forOf — stubs, unprovable

## YOUR TARGETS (in priority order):

### TARGET 1: newObj (LINE 4492)
```lean
| newObj f args => sorry
```
Structurally similar to the call case and arrayLit. Both involve constructor + args list.

1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line number
2. `lean_goal` at the newObj sorry line
3. Read the call proof above (~L4300-4491) and arrayLit proof for patterns
4. Pattern:
   - Check if `f` is a value (`Core.exprValue?`)
   - If yes, check if all `args` are values
   - All-values: both Core and Flat allocate new object, prove HeapInj via `alloc_both`
   - Non-value: find first non-value in `f :: args`, step it, use IH
5. CCStateAgree: trivial for all-values since convertExprList of literals doesn't change st
6. Key: `newObj` in Core allocates a heap object with constructor `f` and args. Check what Flat's `newObj` does — may map to Flat.Expr.newObj or similar.

### TARGET 2: getIndex string (LINE 5082)
```lean
sorry /- getIndex string both-values: UNPROVABLE.
```
Likely unprovable — investigate first:
1. `lean_goal` at L5082
2. If Flat and Core disagree on getIndex string semantics → add comment and SKIP

### IF BOTH DONE: Look at L3332 staging sorry
Line 3332 says "STAGING: proof temporarily sorry'd during HeapInj refactor".
Check if HeapInj refactor is done — look at git history for what was there before.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. Build proof
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
