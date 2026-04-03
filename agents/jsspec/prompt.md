# jsspec — consoleLog (L4270), then newObj (L4470), then getIndex (L5060)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 12 actual sorries. You closed arrayLit — GREAT WORK.

## ⚠️⚠️⚠️ ABSOLUTE BLOCKLIST — DO NOT TOUCH ⚠️⚠️⚠️
- L3709, L3732 if-then/else — BLOCKED CCStateAgree
- L6448 tryCatch finally — BLOCKED CCStateAgree
- L6519 tryCatch error — BLOCKED CCStateAgree (9/10 goals done, last = CCStateAgree)
- L6626 while_ — BLOCKED CCStateAgree
- L4272 non-consoleLog call — BLOCKED no FuncsCorr
- L6293 functionDef — NOT a leaf case! Multi-step + CCStateAgree blocker. DO NOT ATTEMPT.
- L3381 captured var — multi-step simulation gap
- L1507/L1508 forIn/forOf — stubs, unprovable

## YOUR TARGETS (in priority order):

### TARGET 1: consoleLog sub-goals (LINE 4270)
```lean
all_goals sorry -- consoleLog: Core.step + invariants need msg form alignment
```
This is inside the call case where function IS consoleLog. 10 sub-goals for the `refine`.

1. `lean_goal` at L4270 to see what goals remain
2. Try `all_goals (first | rfl | simp_all | assumption | omega)` — if some goals close, narrow down
3. Look at the objectLit/arrayLit proof pattern — same invariants (HeapInj, EnvCorr, etc.)
4. The first goal should be `Core.step? sc = some (.log msg, sc')` — prove by unfolding Core.step?

### TARGET 2: newObj (LINE 4470) — REASSIGNED FROM wasmspec (dead 18+ hours)
```lean
| newObj f args => sorry
```
This is structurally similar to arrayLit which you already proved. Both allocate heap objects.

1. `lean_goal` at L4470
2. Read your arrayLit proof (~100 lines above) for the pattern
3. Split on whether `f` and `args` are all values:
   - All-values case: both Core and Flat allocate, prove correspondence. HeapInj via `alloc_both`.
   - Non-value case: find first non-value, step it, use IH
4. CCStateAgree: should be trivial for all-values case since convertExprList of lit elements doesn't change st

### TARGET 3: getIndex string (LINE 5060)
```lean
sorry -- getIndex string both-values: Flat/Core semantic mismatch
```
MAY be unprovable. Investigate first:
1. `lean_goal` at L5060
2. Check if Flat and Core agree on getIndex string semantics
3. If mismatch is real, add comment and MOVE ON

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. Build proof
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
