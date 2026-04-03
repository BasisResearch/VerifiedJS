# jsspec — consoleLog sub-goals (L4270) then getIndex (L5072)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 actual sorries (you closed arrayLit last run — GREAT WORK).

## ⚠️⚠️⚠️ ABSOLUTE BLOCKLIST — DO NOT TOUCH ⚠️⚠️⚠️
- L3709, L3732 if-then/else — BLOCKED CCStateAgree
- L6460 tryCatch finally — BLOCKED CCStateAgree
- L6531 tryCatch error — BLOCKED CCStateAgree (9/10 goals done, last = CCStateAgree)
- L6638 while_ — BLOCKED CCStateAgree
- L4284 non-consoleLog call — BLOCKED no FuncsCorr
- L6305 functionDef — NOT a leaf case! Multi-step + CCStateAgree blocker. DO NOT ATTEMPT.
- L4482 newObj — wasmspec owns this
- L3381 captured var — multi-step simulation gap, wasmspec owns this
- L1507/L1508 forIn/forOf — stubs, unprovable

## YOUR TARGETS (in priority order):

### TARGET 1: consoleLog sub-goals (LINE 4270)
```lean
· sorry -- Core.step?: type mismatch with let msg form
```
This is inside the call case where the function IS consoleLog. Should be straightforward invariant goals (trace, EnvCorr, HeapInj, etc.) following the same patterns you used for arrayLit.

1. `lean_goal` at L4270 to see what goals remain
2. Try `all_goals (first | rfl | simp_all | assumption | omega)` — if some goals close, narrow down to the hard ones
3. Look at the arrayLit proof you just wrote for patterns

### TARGET 2: getIndex string (LINE 5072)
```lean
sorry -- getIndex string both-values: Flat/Core semantic mismatch in .number else branch
```
The comment says there's a semantic mismatch — Flat checks `propName == "length"` but Core doesn't. This MAY be unprovable.
1. `lean_goal` at L5072
2. Read Flat.step? and Core.step? for getIndex
3. If mismatch is real, add a comment and MOVE ON — don't waste time

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. Build proof
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
