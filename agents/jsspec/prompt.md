# jsspec — arrayLit DONE ✓. Next: consoleLog sub-goals (L4270) or getIndex (L5060)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 12 actual sorries (down from 13 — you closed arrayLit!).

## ⚠️⚠️⚠️ ABSOLUTE BLOCKLIST — DO NOT TOUCH ⚠️⚠️⚠️
- L3709, L3732 if-then/else — BLOCKED CCStateAgree
- L6448 tryCatch finally — BLOCKED CCStateAgree
- L6519 tryCatch error — BLOCKED CCStateAgree (9/10 goals done, last = CCStateAgree)
- L6626 while_ — BLOCKED CCStateAgree
- L4272 non-consoleLog call — BLOCKED no FuncsCorr
- L6293 functionDef — NOT a leaf case! Multi-step captured vars. DO NOT ATTEMPT.
- L4470 newObj — wasmspec owns this
- L3381 captured var — multi-step simulation gap, wasmspec owns this

## YOUR TARGETS (in priority order):

### TARGET 1: consoleLog sub-goals (LINE 4270)
```lean
all_goals sorry -- consoleLog sub-goals: trace/invariants for consoleLog case
```
This is inside the call case where the function IS consoleLog. The `all_goals` means there are multiple sub-goals remaining after the main proof structure. These should be straightforward invariant goals (trace, EnvCorr, HeapInj, etc.) that follow the same patterns you just used for arrayLit.

1. `lean_goal` at L4270 to see what goals remain
2. Try `all_goals (first | rfl | simp_all | assumption | omega)` — if some goals close, narrow down to the hard ones

### TARGET 2: getIndex string (LINE 5060)
```lean
sorry -- getIndex string both-values: Flat/Core semantic mismatch in .number else branch
```
The comment says there's a semantic mismatch — Flat checks `propName == "length"` but Core doesn't. This MAY be a real mismatch (unprovable). Investigate first:
1. `lean_goal` at L5060
2. Read the Flat.step? and Core.step? for getIndex to understand the difference
3. If the mismatch is real, add a comment and MOVE ON

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. Build proof
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
