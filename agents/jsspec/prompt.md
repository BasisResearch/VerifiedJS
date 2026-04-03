# jsspec — NEW DIRECTION: functionDef, newObj, and FuncsCorr infrastructure

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 actual sorries.

## IMPORTANT: Your previous targets are ALL BLOCKED
- tryCatch body-value with finally (L6291): BLOCKED by CCStateAgree
- tryCatch error case (L6309): BLOCKED by scope mismatch
- call function (L4189): BLOCKED by missing FuncsCorr

These are architectural issues. Do NOT attempt them again.

## YOUR NEW TARGETS (in priority order)

### Target 1: functionDef (L6136)
```lean
| functionDef fname params body isAsync isGen => sorry
```
1. `lean_goal` at L6136 to see the exact goal
2. `lean_hover_info` on `Flat.convertExpr` for the `.functionDef` case to understand conversion
3. Core.step? on functionDef creates a closure and stores it. Flat.step? should do analogous.
4. This may be tractable if the closure conversion for functionDef is straightforward.

### Target 2: newObj (L4387)
```lean
| newObj f args => sorry
```
1. `lean_goal` at L4387
2. Check what Core.step? does for newObj and what Flat.step? does
3. May need constructor lookup infrastructure

### Target 3: Build FuncsCorr infrastructure
If Targets 1-2 are blocked, start building infrastructure:
1. `lean_local_search "FuncsCorr"` to see if anything exists
2. Define `FuncsCorr` as a correspondence between Core and Flat function stores
3. This unblocks call function (L4189) which is one of the harder sorries

### COLLISION AVOIDANCE
wasmspec works on L5000-6053. You work on L4000-5000 and L6100+.
Do NOT edit L5000-6053 — that's wasmspec territory.

## CURRENT CC SORRY LOCATIONS (verified 2026-04-03 16:00)
```
L1507: forIn stub (SKIP)
L1508: forOf stub (SKIP)
L3320: captured variable HeapInj (SKIP)
L3648: CCStateAgree if-then (BLOCKED)
L3671 x2: CCStateAgree if-else (BLOCKED)
L4189: call non-consoleLog (BLOCKED - needs FuncsCorr)
L4387: newObj (YOUR TARGET 2)
L4977: getIndex string mismatch (SKIP)
L6002: objectLit all-values (wasmspec — DO NOT TOUCH)
L6136: functionDef (YOUR TARGET 1)
L6291: tryCatch finally (BLOCKED)
L6309: tryCatch error scope (BLOCKED)
L6416: while_ CCState (BLOCKED)
```

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
