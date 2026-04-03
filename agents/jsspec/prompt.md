# jsspec — Close functionDef (L6136), then captured variable (L3320)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC ~14 actual sorries.

## ALL PREVIOUS TARGETS WERE BLOCKED — NEW TARGETS BELOW

### Target 1: functionDef (L6136) — FRESH, UNEXPLORED
```lean
| functionDef fname params body isAsync isGen => sorry
```

1. `lean_goal` at L6136 to see the exact proof state
2. `lean_hover_info` on `Flat.convertExpr` to find the `.functionDef` case
3. Key pattern: Core.step? on `functionDef` creates a closure value and stores it in funcs/env. Flat.convertExpr should produce a `makeClosure` or similar that does the analogous thing.
4. This is a LEAF case — no sub-expression stepping needed, just allocation.
5. Build the Core.step? on one side, Flat.step? on the other, show they correspond.

### Target 2: captured variable (L3320) — MEDIUM DIFFICULTY
```lean
| some idx =>
  -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
  sorry
```

This is the case where `Flat.lookupEnv envMap name = some idx`. The converted expression is `.getEnv (.var envVar) idx`.
1. `lean_goal` at L3320
2. Flat.step? on `.getEnv (.var envVar) idx`:
   - First evaluates `.var envVar` → gets the environment object
   - Then gets index `idx` from that object
   - Should produce the same value as `Core.step?` on `.var name` which looks up `sc.env.lookup name`
3. You need `EnvCorrInj` to bridge: the injMap-based env correspondence should ensure that looking up through the closure env gives the same value as direct variable lookup.
4. Check the non-captured case below (L3321-3360) for the proof pattern — adapt it for the captured case.

### Target 3: newObj (L4387) — EXPLORE
```lean
| newObj f args => sorry
```
1. `lean_goal` at L4387
2. Core.step? and Flat.step? for newObj likely involve constructor invocation
3. May be blocked if it needs FuncsCorr. If so, skip.

### COLLISION AVOIDANCE
wasmspec works on L5000-6053. You work on L3000-5000 and L6100+.
Do NOT edit L5000-6053 — that's wasmspec territory.

## CURRENT CC SORRY LOCATIONS (verified 2026-04-03 16:05)
```
L1507: forIn stub (SKIP - unprovable)
L1508: forOf stub (SKIP - unprovable)
L3320: captured variable HeapInj (YOUR TARGET 2)
L3648: CCStateAgree if-then (BLOCKED)
L3671 x2: CCStateAgree if-else (BLOCKED)
L4189: call non-consoleLog (BLOCKED - needs FuncsCorr)
L4387: newObj (YOUR TARGET 3)
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
