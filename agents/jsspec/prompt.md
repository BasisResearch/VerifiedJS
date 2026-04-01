# jsspec — Close CC tryCatch body + CCState sub-step sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 sorry lines (down from 16 — wasmspec closed objectLit all-values, you/wasmspec closed 2 tryCatch sorries). Good progress!

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 02:05)
```
L1507, L1508: forIn/forOf stubs (SKIP - theorem false)
L3346: HeapInj refactor (SKIP)
L3674: CCStateAgree if-then (SKIP - architecturally blocked)
L3697 x2: CCStateAgree if-else (SKIP - architecturally blocked)
L4215: call function (BLOCKED - needs FuncsCorr)
L4413: newObj (SKIP)
L5003: getIndex string semantic mismatch (SKIP)
L5998: objectLit CCState sub-step (YOUR TARGET 1)
L6005: arrayLit all-values heap (wasmspec TARGET)
L6101: arrayLit CCState sub-step (YOUR TARGET 2)
L6102: functionDef (SKIP)
L6229: tryCatch body non-value (YOUR TARGET 3)
L6261: while_ CCState (SKIP - architecturally blocked)
```

## YOUR TARGETS (in priority order)

### Target 1: objectLit CCState sub-step (L5998)
When a prop needs stepping: show CCState agreement after the IH.
1. `lean_goal` at L5998
2. Pattern: The IH gives `st_a, st_a', hconv', hAgreeIn, hAgreeOut`. Use hAgreeOut and the
   conversion structure to show the output CCState matches.
3. Key: thread CCState through `convertPropList` for done props, then `convertExpr` for target,
   using `convertExpr_state_determined` and the IH's `hAgreeOut`.
4. This is the SAME PATTERN as the arrayLit sub-step at L6101 and previous setProp/setIndex
   sub-steps that were already closed.

### Target 2: arrayLit CCState sub-step (L6101)
Same pattern as Target 1 but for arrayLit. After proving Target 1, adapt the same approach.

### Target 3: tryCatch body non-value (L6229)
When body is not a value, step it via IH.
1. `lean_goal` at L6229
2. Standard sub-stepping pattern: extract Flat sub-step for body, apply IH, reconstruct
   tryCatch around the result.
3. Need: `Flat_step?_tryCatch_body_step` or similar decomposition lemma
4. CCState threading: body conversion uses `st`, catch uses `st1`, finally uses `st2`.
   The IH only touches the body part, so CCState flows through.

### COLLISION AVOIDANCE
wasmspec works on L5000-5999. You work on L5998-6270. Overlap at L5998 — if wasmspec is there, skip to Target 2.

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
