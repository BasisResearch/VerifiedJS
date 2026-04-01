# wasmspec — Close CC objectLit/arrayLit all-values heap sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 19 sorry lines (down from 21). You closed 2 setIndex sorries last run. Great work.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 01:05)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3280: HeapInj refactor (SKIP)
L3608, L3631 x2: CCStateAgree (SKIP)
L4149: call function (BLOCKED)
L4347: newObj (SKIP)
L4937: getIndex string (SKIP)
L5750: objectLit all-values heap (YOUR TARGET 1)
L5846: objectLit CCState sub-step (jsspec TARGET)
L5853: arrayLit all-values heap (YOUR TARGET 2)
L5949, L5950: tryCatch/functionDef (jsspec/SKIP)
L6129, L6132: tryCatch body (jsspec TARGET)
L6164: while_ CCState (SKIP)
```

## YOUR TARGETS

### Target 1: objectLit all-values heap (L5750)
When all props are values: Core allocates object on heap, Flat does same.
1. `lean_goal` at L5750
2. Pattern: all props are values → Core.step? produces heap allocation → Flat does matching allocation
3. **WARNING**: PROOF_BLOCKERS.md says this MAY be blocked by HeapInj prefix (HeapCorr).
   Check if goal needs HeapInj_alloc_both. If so, check whether Flat heap can be bigger
   from env allocations. If blocked, document and move to Target 2.
4. Key helpers to look for: `allValues_convertExprList_valuesFromExprList`, heap allocation lemmas
5. Your previous work on setIndex both-values may share infrastructure — check similar helpers

### Target 2: arrayLit all-values heap (L5853)
Same pattern as objectLit but for arrays.
1. `lean_goal` at L5853
2. All elements are values → heap allocation
3. Same HeapInj caution as Target 1

### If both targets are blocked by HeapInj:
Look at L5846 (objectLit CCState sub-step) — but check with jsspec first (they own L5800+).
If jsspec is not working on it, you can take it. Otherwise, investigate if ANY sorry in
L3000-5000 range is provable.

### COLLISION AVOIDANCE
jsspec works on L5800-6200. You work on L5000-5800. Do NOT edit overlapping regions.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
