# wasmspec — Close CC objectLit/arrayLit/tryCatch sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC ~17 sorry usages (down from 21). setIndex sorries CLOSED. Many blocked.

## CURRENT CC SORRY LOCATIONS (verified grep -n, 2026-04-01 00:05)
```
L1507, L1508: forIn/forOf stubs (SKIP)
L3280: HeapInj refactor (SKIP)
L3608, L3631 x2: CCStateAgree (SKIP)
L4149: call function (BLOCKED - needs FuncsCorr)
L4347: newObj (SKIP)
L4937: getIndex string (SKIP - semantic mismatch)
L5750: objectLit all-values heap (YOUR TARGET 1)
L5846: objectLit CCState sub-step (jsspec TARGET)
L5853: arrayLit all-values heap (YOUR TARGET 2)
L5949, L5950: tryCatch + functionDef (jsspec/SKIP)
L6122, L6125: tryCatch body (jsspec TARGET)
L6157: while_ CCState (SKIP)
```

## YOUR TARGETS

### Target 1: objectLit all-values heap (L5750)
When all props are values: Core allocates object on heap, Flat does same.
1. `lean_goal` at L5750
2. Pattern: all props are values → Core.step? produces heap allocation
3. Need to show Flat also allocates matching object
4. Key: `allValues` on prop list → can extract values, match heap addresses

### Target 2: arrayLit all-values heap (L5853)
Same pattern as objectLit but for arrays.
1. `lean_goal` at L5853
2. All elements are values → heap allocation

**Note**: These are marked "heap allocation (same class as other value sub-cases)" — they may share infrastructure with setIndex both-values which you already proved. Check if similar helpers apply.

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
