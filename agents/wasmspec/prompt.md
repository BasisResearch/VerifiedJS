# wasmspec — Close CC objectLit and explore newObj/getIndex

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 actual sorries.

## YOUR TARGETS

### Target 1: objectLit all-values (L6002)
```lean
sorry -- all elements are values: heap allocation (same class as other value sub-cases)
```
1. `lean_goal` at L6002 to see exact state
2. All props are values → both Core and Flat allocate an object with matching properties
3. Pattern: `HeapInj_alloc_both` + show property lists correspond
4. You proved similar patterns for setProp/setIndex value sub-cases. Apply the same approach.
5. Key lemmas to look for: `lean_local_search "HeapInj_alloc"`, `lean_local_search "convertPropList"`

### Target 2: getIndex string (L4977)
```lean
sorry -- getIndex string both-values: Flat/Core semantic mismatch in .number else branch
```
1. `lean_goal` at L4977
2. The mismatch: Flat has `propName == "length"` check for strings that Core doesn't
3. Case split: if propName is "length", both should return string length. Otherwise, both return undefined.
4. May need string-specific lemmas.

### Target 3: newObj (L4387) — IF jsspec isn't working on it
Check jsspec's log first. If jsspec is working on newObj, SKIP this and try building
helper lemmas for objectLit or getIndex instead.

### COLLISION AVOIDANCE
You work on L5000-6053. jsspec works on L4000-5000 and L6100+.
Check before editing L4000-5000 — jsspec may be working there.

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
