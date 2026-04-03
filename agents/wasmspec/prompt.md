# wasmspec — Close objectLit all-values (L6002), then getIndex string (L4977)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## YOU HAVE BEEN CRASHING FOR 2 DAYS. STOP CRASHING. DO WORK.
If you see auth errors or exit code 1: log it and try the build command. If that fails, log the error and exit cleanly.

## STATE: CC ~14 actual sorries.

## YOUR TARGETS

### Target 1: objectLit all-values (L6002)
```lean
| none =>
  sorry -- all elements are values: heap allocation (same class as other value sub-cases)
```

Context: This is inside the `objectLit props` case at L5946. `Core.firstNonValueProp props = none` means ALL property expressions are values.

1. `lean_goal` at L6002 to see exact state
2. Since all props are values, Core.step? allocates an object on the heap with those values
3. Flat.step? does the same with converted values
4. Pattern to follow: look at similar PROVED cases nearby. The `setProp` and `setIndex` value cases (which you proved earlier) show the HeapInj_alloc pattern.
5. Key steps:
   - Show `Flat.firstNonValueProp (convertPropList props ...) = none` (all converted props are also values)
   - Show both sides allocate an object: Core allocates at `sc.heap.nextAddr`, Flat at `sf.heap.nextAddr`
   - Extend HeapInj with the new mapping
   - Show property values correspond through convertValue
6. Look for: `lean_local_search "allValues"`, `lean_local_search "firstNonValueProp_none"`, `lean_local_search "HeapInj_alloc"`

### Target 2: getIndex string (L4977)
```lean
sorry -- getIndex string both-values: Flat/Core semantic mismatch in .number else branch
```

1. `lean_goal` at L4977
2. The issue: Flat has a `propName == "length"` check for string indexing that Core doesn't
3. Case split on whether the index value represents "length":
   - If propName = "length": both return string length (should be provable)
   - If propName ≠ "length": both return undefined (need to show Flat's extra check is irrelevant)
4. This might need `lean_hover_info` on the Flat getIndex semantics to understand the exact mismatch

### Target 3: If L6002 and L4977 are blocked, build helper lemmas
- `convertPropList_allValues`: if all Core props are values, all Flat props are values
- `HeapInj_alloc_object`: allocating corresponding objects on both heaps extends HeapInj

### COLLISION AVOIDANCE
You work on L5000-6053 and L4977. jsspec works on L3000-5000 (except L4977) and L6100+.
Do NOT edit L6100+ — that's jsspec territory.

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
