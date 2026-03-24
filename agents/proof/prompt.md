# proof — Close 42 Sorries (8 CC + 2 ANF + 1 Lower + 31 Wasm)

You own Proofs/*.lean and compiler passes. HeapCorr is DONE ✅. Focus on closing the remaining CC sorries.

## TASK 0 (DO FIRST): Close L1655 and L2063 — well-formedness

These are `| some addr => sorry` branches in getProp/getIndex where `addr` came from Flat heap but might be outside Core heap range. HeapCorr gives `cheap.objects.size ≤ fheap.objects.size` but you need to show the addr actually came from Core (so `addr < cheap.objects.size`).

Strategy: The addr comes from `convertValue v` which converts Core values to Flat values. For `.object addr`, convertValue preserves the addr. So if the Core expression produced `.object addr`, then `addr` was allocated by Core → `addr < sc.heap.objects.size`. Add a `AllAddrsValid` invariant to CC_SimRel or prove it inline from EnvCorr + HeapCorr.

Try this approach at L1655:
```lean
-- The addr comes from a Core value via convertValue, so it's in Core heap range
-- Show: if sc produces .object addr, then addr < sc.heap.objects.size
-- Use HeapCorr_get once you have the bound
```

## TASK 1: Close L3028 objectLit, L3029 arrayLit, L1580 newObj

**BLOCKER**: Flat `allocFreshObject` pushes `[]` to heap. Core pushes actual properties. HeapCorr (`cheap.objects[addr]? = fheap.objects[addr]?`) is FALSE at the new address because `[]` ≠ `heapProps`.

**You CANNOT prove these until wasmspec fixes `allocFreshObject`**. Skip for now.

If wasmspec fixes it (pushes properties), then HeapCorr_alloc_both closes all 3.

## TASK 2: L869 captured var (stuttering)

Core: `.var name` → 1 step → value
Flat: `.getEnv (.var envVar) idx` → 2 steps → value (first step evals `.var envVar` to env object, second step does getEnv)

Need multi-step simulation. Use `Flat.Steps` (transitive closure) to show Flat reaches the same value in 2 steps.

## TASK 3: L1579 call — needs function body correspondence

Core enters function body. Flat also enters function body (call IS implemented — not a stub). Need to show CC_SimRel is preserved when stepping into the function.

## TASK 4: L3030 functionDef — most complex, do last

## TASK 5: ANF (L106, L1181) — independent of CC, work on if CC is blocked

## TASK 6: Lower (L69) — LowerSimRel.init, blocked by `lowerExpr` being partial

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
