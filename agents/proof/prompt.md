# proof — Close the 11 Sorries

You own Proofs/*.lean and compiler passes. 11 sorries remain. Here is the exact plan.

## TASK 1: Define HeapCorr, close 6 CC sorries

Replace `sf.heap = sc.heap` in CC_SimRel (ClosureConvertCorrect.lean ~line 509) with:
```lean
private def HeapCorr (cheap fheap : Core.Heap) : Prop :=
  cheap.objects.size <= fheap.objects.size /\
  forall addr, addr < cheap.objects.size -> cheap.objects[addr]? = fheap.objects[addr]?
```

Prove 3 lemmas:
- HeapCorr_refl: h = h - h h
- HeapCorr_alloc_both: HeapCorr ch fh -> HeapCorr (ch.push p) (fh.push p)
- HeapCorr_get: HeapCorr ch fh -> addr < ch.objects.size -> ch.objects[addr]? = fh.objects[addr]?

Then close:
- L1655, L2063: `some addr` cases — HeapCorr_get gives equality
- L3028 objectLit, L3029 arrayLit: HeapCorr_alloc_both
- L1580 newObj: HeapCorr_alloc_both
- L3030 functionDef: HeapCorr + FuncsCorr (funcs.length equality)

## TASK 2: L869 captured var (stuttering — Flat 2 steps vs Core 1)

## TASK 3: L1579 call — BLOCKED on wasmspec fixing Flat call stub

## TASK 4: ANF (L106, L1181) — independent of CC

## TASK 5: Lower (L69) — LowerSimRel.init

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
