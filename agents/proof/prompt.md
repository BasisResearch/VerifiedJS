# proof — Close remaining CC sorries + ANF

You own Proofs/*.lean and compiler passes. EnvAddrWF is defined and integrated into CC_SimRel. ExprAddrWF_mono is proved. HeapCorr replaces heap identity.

## Current CC sorry count: 8

```
L1074  captured var           sorry (multi-step: Core 1 step, Flat 2 steps via getEnv)
L1824  call                   sorry (env/heap/funcs correspondence)
L1825  newObj                 sorry (env/heap correspondence)
L1881  getProp value          sorry /- ExprAddrWF -/  (needs HeapValuesWF)
L2306  getIndex value         sorry /- ExprAddrWF -/  (needs HeapValuesWF)
L3330  objectLit              sorry (env/heap correspondence)
L3331  arrayLit               sorry (env/heap correspondence)
L3332  functionDef            sorry (env/heap/funcs + CC state)
```

## TASK 0 (DO FIRST): Close L1881 and L2306 ExprAddrWF sorries

These are inside getProp (L1881) and getIndex (L2306) cases. The pattern is identical:
```lean
refine ⟨sorry /- ExprAddrWF -/, scope, st, st, ?_⟩
```

The goal is `ExprAddrWF <result_expr> sc'.heap.objects.size`. The result comes from looking up a property in the heap. To prove the result value satisfies addr bounds, you need **HeapValuesWF**:

```lean
private def HeapValuesWF (heap : Core.Heap) : Prop :=
  ∀ addr, addr < heap.objects.size →
    ∀ props, heap.objects[addr]? = some props →
      ∀ kv, kv ∈ props → ValueAddrWF kv.2 heap.objects.size
```

**Steps:**
1. Add `hheapvwf : HeapValuesWF sc.heap` field to CC_SimRel
2. Prove it holds initially: initial heap has 1 object (console) with no props → trivially WF
3. Prove preservation: non-mutating steps get it from `hsc'_heap : sc'.heap = sc.heap`; mutating steps (setProp, setIndex) preserve it if the stored value satisfies ValueAddrWF
4. At L1881/L2306: the value `v` is `object addr` with `addr < heap.objects.size` (from ExprAddrWF of the sub-expression). The property lookup gives a value from the heap. Apply HeapValuesWF to get `ValueAddrWF result heap.objects.size`, then show that implies `ExprAddrWF` of the result expression.

Use `lean_goal` at L1881 and L2306 to verify the exact goal shape before editing.

## TASK 1: Close L3330/L3331 (objectLit/arrayLit)

These use `allocObjectWithProps` (not `allocFreshObject` with `[]` — that blocker is STALE).
- Flat/Semantics.lean:803: objectLit uses `allocObjectWithProps s.heap heapProps`
- Flat/Semantics.lean:822: arrayLit uses `allocObjectWithProps` with indexed props

Re-analyze with `lean_goal` at L3330/L3331. The key insight: after `allocObjectWithProps`, `heap.objects.size` increases by 1, and the new object addr = old size. Show ExprAddrWF and HeapCorr are preserved.

## TASK 2: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main `anfConvert_step_star` theorem
- **ANFConvertCorrect.lean:1181**: nested seq induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
