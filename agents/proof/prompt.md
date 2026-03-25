# proof — Close remaining CC sorries + ANF

You own Proofs/*.lean and compiler passes. EnvAddrWF is defined and integrated into CC_SimRel. ExprAddrWF_mono is proved. HeapCorr replaces heap identity.

## Current CC sorry count: 10

```
L1061  captured var           sorry (multi-step: Core 1 step, Flat 2 steps via getEnv)
L1123  in-scope var found     sorry /- ExprAddrWF -/
L1811  call                   sorry (env/heap/funcs correspondence)
L1812  newObj                 sorry (env/heap correspondence)
L1868  getProp value          sorry /- ExprAddrWF -/
L2293  getIndex value         sorry /- ExprAddrWF -/
L3317  objectLit              sorry — MAY BE UNBLOCKED (see TASK 2)
L3318  arrayLit               sorry — MAY BE UNBLOCKED (see TASK 2)
L3319  functionDef            sorry (env/heap/funcs + CC state)
L4415  this found             sorry /- ExprAddrWF -/
```

## TASK 0 (DO FIRST): Close L1123 and L4415 ExprAddrWF sorries

The sub-function returns tuple: `⟨trace, envCorr, heapCorr, envAddrWF, noCallFrameReturn, exprAddrWF, scope, st, st', conv⟩`.

The sorry at position 6 is ExprAddrWF. The goal: `ExprAddrWF sc'.expr sc'.heap.objects.size`.

**L1123** (`.var name`, in-scope, found): You have `hsc'_expr`, `hsc'_heap`, `henvwf`, `hcenv : sc.env.lookup name = some cv`.
The sorry is inline: `sorry /- ExprAddrWF -/`. Replace with:
```lean
by rw [hsc'_expr, hsc'_heap]; simp [ExprAddrWF]; exact henvwf name cv hcenv
```
If `simp [ExprAddrWF]` doesn't reduce, try `exact henvwf name cv hcenv` directly.

**L4415** (`.this`, found): You have `hsc'_expr`, `henvwf`, `hcenv : sc.env.lookup "this" = some cv`.
The heap is already rewritten at L4414 (`exact hheap`), so sc'.heap = sc.heap is established in context.
Replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr]; simp [ExprAddrWF]; exact henvwf "this" cv hcenv
```
If that fails because heap isn't rewritten in ExprAddrWF, try:
```lean
by simp [ExprAddrWF]; exact henvwf "this" cv hcenv
```

Use `lean_goal` at L1123 and L4415 to verify before editing.

## TASK 1: Close L1868 and L2293 ExprAddrWF sorries (getProp/getIndex)

These need the looked-up property VALUE to satisfy ValueAddrWF. The value comes from the heap, so you need **HeapValuesWF**:
```lean
private def HeapValuesWF (heap : Core.Heap) : Prop :=
  ∀ addr, addr < heap.objects.size →
    ∀ props, heap.objects[addr]? = some props →
      ∀ kv, kv ∈ props → ValueAddrWF kv.2 heap.objects.size
```

This is NOT yet in CC_SimRel. To close L1868/L2293:
1. Add `HeapValuesWF sc.heap` to CC_SimRel (after EnvAddrWF)
2. Prove it holds initially: initial heap has 1 object (console) with no props → trivially WF
3. Prove it's preserved by each step: heap-mutating steps (setProp, setIndex, objectLit, arrayLit) must maintain it. For non-mutating steps, `hsc'_heap : sc'.heap = sc.heap` gives it for free.
4. Use it at L1868/L2293: extract the addr < heap.size from ExprAddrWF, look up the property, apply HeapValuesWF

Skip if TASK 0 isn't done.

## TASK 2: Close L3317 and L3318 (objectLit/arrayLit)

Your previous analysis said these are BLOCKED by `allocFreshObject` pushing `[]`. This is STALE:
- **objectLit** (Flat/Semantics.lean:803) now uses `allocObjectWithProps s.heap heapProps`
- **arrayLit** (Flat/Semantics.lean:822) also uses `allocObjectWithProps` with indexed props

Re-analyze with `lean_goal` at L3317/L3318.

## TASK 3: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main `anfConvert_step_star` theorem
- **ANFConvertCorrect.lean:1181**: nested seq induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
