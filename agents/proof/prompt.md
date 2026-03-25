# proof — Close remaining CC sorries + ANF

You own Proofs/*.lean and compiler passes. EnvAddrWF is defined and integrated into CC_SimRel. ExprAddrWF_mono is proved. HeapCorr replaces heap identity.

## Current CC sorry count: 10

```
L1057  captured var           sorry (multi-step: Core 1 step, Flat 2 steps via getEnv)
L1119  in-scope var found     sorry /- ExprAddrWF -/
L1807  call                   sorry (env/heap/funcs correspondence)
L1808  newObj                 sorry (env/heap correspondence)
L1864  getProp value          sorry /- ExprAddrWF -/
L2289  getIndex value         sorry /- ExprAddrWF -/
L3313  objectLit              sorry — MAY BE UNBLOCKED (see TASK 2)
L3314  arrayLit               sorry — MAY BE UNBLOCKED (see TASK 2)
L3315  functionDef            sorry (env/heap/funcs + CC state)
L4411  this found             sorry /- ExprAddrWF -/
```

## TASK 0 (DO FIRST): Close L1119 and L4411 ExprAddrWF sorries

The sub-function returns tuple: `⟨trace, envCorr, heapCorr, envAddrWF, noCallFrameReturn, exprAddrWF, scope, st, st', conv⟩`.

The sorry at position 6 is ExprAddrWF. The goal: `ExprAddrWF sc'.expr sc'.heap.objects.size`.

**L1119** (`.var name`, in-scope, found): You have `hsc'_expr`, `hsc'_heap`, `henvwf`, `hcenv : sc.env.lookup name = some cv`.
Replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr, hsc'_heap]; simp [ExprAddrWF]; exact henvwf name cv hcenv
```
If `simp [ExprAddrWF]` doesn't reduce, try `exact henvwf name cv hcenv` directly (it may reduce by definitional equality).

**L4411** (`.this`, found): You have `hsc'_expr`, `henvwf`, `hcenv : sc.env.lookup "this" = some cv`.
**NOTE**: There is NO `hsc'_heap` in this branch. You need to add it first. Insert before L4411:
```lean
      have hsc'_heap : sc'.heap = sc.heap := by
        have h0 := hcstep
        rw [show sc = {sc with expr := .this} from by cases sc; simp_all] at h0
        simp only [Core.step?, hcenv] at h0
        have heq := (Prod.mk.inj (Option.some.inj h0)).2; subst heq; rfl
```
Then replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr, hsc'_heap]; simp [ExprAddrWF]; exact henvwf "this" cv hcenv
```

**Alternative if henvwf already unifies without rewriting**: If `lean_goal` shows the goal is `ExprAddrWF (.lit cv) sc.heap.objects.size` (already simplified), then just use:
```lean
by simp [ExprAddrWF]; exact henvwf name cv hcenv  -- L1119
by simp [ExprAddrWF]; exact henvwf "this" cv hcenv  -- L4411
```

Use `lean_goal` at L1119 and L4411 to verify before editing.

## TASK 1: Close L1864 and L2289 ExprAddrWF sorries (getProp/getIndex)

These need the looked-up property VALUE to satisfy ValueAddrWF. The value comes from the heap, so you need **HeapValuesWF** (L687):
```lean
private def HeapValuesWF (heap : Core.Heap) : Prop :=
  ∀ addr, addr < heap.objects.size →
    ∀ props, heap.objects[addr]? = some props →
      ∀ kv, kv ∈ props → ValueAddrWF kv.2 heap.objects.size
```

This is NOT yet in CC_SimRel. To close L1864/L2289:
1. Add `HeapValuesWF sc.heap` to CC_SimRel (after EnvAddrWF)
2. Prove it holds initially (closureConvert_init_related): initial heap has 1 object (console) with no props → trivially WF
3. Prove it's preserved by each step: heap-mutating steps (setProp, setIndex, objectLit, arrayLit) must maintain it. For non-mutating steps, `hsc'_heap : sc'.heap = sc.heap` gives it for free.
4. Use it at L1864/L2289: extract the addr < heap.size from ExprAddrWF, look up the property, apply HeapValuesWF

This is a significant invariant addition. Skip if TASK 0 isn't done.

## TASK 2: Close L3313 and L3314 (objectLit/arrayLit)

Your previous analysis said these are BLOCKED by `allocFreshObject` pushing `[]`. This is STALE:
- **objectLit** (Flat/Semantics.lean:803) now uses `allocObjectWithProps s.heap heapProps`
- **arrayLit** (Flat/Semantics.lean:822) also uses `allocObjectWithProps` with indexed props

Re-analyze with `lean_goal` at L3313/L3314.

## TASK 3: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main `anfConvert_step_star` theorem
- **ANFConvertCorrect.lean:1181**: nested seq induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
