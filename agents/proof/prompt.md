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
L3313  objectLit              sorry — MAY BE UNBLOCKED (see below)
L3314  arrayLit               sorry — MAY BE UNBLOCKED (see below)
L3315  functionDef            sorry (env/heap/funcs + CC state)
L4411  this found             sorry /- ExprAddrWF -/
```

## TASK 0 (DO FIRST): Close L1119 and L4411 ExprAddrWF sorries

These are env-lookup result cases. You have in scope:
- `hsc'_expr : sc'.expr = .lit cv`
- `hsc'_heap : sc'.heap = sc.heap`
- `henvwf : EnvAddrWF sc.env sc.heap.objects.size`
- `hcenv : sc.env.lookup name = some cv` (L1119) or `hcenv : sc.env.lookup "this" = some cv` (L4411)

The goal is `ExprAddrWF sc'.expr sc'.heap.objects.size`.

**L1119** — replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr, hsc'_heap]; simp [ExprAddrWF]; exact henvwf name cv hcenv
```

**L4411** — replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr, hsc'_heap]; simp [ExprAddrWF]; exact henvwf "this" cv hcenv
```

If `simp [ExprAddrWF]` doesn't reduce to `ValueAddrWF cv sc.heap.objects.size`, try `simp [ExprAddrWF, ValueAddrWF]; cases cv <;> simp [ValueAddrWF] <;> try exact henvwf name cv hcenv`.

Use `lean_goal` at L1119/L4411 to verify before editing.

## TASK 1: Close L1864 and L2289 ExprAddrWF sorries (getProp/getIndex)

These need heap lookup value to satisfy ValueAddrWF. Add `HeapValuesWF sc.heap` (L687) to CC_SimRel if not already there.

## TASK 2: Close L3313 and L3314 (objectLit/arrayLit)

**IMPORTANT**: Your previous analysis said these are BLOCKED by `allocFreshObject` pushing `[]`. This is STALE — `allocFreshObject` was fixed. Check the code:
- **objectLit** (Flat/Semantics.lean:803) now uses `allocObjectWithProps s.heap heapProps` which pushes actual properties
- **arrayLit** (Flat/Semantics.lean:822) also uses `allocObjectWithProps` with indexed props

Both Flat and Core now allocate objects with properties. HeapCorr should be maintainable through these operations. Re-analyze with `lean_goal` at L3313/L3314 to check.

## TASK 3: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main `anfConvert_step_star` theorem
- **ANFConvertCorrect.lean:1181**: nested seq induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
