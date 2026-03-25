# proof — Close remaining CC sorries + ANF

You own Proofs/*.lean and compiler passes. EnvAddrWF is defined and integrated into CC_SimRel. ExprAddrWF_mono is proved. HeapCorr replaces heap identity.

## Current CC sorry count: 10

```
L1055  captured var           sorry (multi-step: Core 1 step, Flat 2 steps via getEnv)
L1115  in-scope var found     sorry /- ExprAddrWF -/
L1803  call                   sorry (env/heap/funcs correspondence)
L1804  newObj                 sorry (env/heap correspondence)
L1860  getProp value          sorry /- ExprAddrWF -/
L2285  getIndex value         sorry /- ExprAddrWF -/
L3309  objectLit              sorry (env/heap correspondence)
L3310  arrayLit               sorry (env/heap correspondence)
L3311  functionDef            sorry (env/heap/funcs + CC state)
L4407  this found             sorry /- ExprAddrWF -/
```

## TASK 0 (DO FIRST): Close L1115 and L4407 ExprAddrWF sorries

These are env-lookup result cases. The converted result is `.lit (convertValue cv)` where `cv` from env lookup. You have `henvwf : EnvAddrWF sc.env sc.heap.objects.size` in scope. Heap doesn't change for var/this steps (var step just changes expr).

**Key facts**:
- `convertExpr (.lit cv) scope envVar envMap st = (.lit (convertValue cv), st)` (ClosureConvert.lean:165)
- `ExprAddrWF (.lit (convertValue cv)) n` reduces to `ValueAddrWF (convertValue cv) n`
- `convertValue` preserves `.object addr` → `.object addr` (ClosureConvert.lean:108)
- So `ValueAddrWF (convertValue cv) n ↔ ValueAddrWF cv n` (for all value constructors)
- `henvwf name cv hcenv` gives `ValueAddrWF cv sc.heap.objects.size`
- After var step, `sc'.heap = sc.heap` (proved at L1114 via `subst h1; exact hheap`)

**L1115** — replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr]; simp [Flat.convertExpr, ExprAddrWF, Flat.convertValue, ValueAddrWF]
   cases cv <;> simp [ValueAddrWF, Flat.convertValue]
   exact henvwf name (.object ‹_›) hcenv
```
If `simp` doesn't close non-object cases, try `<;> trivial` or check the exact goal with `lean_goal`.

**L4407** — same pattern but with `"this"`:
```lean
by rw [hsc'_expr]; simp [Flat.convertExpr, ExprAddrWF, Flat.convertValue, ValueAddrWF]
   cases cv <;> simp [ValueAddrWF, Flat.convertValue]
   exact henvwf "this" (.object ‹_›) hcenv
```

## TASK 1: Close L1860 and L2285 ExprAddrWF sorries (getProp/getIndex)

These need the result value from a heap property lookup to satisfy ValueAddrWF. The value `v` comes from `heap.objects[addr]?.bind (find prop)`. You need HeapValuesWF.

**Option A**: Add `HeapValuesWF sc.heap` (defined at L687) to CC_SimRel. Then close with:
```lean
by cases v <;> simp [ExprAddrWF, ValueAddrWF, Flat.convertExpr, Flat.convertValue] <;> try trivial
   exact heapwf addr haddr_lt props hprops_eq (prop, v) hmem
```

**Option B**: Prove a focused lemma that if ExprAddrWF holds for the getProp expression and the heap is well-formed, then ExprAddrWF holds for the result. Use `lean_goal` at L1860/L2285 to decide.

## TASK 2: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main `anfConvert_step_star` theorem
- **ANFConvertCorrect.lean:1181**: nested seq induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
