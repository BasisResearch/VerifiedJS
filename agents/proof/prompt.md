# proof — Close remaining CC sorries + ANF

You own Proofs/*.lean and compiler passes. EnvAddrWF is defined and integrated into CC_SimRel. ExprAddrWF_mono is proved. You closed 44 ExprAddrWF preservation sorries — excellent work.

## Current CC sorry count: 10

```
L1045  captured var           sorry (multi-step simulation)
L1105  in-scope var           sorry /- ExprAddrWF -/
L1771  call                   sorry (env/heap/funcs correspondence)
L1772  newObj                 sorry (env/heap correspondence)
L1828  getProp value          sorry /- ExprAddrWF -/
L2251  getIndex value         sorry /- ExprAddrWF -/
L3267  objectLit              sorry (env/heap correspondence)
L3268  arrayLit               sorry (env/heap correspondence)
L3269  functionDef            sorry (env/heap/funcs + CC state)
L4360  this found             sorry /- ExprAddrWF -/
```

## TASK 0 (DO FIRST): Close L1105 and L4360 ExprAddrWF sorries

These are env-lookup cases. The result expression is `.lit cv` where `cv` comes from `sc.env.lookup`. You have `henvwf : EnvAddrWF sc.env sc.heap.objects.size` in scope (from CC_SimRel destructuring). The heap doesn't change for var/this steps.

**L1105** (in-scope var, `cv` from `hcenv : sc.env.lookup name = some cv`):
Replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr]; simp [ExprAddrWF]; exact henvwf name cv hcenv
```
If the destructured variable names differ, use `lean_goal` at L1105 col 90 to see what's in scope.

**L4360** (this, `cv` from `hcenv : sc.env.lookup "this" = some cv`):
Replace `sorry /- ExprAddrWF -/` with:
```lean
by rw [hsc'_expr]; simp [ExprAddrWF]; exact henvwf "this" cv hcenv
```

## TASK 1: Close L1828 and L2251 ExprAddrWF sorries (getProp/getIndex)

These need the result value from a heap property lookup to satisfy ValueAddrWF. The value `v` comes from `heap.objects[addr]?.bind (find prop)`. You need HeapValuesWF in scope.

**Option A**: Add `HeapValuesWF sc.heap` to CC_SimRel (you already have the definition at L687). Then close the sorry with:
```lean
by cases v <;> simp [ExprAddrWF, ValueAddrWF] <;> try rfl
   exact heapwf addr haddr_lt props hprops_eq (prop, v) hmem
```

**Option B**: If HeapValuesWF integration is too disruptive, prove a focused lemma that the specific value from the property lookup satisfies ValueAddrWF using the ExprAddrWF hypothesis on the original getProp expression. Use `lean_goal` at L1828/L2251 to decide.

## TASK 2: Close L1045 (captured var multi-step)

Core: `.var name` → env lookup → `.lit cv` (1 step)
Flat: `.getEnv (.var envVar) idx` → multi-step (var lookup + getEnv)

This needs a multi-step simulation lemma. Use `lean_goal` at L1045 to see the exact goal shape.

## TASK 3: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main `anfConvert_step_star` theorem
- **ANFConvertCorrect.lean:1181**: nested seq induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
