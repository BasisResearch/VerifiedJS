# proof — Close CC and ANF sorries

You own ClosureConvertCorrect.lean, ANFConvertCorrect.lean, LowerCorrect.lean.

## Current sorry count: 11 (8 CC + 2 ANF + 1 Lower)

### CC sorries (ClosureConvertCorrect.lean)
```
L829   forIn           sorry — UNPROVABLE (theorem false, forIn converts to .lit .undefined stub)
L830   forOf           sorry — UNPROVABLE (theorem false, forOf converts to .lit .undefined stub)
L1113  var (captured)  sorry — needs env object lookup
L1882  call            sorry — needs env/heap/funcs correspondence
L1883  newObj          sorry — needs env/heap correspondence
L3532  objectLit       sorry — needs heap correspondence (allocObjectWithProps)
L3533  arrayLit        sorry — needs heap correspondence (allocObjectWithProps)
L3534  functionDef     sorry — needs env/heap/funcs + CC state
```

**L829/L830 are expected sorry — skip them.**

### ANF sorries (ANFConvertCorrect.lean)
```
L106   anfConvert_step_star  sorry — ENTIRE step simulation theorem (architecture plan at L107-142)
L1177  nested seq case        sorry — in anfConvert_halt_star_aux, seq c1 c2
```

### Lower sorry (LowerCorrect.lean)
```
L69    LowerSimRel.init  by sorry — init field proof
```

## Priority 1: CC objectLit (L3532)

Both Core and Flat allocate an object on the heap. `allocObjectWithProps` was fixed to populate heap props. The pattern:

1. Core allocates via `Core.allocObject` → pushes properties, gets addr
2. Flat allocates via `Flat.allocObjectWithProps` → same thing

**Key issue**: HeapCorr gives `sc.heap.objects.size ≤ sf.heap.objects.size` (≤, not =). If sizes differ, Core and Flat get different addrs, so `.lit (.object addr)` won't match.

**Check if heaps have equal size** at this point. Read `HeapCorr` definition and `CC_SimRel` to see if `heap_size_eq` can be derived. If HeapCorr gives `=` (because Flat only allocates extra objects for closure envs, and at objectLit time no extra envs exist for this expression), use:
```lean
have hsize : sc.heap.objects.size = sf.heap.objects.size := by
  exact hheap.size_eq  -- or derive from HeapCorr fields
```
Then use `HeapCorr_alloc_both hheap hsize props` to maintain HeapCorr after both push.

If heap sizes CAN differ, you need to add `heap_size_eq : sc.heap.objects.size = sf.heap.objects.size` to CC_SimRel and prove it's preserved.

## Priority 2: ANF L1177 (nested seq — ARCHITECTURAL)

At L1177, case `| seq c1 c2 =>` inside `anfConvert_halt_star_aux`. Variables:
- `a1 = .seq c d` (from an outer case split)
- `c = .seq c1 c2` (this case)
- `sf.expr = .seq (.seq (.seq (.seq c1 c2) d) a2) b`

The induction is on `N` (depth bound, `sf.expr.depth ≤ N + 1`). Depth is ADDITIVE: `.seq a b => a.depth + b.depth + 1`. So seq reassociation does NOT change depth — `ih` can't fire with the same state.

**The case-split approach fails for unbounded left-spine nesting.** Options:

**Option A (recommended)**: Add an INNER induction on `leftSpineCount`:
```lean
def leftSpineCount : Flat.Expr → Nat
  | .seq a _ => leftSpineCount a + 1
  | _ => 0
```
For the `| seq c1 c2 =>` case, show that ONE Flat step either:
- Eliminates a value from the left spine (decreasing leftSpineCount)
- Steps a non-value (producing a state the outer `ih` handles)

**Option B**: Factor out a helper that handles arbitrary left-spine depth using well-founded recursion on `leftSpineCount`.

**Option C**: Skip L1177 for now — it's architecturally hard. Focus on CC sorries first.

## Available lemmas
- `flatToCoreValue_convertValue` (L806)
- `HeapCorr_alloc_both` (L591): both push same object, requires `size =`
- `HeapCorr_alloc_right` (L607): Flat pushes extra object
- `EnvCorr_extend` (L273), `EnvCorr_assign` (L361)
- `HeapValuesWF` preservation: proved for setProp/setIndex/deleteProp

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
