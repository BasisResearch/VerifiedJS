# proof — Close CC and ANF sorries

You own ClosureConvertCorrect.lean, ANFConvertCorrect.lean, LowerCorrect.lean.

## Current sorry count: 9 (6 CC + 2 ANF + 1 Lower)

### CC sorries (ClosureConvertCorrect.lean)
```
L1101  var (captured)     sorry — envMap says name→idx, Flat expr is .getEnv (.var envVar) idx
L1870  call               sorry — needs env/heap/funcs correspondence
L1871  newObj              sorry — needs env/heap correspondence
L3520  objectLit           sorry — stepping sub-case + all-values allocation
L3521  arrayLit            sorry — stepping sub-case + all-values allocation
L3522  functionDef         sorry — needs env/heap/funcs + CC state
```

### ANF sorries (ANFConvertCorrect.lean)
```
L106   anfConvert_step_star  sorry — ENTIRE step simulation theorem
L1177  nested seq case        sorry — in anfConvert_halt_star_aux, seq c1 c2
```

### Lower sorry (LowerCorrect.lean)
```
L69    LowerSimRel.init  by sorry — init field proof
```

## Priority: ANF L1177 (nested seq case)

This is the most tractable sorry. At L1177, inside `anfConvert_halt_star_aux`, the case is `| seq c1 c2 =>` where `c = .seq c1 c2`. The issue: left-spine depth > 3 needs recursive flattening.

**Strategy**: Add an inner induction on `c` (the left spine of seq chains) or use well-founded recursion on `Flat.Expr.depth c`. The pattern is:
1. `c = .seq c1 c2`: flatten by stepping c1, then handle c2
2. Each flatten step reduces depth by at least 1

Try replacing L1177 with:
```lean
            -- Nested seq: step c1 in Flat, which steps the whole .seq (.seq c1 c2) b
            -- Since c1 might also be a seq, we need to recurse
            -- But sf.expr.depth strictly decreases when stepping into c1
            have hd_c1 : Flat.Expr.depth c1 < Flat.Expr.depth c := by
              rw [hc]; simp [Flat.Expr.depth]; omega
            -- The Flat step for .seq (.seq c1 c2) b steps into c1
            -- Use ih with decreased depth on the inner seq
            sorry -- TODO: construct the Flat step and apply ih
```

If this approach is blocked, try adding a helper lemma:
```lean
private theorem flatten_seq_left (sf : Flat.State) (c1 c2 b : Flat.Expr) :
    sf.expr = .seq (.seq c1 c2) b →
    ∃ sf', Flat.Step sf .silent sf' ∧ sf'.expr.depth < sf.expr.depth := by
  sorry
```

## Priority: CC objectLit/arrayLit (L3520-L3521)

These have TWO sub-cases each:

**Sub-case 1 (stepping)**: Some prop/elem is not a value. Both Core and Flat step the same sub-expression. Use `ih_depth` on the sub-expression (depth strictly decreases via `firstNonValueProp_depth`). This follows the same pattern as the `binary`/`seq` stepping cases already proved above.

**Sub-case 2 (all-values allocation)**: All props/elems are values. Both Core and Flat allocate on heap. BUT: HeapCorr is a PREFIX relation (`cheap.objects.size ≤ fheap.objects.size`). When both allocate, Core addr = `sc.heap.nextAddr`, Flat addr = `sf.heap.nextAddr`. If heap sizes differ, addrs differ and `.lit (.object addr)` won't match.

**Key insight**: You need to prove that at objectLit/arrayLit time, `sc.heap.objects.size = sf.heap.objects.size` (no extra Flat env objects yet). This might require strengthening CC_SimRel with a `heap_size_eq` field, or tracking when extra Flat objects are added.

Alternatively, if heap sizes always match (because closure envs haven't been allocated yet for the current expression), use:
```lean
have hsize : sc.heap.objects.size = sf.heap.objects.size := by
  -- HeapCorr gives ≤, need = . If no extra Flat objects, this holds.
  sorry
```
Then apply `HeapCorr_alloc_both hheap hsize heapProps`.

## Available lemmas
- `flatToCoreValue_convertValue : Flat.flatToCoreValue (Flat.convertValue v) = v` (L806)
- `HeapCorr_alloc_both` (L591): both push same object, requires `size =`
- `HeapCorr_alloc_right` (L607): Flat pushes extra object
- `EnvCorr_extend` (L273), `EnvCorr_assign` (L361)
- `HeapValuesWF` preservation: already proved for setProp/setIndex/deleteProp

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
