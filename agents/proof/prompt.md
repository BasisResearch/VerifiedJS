# proof — Close CC and ANF sorries

You own ClosureConvertCorrect.lean, ANFConvertCorrect.lean, LowerCorrect.lean.

## Current sorry count: 11 (8 CC + 2 ANF + 1 Lower)

### CC sorries (ClosureConvertCorrect.lean)
```
L829   forIn           sorry — UNPROVABLE (stub, skip)
L830   forOf           sorry — UNPROVABLE (stub, skip)
L1113  var (captured)  sorry — needs EnvObjCorr (see Priority 1)
L1897  call            sorry — needs env/heap/funcs correspondence
L1898  newObj          sorry — needs env/heap correspondence
L3547  objectLit       sorry — needs heap correspondence
L3548  arrayLit        sorry — needs heap correspondence
L3549  functionDef     sorry — needs env/heap/funcs + CC state
```

**L829/L830 are expected sorry — skip them.**

### ANF sorries (ANFConvertCorrect.lean)
```
L106   anfConvert_step_star  sorry — ENTIRE step simulation theorem
L1177  nested seq case        sorry — in anfConvert_halt_star_aux
```

### Lower sorry (LowerCorrect.lean)
```
L69    LowerSimRel.init  by sorry — init field proof (owned by wasmspec, skip)
```

## Priority 1: CC L1113 (captured var — needs EnvObjCorr)

When `lookupEnv envMap name = some idx`, `convertExpr (.var name)` produces `.getEnv (.var envVar) idx`. The Flat semantics evaluates this by:
1. Looking up `envVar` in env → `.object envAddr`
2. Getting property `envSlotKey idx` from heap object at `envAddr`
3. Returning the value

**Missing abstraction**: CC_SimRel needs an env-object correspondence invariant. Add to CC_SimRel:

```lean
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  EnvCorr sc.env sf.env ∧
  HeapCorr sc.heap sf.heap ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧
  EnvAddrWF sc.env sc.heap.objects.size ∧
  HeapValuesWF sc.heap ∧
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st ∧
    -- NEW: env object correspondence for captured variables
    EnvObjCorr sc.env sf.env sf.heap envVar envMap
```

Define:
```lean
/-- Env object correspondence: if envMap is non-empty, envVar maps to an object
    on the Flat heap whose slots contain the captured variable values. -/
private def EnvObjCorr (cenv : Core.Env) (fenv : Flat.Env) (fheap : Core.Heap)
    (envVar : String) (envMap : Flat.EnvMapping) : Prop :=
  ∀ name idx, envMap.find? (fun p => p.1 == name) = some (name, idx) →
    ∃ cv fv envAddr props,
      cenv.lookup name = some cv ∧
      fenv.lookup envVar = some (.object envAddr) ∧
      Flat.heapObjectAt? fheap envAddr = some props ∧
      props.find? (fun kv => kv.1 == Flat.envSlotKey idx) = some (Flat.envSlotKey idx, cv)
```

**NOTE**: `Flat.envSlotKey` is `private`. Either:
1. Make it public in Flat/Semantics.lean (ask wasmspec), or
2. Define your own copy: `private def envSlotKey (idx : Nat) : Core.PropName := "__env" ++ toString idx`

**For initial state**: `envMap = []` so `EnvObjCorr` is vacuously true. No change to `closureConvert_init_related`.

**For most cases**: env object doesn't change, so `EnvObjCorr` is preserved (same heap, same env).

## Priority 2: CC objectLit/arrayLit (L3547-3548)

Both allocate objects. Check `HeapCorr` — if it has `size_eq`, use it. Otherwise add `heap_size_eq : sc.heap.objects.size = sf.heap.objects.size` to CC_SimRel.

## Priority 3: ANF L1177 (nested seq — skip unless CC done)

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
