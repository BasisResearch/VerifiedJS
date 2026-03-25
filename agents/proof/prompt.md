# proof — Close CC and ANF sorries

You own ClosureConvertCorrect.lean, ANFConvertCorrect.lean, LowerCorrect.lean.

## Current sorry count: 12 (9 CC + 2 ANF + 1 Lower)

### CC sorries (ClosureConvertCorrect.lean)
```
L829   forIn           sorry — UNPROVABLE (stub, skip)
L830   forOf           sorry — UNPROVABLE (stub, skip)
L1113  var (captured)  sorry — needs EnvObjCorr (see Priority 1)
L1252  let (some v)    sorry — let-value case, init is literal
L1818  call            sorry — needs env/heap/funcs correspondence
L1819  newObj          sorry — needs env/heap correspondence
L3468  objectLit       sorry — needs heap correspondence
L3469  arrayLit        sorry — needs heap correspondence
L3470  functionDef     sorry — needs env/heap/funcs + CC state
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

## Priority 1: CC L1252 (let-value some case)

When `Core.exprValue? init = some v`, the init is a literal. `convertExpr (.lit v)` = `(.lit (convertValue v), st)`. Both Core and Flat take a let-value step:
- Core: `step? {expr := .let name (.lit v) body, ...}` = silent, bind `name → v`, continue with body
- Flat: `step? {expr := .let name (.lit (convertValue v)) body', ...}` = silent, bind `name → convertValue v`, continue with body'

Proof sketch (already partially done in your last run):
1. `cases init` from `Core.exprValue? init = some v` to get `init = .lit v`
2. `simp [Flat.convertExpr]` to simplify flat conversion
3. Show both sides step silently to body with extended env
4. Prove all CC_SimRel invariants (EnvCorr_extend, HeapCorr unchanged, etc.)

If you already have a working proof from your worktree, build and commit it.

## Priority 2: CC L1113 (captured var — needs EnvObjCorr)

When `lookupEnv envMap name = some idx`, `convertExpr (.var name)` produces `.getEnv (.var envVar) idx`. Add to CC_SimRel:

```lean
private def EnvObjCorr (cenv : Core.Env) (fenv : Flat.Env) (fheap : Core.Heap)
    (envVar : String) (envMap : Flat.EnvMapping) : Prop :=
  ∀ name idx, envMap.find? (fun p => p.1 == name) = some (name, idx) →
    ∃ cv fv envAddr props,
      cenv.lookup name = some cv ∧
      fenv.lookup envVar = some (.object envAddr) ∧
      Flat.heapObjectAt? fheap envAddr = some props ∧
      props.find? (fun kv => kv.1 == Flat.envSlotKey idx) = some (Flat.envSlotKey idx, cv)
```

**NOTE**: `Flat.envSlotKey` is `private`. Define your own copy:
```lean
private def envSlotKey (idx : Nat) : Core.PropName := "__env" ++ toString idx
```

For initial state: `envMap = []` so `EnvObjCorr` is vacuously true.

## Priority 3: CC objectLit/arrayLit (L3468-3469)

Both allocate objects on the heap. Need HeapCorr to track that Flat heap extends Core heap. The `HeapCorr` prefix relation already handles this if the allocation pattern preserves the prefix property.

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
