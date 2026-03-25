# proof — Close CC and ANF sorries

You own ClosureConvertCorrect.lean, ANFConvertCorrect.lean, LowerCorrect.lean.

## Current sorry count: 11 (8 CC + 2 ANF + 1 Lower)

### CC sorries (ClosureConvertCorrect.lean)
```
L829   forIn           sorry — UNPROVABLE (stub, skip)
L830   forOf           sorry — UNPROVABLE (stub, skip)
L1113  var (captured)  sorry — ARCHITECTURAL: needs stuttering sim (see below)
L1897  call            sorry — needs env/heap/funcs correspondence
L1898  newObj          sorry — needs env/heap correspondence
L3547  objectLit       sorry — needs WeakHeapCorr (see Priority 1)
L3548  arrayLit        sorry — needs WeakHeapCorr (see Priority 1)
L3549  functionDef     sorry — needs env/heap/funcs + CC state
```

**L829/L830 are expected sorry — skip them.**

### ANF sorries (ANFConvertCorrect.lean)
```
L106   anfConvert_step_star  sorry — ENTIRE step simulation theorem
L1365  nested seq case        sorry — in anfConvert_halt_star_aux
```

### Lower sorry (LowerCorrect.lean)
```
L69    LowerSimRel.init  by sorry — init field proof (owned by wasmspec, skip)
```

## Priority 1: objectLit/arrayLit (L3547-3548)

Both sides allocate on heap. Problem: `HeapCorr` requires `cheap.objects[addr]? = fheap.objects[addr]?` (identical objects), but Flat stores `convertValue v` while Core stores `v`. When values contain `.function idx`, `convertValue` changes it to `.closure idx 0`.

**Fix**: Weaken `HeapCorr` to allow `convertValue` relationship:

```lean
private def WeakHeapCorr (cheap fheap : Core.Heap) : Prop :=
  cheap.objects.size ≤ fheap.objects.size ∧
  ∀ addr, addr < cheap.objects.size →
    ∀ kv, kv ∈ cheap.objects[addr]'(by omega) →
      ∃ kv', kv' ∈ fheap.objects[addr]'(by omega) ∧
        kv'.1 = kv.1 ∧ kv'.2 = Flat.convertValue kv.2
```

OR simpler: keep `HeapCorr` as-is but add a lemma that objectLit with no `.function` values in props produces identical objects:

```lean
/-- When all values in props are non-function, convertValue is identity on them. -/
private theorem convertValue_non_function (v : Core.Value) (h : ¬ v.isFunction) :
    Flat.convertValue v = v := by
  cases v <;> simp [Flat.convertValue, Core.Value.isFunction] at * <;> contradiction
```

For objectLit where all prop values are non-function (common case), `HeapCorr_alloc_both` works directly. For the general case with function values, you need `WeakHeapCorr`.

**Proof sketch for objectLit (non-function values)**:
1. Both Core and Flat evaluate props to values, allocate on heap
2. `HeapCorr_alloc_both` needs `ch.objects.size = fh.objects.size` — may not hold if Flat allocated env objects
3. Use `HeapCorr_alloc_right` pattern if Flat heap is larger

**Practical approach**: Start with the stepping sub-expression case (when some prop is not yet a value). This follows the exact same pattern as `binary`, `seq`, etc. — 1-1 stepping inside the prop list. This is the MOST of the proof work.

## Priority 2: CC L1113 (captured var) — ARCHITECTURAL BLOCKER

When `lookupEnv envMap name = some idx`, `convertExpr (.var name)` = `.getEnv (.var envVar) idx`.

**Problem**: Flat needs 2 steps (resolve envVar, then lookup slot) but Core needs 1 step (resolve name). The current 1-1 `step_simulation` can't handle this. After Flat step 1, `sf'.expr = .getEnv (.lit (.object envPtr)) idx` which is NOT the output of any `convertExpr`.

**Fix**: Change `step_simulation` to allow stuttering:

```lean
theorem step_simulation (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t) :
    ∀ sc sf ev sf',
    CC_SimRel s t sf sc → Flat.Step sf ev sf' →
    (∃ sc', Core.Step sc ev sc' ∧ CC_SimRel s t sf' sc') ∨
    (ev = .silent ∧ CC_SimRel_intermediate s t sf' sc ∧
     Flat.exprMeasure sf'.expr < Flat.exprMeasure sf.expr)
```

Where `CC_SimRel_intermediate` allows `.getEnv (.lit ...) idx` states:

```lean
private inductive ExprCorr : Core.Expr → Flat.Expr → Prop
  | convert (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
      (st : Flat.CCState) :
      ExprCorr e (Flat.convertExpr e scope envVar envMap st).1
  | getEnvReady (envPtr : Nat) (idx : Nat) (cv : Core.Value) :
      ExprCorr (.lit cv) (.getEnv (.lit (.object envPtr)) idx)
```

**DO NOT attempt L1113 until you restructure step_simulation. Do objectLit/arrayLit first.**

## Priority 3: call/newObj (L1897-1898)

These have the same stuttering issue as captured var (makeClosure takes extra steps). Defer until after Priority 2 restructuring.

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
