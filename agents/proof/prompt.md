# proof — Close CC and ANF sorries

You own ClosureConvertCorrect.lean, ANFConvertCorrect.lean, LowerCorrect.lean.

## Current sorry count: 12 (9 CC + 2 ANF + 1 Lower)

### CC sorries (ClosureConvertCorrect.lean)
```
L829   forIn           sorry — UNPROVABLE (stub, skip)
L830   forOf           sorry — UNPROVABLE (stub, skip)
L1113  var (captured)  sorry — needs env object lookup via heap
L1258  let-value       sorry — convertExpr unfold blocked
L1824  call            sorry — needs env/heap/funcs correspondence
L1825  newObj          sorry — needs env/heap correspondence
L3474  objectLit       sorry — needs heap correspondence (allocObjectWithProps)
L3475  arrayLit        sorry — needs heap correspondence
L3476  functionDef     sorry — needs env/heap/funcs + CC state
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

## Priority 1: CC L1258 (let-value case)

This is at the `let` case where the init expression IS a value (`Core.exprValue? init = some v`). Both Core and Flat step to the body with env extended. The proof pattern:

1. Core steps: `Core.step? sc = some (.silent, sc')` where `sc'` has `env.extend name v` and `expr = body`
2. Flat steps: `Flat.step? sf = some (.silent, sf')` where `sf'` has `env.extend name (convertValue v)` and `expr = body'`

```lean
-- After subst ha_lit, hconv gives sf.expr = .let name (.lit (convertValue v)) body'
-- Flat step for let-value is deterministic:
have hflat_step : Flat.step? sf = some (.silent, ⟨body', sf.env.extend name (Flat.convertValue v), sf.heap, sf.trace, sf.funcs, sf.callStack⟩) := by
  rw [show sf = {sf with expr := .let name (.lit (Flat.convertValue v)) body'} from by cases sf; simp_all]
  simp [Flat.step?, Flat.exprValue?]
-- Core step for let-value:
have hcore_step : Core.step? sc = some (.silent, ⟨body, sc.env.extend name v, sc.heap, sc.trace, sc.funcs, sc.callStack⟩) := by
  rw [show sc = {sc with expr := .let name (.lit v) body} from by cases sc; simp_all]
  simp [Core.step?, Core.exprValue?]
-- Then use EnvCorr_extend + IH on body
```

The key is that `convertExpr body (name::scope) ...` produces `body'`, and the IH gives you the simulation for `body` at depth `n-1`.

## Priority 2: CC objectLit (L3474)

Both Core and Flat allocate an object on the heap. **Key issue**: HeapCorr gives `≤` not `=` for heap sizes. If sizes differ, addrs won't match.

**Check `HeapCorr` definition** — if it has `size_eq`, use it. Otherwise add `heap_size_eq : sc.heap.objects.size = sf.heap.objects.size` to CC_SimRel and prove it's an invariant.

## Priority 3: ANF L1177 (nested seq — ARCHITECTURAL)

Skip for now unless CC sorries are all done. See leftSpineCount approach:
```lean
def leftSpineCount : Flat.Expr → Nat
  | .seq a _ => leftSpineCount a + 1
  | _ => 0
```

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — fix ALL cascading errors before building
