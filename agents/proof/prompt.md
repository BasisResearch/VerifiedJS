# proof — Close 44 Sorries (8 CC + 2 ANF + 1 Lower + 33 Wasm)

You own Proofs/*.lean and compiler passes. HeapCorr is DONE.

## TASK 0 (DO FIRST): Close L1706 and L2114 — well-formedness

Both sorry sites are in the `| some _ =>` branch after `cases sf.heap.objects[addr]?` where `addr ≥ sc.heap.objects.size`.

**The branch is unreachable.** Here's why: `addr` comes from Core expression `.getProp (.lit (.object addr)) prop` (or `.getIndex`). Core allocated this `addr`, so `addr < sc.heap.objects.size` must hold. But the current proof splits on `Nat.lt_or_ge addr sc.heap.objects.size` and can't dismiss the `≥` branch.

**Fix: Add `ExprAddrWF` to CC_SimRel.**

```lean
/-- All object addresses in a Core value are valid heap addresses. -/
private def ValueAddrWF (v : Core.Value) (heapSize : Nat) : Prop :=
  match v with
  | .object addr => addr < heapSize
  | _ => True

/-- All object addresses in a Core expression are valid heap addresses.
    Only needs cases that appear in sorry sites (getProp, getIndex, lit). -/
private def ExprAddrWF : Core.Expr → Nat → Prop
  | .lit v, n => ValueAddrWF v n
  | .getProp e _, n => ExprAddrWF e n
  | .getIndex e _, n => ExprAddrWF e n
  | _, _ => True
```

Add `ExprAddrWF sc.expr sc.heap.objects.size` to CC_SimRel:

```lean
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  EnvCorr sc.env sf.env ∧
  HeapCorr sc.heap sf.heap ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧  -- ADD THIS
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st
```

Then at L1706/L2114: `ExprAddrWF (.getProp (.lit (.object addr)) prop) sc.heap.objects.size` gives `addr < sc.heap.objects.size`, which contradicts `hge : addr ≥ sc.heap.objects.size`. Replace `sorry` with `exact absurd (haddr) (Nat.not_lt.mpr hge)` (adjust names to match your proof context).

**closureConvert_init_related**: Initial expression has no `.object` values (it's the program body with only variable references and literals), so `ExprAddrWF` holds trivially — likely `trivial` or `simp [ExprAddrWF]`.

**Preservation**: Each Core step case must preserve ExprAddrWF:
- objectLit/arrayLit: `addr = heap.nextAddr`, new heap has `objects.size = old + 1`, so `addr < new_size`. Use `omega`.
- Other steps that don't allocate: heap unchanged, expr may change but stays in bounds.
- Env lookups: values came from earlier heap state, heap only grows → still valid. Needs `ValueAddrWF` in EnvCorr (you may need `∀ v ∈ env, ValueAddrWF v heap.size`).

**SIMPLER ALTERNATIVE (try first)**: Look at the proof context at L1706. The `addr` may already be constrained by a hypothesis from an earlier case split. Search for `h` or `hc` hypotheses containing `addr`. If you can find `sc.heap.objects[addr]? = some _` earlier in the proof tree (from the Core step), that directly gives `addr < sc.heap.objects.size` via `Array.getElem?_some`.

## TASK 1: L920 captured var (stuttering)

Core: `.var name` → 1 step → value
Flat: `.getEnv (.var envVar) idx` → 2 steps → value

Need multi-step: show Flat reaches same value in 2 steps via `Flat.Steps`.

## TASK 2: L3079 objectLit, L3080 arrayLit, L1631 newObj

BLOCKED on wasmspec fixing allocFreshObject. Skip.

## TASK 3: L1630 call — function body correspondence

Core enters function body. Flat enters function body. Need CC_SimRel preservation through call.

## TASK 4: L3081 functionDef — most complex, do last

## TASK 5: ANF (L106, L1181) — independent of CC

## TASK 6: Lower (L69) — LowerSimRel.init

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
