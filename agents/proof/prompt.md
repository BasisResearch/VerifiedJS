# proof — Close 43 Sorries (8 CC + 2 ANF + 1 Lower + 32 Wasm)

You own Proofs/*.lean and compiler passes. HeapCorr is DONE.

## TASK 0 (DO FIRST): Close L1684 and L2092 — well-formedness

Both are `| some _ => sorry` after `cases sf.heap.objects[addr]?` where `addr ≥ sc.heap.objects.size`.

**Root cause**: We need `addr < sc.heap.objects.size` to eliminate this branch. Then the `¬(addr < sc.heap.objects.size)` case is vacuously unreachable.

**Strategy**: Add `AddrWF` to CC_SimRel — all `.object addr` values reachable from Core state have `addr < sc.heap.objects.size`.

```lean
/-- All object addresses in a value are valid heap addresses. -/
private def ValueAddrWF (v : Core.Value) (heapSize : Nat) : Prop :=
  match v with
  | .object addr => addr < heapSize
  | _ => True

/-- All object addresses in an expression are valid. -/
private def ExprAddrWF (e : Core.Expr) (heapSize : Nat) : Prop :=
  match e with
  | .lit v => ValueAddrWF v heapSize
  -- add cases as needed for compound exprs
  | _ => True
```

Add `ExprAddrWF sc.expr sc.heap.objects.size` to CC_SimRel. Then at L1684/L2092:
- You have `ExprAddrWF (.getProp (.lit (.object addr)) _) sc.heap.objects.size`
- This gives `addr < sc.heap.objects.size`
- Contradicts `¬(addr < sc.heap.objects.size)`
- The `| some _` branch is eliminated

You also need to prove `ExprAddrWF` is preserved by each Core step. Core allocation grows heap and assigns `nextAddr`, so newly allocated addresses are valid. Core env lookups return values that were stored when heap was smaller, but heap only grows, so they stay valid.

**Alternative (simpler, try first)**: Instead of threading through SimRel, try `omega` or `Nat.lt_of_lt_of_le` inline at the sorry site. The `.object addr` came from `sc.heap.objects[addr]?` returning `some props` earlier in the proof, which means `addr < sc.heap.objects.size`. Look up the proof context for that hypothesis.

## TASK 1: L898 captured var (stuttering)

Core: `.var name` → 1 step → value
Flat: `.getEnv (.var envVar) idx` → 2 steps → value

Need multi-step: show Flat reaches same value in 2 steps via `Flat.Steps`.

## TASK 2: L3057 objectLit, L3058 arrayLit, L1609 newObj

BLOCKED on wasmspec fixing allocFreshObject. Skip.

## TASK 3: L1608 call — function body correspondence

Core enters function body. Flat enters function body. Need CC_SimRel preservation through call.

## TASK 4: L3059 functionDef — most complex, do last

## TASK 5: ANF (L106, L1181) — independent of CC

## TASK 6: Lower (L69) — LowerSimRel.init

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
