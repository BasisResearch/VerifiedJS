# proof — Add EnvAddrWF + HeapAddrWF to CC_SimRel, close remaining CC sorries

You own Proofs/*.lean and compiler passes. ExprAddrWF is defined and in CC_SimRel. ExprAddrWF_mono is proved.

## TASK 0 (DO FIRST): Add EnvAddrWF and HeapAddrWF to CC_SimRel

The 4 remaining `sorry /- ExprAddrWF -/` (L1063, L1768, L2173, L4222) need values from env/heap to satisfy ValueAddrWF. You must add two new invariants to CC_SimRel.

### Step 1: Add definitions (after ExprAddrWF_mono, ~L683)

```lean
private def EnvAddrWF (env : Core.Env) (heapSize : Nat) : Prop :=
  ∀ name v, env.lookup name = some v → ValueAddrWF v heapSize

private def HeapValuesWF (heap : Core.Heap) : Prop :=
  ∀ addr, addr < heap.objects.size →
    ∀ props, heap.objects[addr]? = some props →
      ∀ kv, kv ∈ props → ValueAddrWF kv.2 heap.objects.size

private theorem EnvAddrWF_mono {env : Core.Env} {n m : Nat}
    (h : EnvAddrWF env n) (hle : n ≤ m) : EnvAddrWF env m :=
  fun name v hlookup => ValueAddrWF_mono (h name v hlookup) hle

private theorem EnvAddrWF_extend {env : Core.Env} {n : Nat}
    (h : EnvAddrWF env n) (name : String) (v : Core.Value)
    (hv : ValueAddrWF v n) : EnvAddrWF (env.extend name v) n := by
  intro n' v' hlookup
  simp [Core.Env.extend, Core.Env.lookup] at hlookup
  cases hlookup with
  | inl heq => exact heq.2 ▸ hv
  | inr hother => exact h n' v' hother

private theorem EnvAddrWF_empty (n : Nat) : EnvAddrWF Core.Env.empty n := by
  intro name v h; simp [Core.Env.empty, Core.Env.lookup] at h
```

### Step 2: Modify CC_SimRel (L687-695)

Change from:
```lean
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  EnvCorr sc.env sf.env ∧
  HeapCorr sc.heap sf.heap ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st
```

To:
```lean
private def CC_SimRel (_s : Core.Program) (_t : Flat.Program)
    (sf : Flat.State) (sc : Core.State) : Prop :=
  sf.trace = sc.trace ∧
  EnvCorr sc.env sf.env ∧
  HeapCorr sc.heap sf.heap ∧
  noCallFrameReturn sc.expr = true ∧
  ExprAddrWF sc.expr sc.heap.objects.size ∧
  EnvAddrWF sc.env sc.heap.objects.size ∧
  ∃ (scope : List String) (envVar : String) (envMap : Flat.EnvMapping) (st st' : Flat.CCState),
    (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st
```

Note: Only adding EnvAddrWF (not HeapValuesWF). L1768/L2173 can be closed differently — see Step 4.

### Step 3: Fix closureConvert_init_related (L697-717)

After `refine ⟨rfl, ?_, HeapCorr_refl _, h_wf, ?_, ?_, ?_⟩` add:
```lean
  · -- EnvAddrWF: initial env has "console" → .object 0, heap has 1 object
    exact EnvAddrWF_extend (EnvAddrWF_empty 1) "console" (.object 0) (by simp [ValueAddrWF]; omega)
```

### Step 4: Fix all CC_SimRel tuple sites

The tuple now has 7 fields: `⟨trace, envCorr, heapCorr, noCallFrame, exprAddrWF, envAddrWF, ∃scope...⟩`

For MOST cases (env unchanged, heap unchanged), just add `henvwf` (the destructured EnvAddrWF hypothesis). When destructuring CC_SimRel, add `henvwf` in position 6:
```lean
obtain ⟨htrace, henvCorr, hheap, hncfr, hexprwf, henvwf, scope, envVar, envMap, st, st', hconv⟩ := hrel
```

**When building the result tuple**, add `henvwf` after the ExprAddrWF field. For cases where:
- **Env unchanged, heap unchanged**: `henvwf`
- **Env extended with value v** (let binding): `EnvAddrWF_extend henvwf name v (by ...)` where `by ...` proves `ValueAddrWF v sc.heap.objects.size`
- **Heap grows** (allocFreshObject): `EnvAddrWF_mono henvwf (by omega)`

### Step 5: Close the 4 ExprAddrWF sorries

**L1063** (var captured, `cv` from env): Replace `sorry /- ExprAddrWF -/` with:
```lean
(by simp [ExprAddrWF]; exact henvwf name cv hcenv)
```

**L4222** (this found, `cv` from env): Replace `sorry /- ExprAddrWF -/` with:
```lean
(by simp [ExprAddrWF]; exact henvwf "this" cv hcenv)
```

**L1768** (getProp result from heap): The value `v` comes from `sc.heap`. Use `HeapCorr` + the fact that Core.step? preserves the heap object. The result expression is `.lit v` where `v` came from a property lookup. Since the heap didn't change and the original expression had ExprAddrWF, the object address was valid. The property value's ValueAddrWF needs to be established from the heap structure. Try:
```lean
(by simp [ExprAddrWF]; cases v <;> simp [ValueAddrWF] <;> try rfl; sorry /- HeapValuesWF -/)
```
If this doesn't close fully, you may need HeapValuesWF in CC_SimRel as well. Check `lean_goal` first.

**L2173** (getIndex result from heap): Same pattern as L1768.

## TASK 1: Close L1003 (captured var multi-step)

L1003 is `sorry` for the captured variable case. Core does `.var name` → looks up env → `.lit cv`. Flat does `.getEnv (.var envVar) idx` which is multi-step. This needs to show the Flat multi-step execution matches. Use `lean_goal` at L1003 to see what's needed.

## TASK 2: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main theorem
- **ANFConvertCorrect.lean:1181**: induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
- DO NOT break the build — if CC_SimRel change causes cascading errors, fix them ALL before building
