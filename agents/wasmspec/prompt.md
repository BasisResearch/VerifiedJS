# wasmspec — Fix allocFreshObject (ONLY TASK THIS RUN)

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## TASK 0 — THE ONLY THING YOU DO THIS RUN

Fix `allocFreshObject` in **both** Flat/Semantics.lean AND ANF/Semantics.lean. This has been blocking 3 CC proof sorries for 10+ runs.

### Step 1: Flat/Semantics.lean line 194

Replace:
```lean
private def allocFreshObject (h : Core.Heap) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push [], nextAddr := addr + 1 }
  (addr, h')
```

With:
```lean
private def allocFreshObject (h : Core.Heap) (props : List (Core.PropName × Core.Value) := []) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push props, nextAddr := addr + 1 }
  (addr, h')
```

### Step 2: Flat/Semantics.lean objectLit case (~line 791-797)

Replace lines 795-796:
```lean
          let (addr, heap') := allocFreshObject s.heap
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
```

With:
```lean
          let heapProps := props.filterMap fun (k, e) =>
            match exprValue? e with | some v => some (k, flatToCoreValue v) | none => none
          let (addr, heap') := allocFreshObject s.heap heapProps
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
```

NOTE: `exprValue?` returns `Flat.Value`, heap needs `Core.Value`, so you MUST use `flatToCoreValue v`.

### Step 3: Flat/Semantics.lean arrayLit case (~line 812)

Replace line 812:
```lean
          let (addr, heap') := allocFreshObject s.heap
```

With:
```lean
          let heapProps : List (Core.PropName × Core.Value) := elems.enum.filterMap fun (i, e) =>
            match exprValue? e with | some v => some (toString i, flatToCoreValue v) | none => none
          let (addr, heap') := allocFreshObject s.heap heapProps
```

### Step 4: newObj case (~line 470) — NO CHANGE needed

`allocFreshObject s.heap` already passes `[]` by default. Leave it as-is.

### Step 5: ANF/Semantics.lean line 168

Same signature change as Step 1:
```lean
private def allocFreshObject (h : Core.Heap) (props : List (Core.PropName × Core.Value) := []) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap := { objects := h.objects.push props, nextAddr := addr + 1 }
  (addr, h')
```

### Step 6: ANF/Semantics.lean objectLit case (~line 289)

Replace line 289:
```lean
          let (addr, heap') := allocFreshObject s.heap
```

With:
```lean
          let heapProps := props.filterMap fun (k, t) =>
            match evalTrivial s.env t with | .ok v => some (k, flatToCoreValue v) | .error _ => none
          let (addr, heap') := allocFreshObject s.heap heapProps
```

### Step 7: ANF/Semantics.lean arrayLit case (~line 295)

Replace line 295:
```lean
          let (addr, heap') := allocFreshObject s.heap
```

With:
```lean
          let heapProps : List (Core.PropName × Core.Value) := elems.enum.filterMap fun (i, t) =>
            match evalTrivial s.env t with | .ok v => some (toString i, flatToCoreValue v) | .error _ => none
          let (addr, heap') := allocFreshObject s.heap heapProps
```

### Step 8: Build
```bash
bash scripts/lake_build_concise.sh
```

DO NOT do anything else this run. Just these edits and build.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
