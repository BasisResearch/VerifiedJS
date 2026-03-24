# wasmspec — Fix allocFreshObject (12TH ESCALATION — CRITICAL)

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## THE ONLY TASK: 4 edits, then build

You have been assigned this task for 12 consecutive runs and failed every time due to timeouts. DO NOT read files, DO NOT use lean_goal, DO NOT investigate. Just make these 4 edits and build. Total time budget: 10 minutes.

### Edit 1: Flat/Semantics.lean line 194

OLD (exact match):
```
private def allocFreshObject (h : Core.Heap) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push [], nextAddr := addr + 1 }
  (addr, h')
```

NEW:
```
private def allocFreshObject (h : Core.Heap) (props : List (Core.PropName × Core.Value) := []) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push props, nextAddr := addr + 1 }
  (addr, h')
```

### Edit 2: Flat/Semantics.lean line 795

OLD (exact match):
```
          let (addr, heap') := allocFreshObject s.heap
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
```

NEW:
```
          let heapProps := props.filterMap fun (k, e) =>
            match exprValue? e with | some v => some (k, flatToCoreValue v) | none => none
          let (addr, heap') := allocFreshObject s.heap heapProps
          let s' := pushTrace { s with expr := .lit (.object addr), heap := heap' } .silent
```

### Edit 3: Flat/Semantics.lean line 812

OLD (exact match):
```
          let (addr, heap') := allocFreshObject s.heap
```

NEW:
```
          let heapProps : List (Core.PropName × Core.Value) := elems.enum.filterMap fun (i, e) =>
            match exprValue? e with | some v => some (toString i, flatToCoreValue v) | none => none
          let (addr, heap') := allocFreshObject s.heap heapProps
```

### Edit 4: ANF/Semantics.lean line 168

OLD (exact match):
```
private def allocFreshObject (h : Core.Heap) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap := { objects := h.objects.push [], nextAddr := addr + 1 }
  (addr, h')
```

NEW:
```
private def allocFreshObject (h : Core.Heap) (props : List (Core.PropName × Core.Value) := []) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap := { objects := h.objects.push props, nextAddr := addr + 1 }
  (addr, h')
```

### Then build
```bash
bash scripts/lake_build_concise.sh
```

DO NOT do ANF objectLit/arrayLit edits — leave those for next run. Just these 4 edits.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- DO NOT read files, investigate, or use lean tools. Just edit and build.
