# wasmspec — Fix allocFreshObject + Close Wasm Sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## TASK 0 (DO FIRST): Fix allocFreshObject in Flat/Semantics.lean

`allocFreshObject` at line 194 pushes `[]` (empty properties) to heap. Core pushes actual properties. This blocks 3 CC proof sorries (objectLit/arrayLit/newObj).

Change `allocFreshObject` to take a properties parameter:

```lean
private def allocFreshObject (h : Core.Heap) (props : List (Core.PropName × Core.Value) := []) : Nat × Core.Heap :=
  let addr := h.nextAddr
  let h' : Core.Heap :=
    { objects := h.objects.push props, nextAddr := addr + 1 }
  (addr, h')
```

Then update the 3 call sites:
- **objectLit** (~line 795): Extract values from props and pass them:
  ```lean
  let heapProps := props.filterMap fun (k, e) =>
    match Flat.exprValue? e with | some v => some (k, v) | none => none
  let (addr, heap') := allocFreshObject s.heap heapProps
  ```
- **arrayLit** (~line 812): Same pattern with indexed props:
  ```lean
  let heapProps := elems.enum.filterMap fun (i, e) =>
    match Flat.exprValue? e with | some v => some (.index i, v) | none => none
  let (addr, heap') := allocFreshObject s.heap heapProps
  ```
- **newObj** (~line 470): Keep `[]` (new objects start empty, same as Core).

Build and verify nothing breaks.

## TASK 1: Make `irTypeToValType` public in Emit.lean

Line 12: Change `private def irTypeToValType` to `def irTypeToValType`. This unblocks the `emit_globals_init_valcorr` sorry at Wasm/Semantics.lean:6833.

## TASK 2: Close easy EmitSimRel step_sim cases

The `.unOp .i32` case is fully proved and shows the pattern. Apply it to:
- `.binOp` (line 7445) — IR and Wasm binary ops use same semantics
- `.load` (line 7436) — memory access
- `.store` / `.store8` (lines 7439, 7442) — memory write
- `.memoryGrow` (line 7915) — memory growth

Use `lean_multi_attempt` to test tactics before editing.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Cite WasmCert-Coq: `-- WASMCERT: file:L1-L10` + `-- |` verbatim text
- `bash scripts/verify_wasmcert_refs.sh` every run
- Log to agents/wasmspec/log.md
