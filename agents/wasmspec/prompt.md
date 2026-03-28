# wasmspec — CONTINUE: writeLE? + binOp + unOp CASES

## STATUS: 19 Wasm sorries remaining (was 20 last run — good, -1). Target: ≤16 this run (-3).

File: `VerifiedJS/Wasm/Semantics.lean`

## P0: L308 — writeLE?_preserves_size (STILL OPEN)

This is a PURE LEMMA, no semantic complexity. Goal:
```
mem' : ByteArray, h : writeLE? mem addr width value = some mem'
⊢ mem'.size = mem.size
```

The `writeLE?` loop does `ByteArray.set!` at each iteration, which preserves size (index is checked in-bounds by the `if idx < out.size` guard — if out of bounds, returns `none`).

Strategy: The loop is `for k in [0:width]` which is `List.forIn [0, 1, ..., width-1]`. Unfold the `Id.run do` and prove the loop invariant `out.size = mem.size` is preserved.

If direct induction on width is hard, try:
```lean
  -- The loop body only calls set! when idx < out.size, so size is preserved
  -- set! with in-bounds index preserves size
  unfold writeLE? Id.run at h
  simp only [forIn, ForIn.forIn] at h
  sorry -- examine goal after simp, continue from there
```

Or try `lean_multi_attempt` at L308 with:
```
["omega", "simp [writeLE?]", "unfold writeLE? at h; simp [Id.run] at h"]
```

**LSP TIMEOUT WORKAROUND**: This file is 11K+ lines. If lean_goal/lean_multi_attempt timeout:
1. Read the code around L300-310
2. Write the proof directly
3. Build: `lake build VerifiedJS.Wasm.Semantics`
4. Use `lean_diagnostic_messages` on line 308 to check errors

## P1: L10462 and L10715 — binOp/unOp cases

Read 50 lines of context around each sorry. These typically follow the pattern from nearby proved cases:
- Match on operator type
- Show IR evaluation matches Wasm evaluation
- Construct EmitSimRel with updated stack

Write proof by analogy with the nearest proved case above/below the sorry.

## P2: L10768, L10772 — deeper cases

Same approach: read context, find nearest proved case, adapt.

## SKIP: L6675-L6753 (structural decomposition block — 12 sorries, complex), L10775 (callIndirect), L11535 (memoryGrow)

## BUILD: `lake build VerifiedJS.Wasm.Semantics`
## Log to agents/wasmspec/log.md
