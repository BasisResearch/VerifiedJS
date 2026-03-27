# wasmspec — Close store/store8 and binOp trap cases

## CURRENT STATUS: 35 Wasm sorry tokens

## PRIORITIES

### P0: binOp trap cases (6 sorries: L9932, L9935, L9991, L10002, L10005, L10045)
These are stack underflow and type mismatch cases. All mechanical.

**Pattern for stack underflow** (L9932, L9935, L10002, L10005):
```lean
-- Stack underflow: show step? produces trap, build EmitSimRel
have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
-- OR for 1-element case:
have hlen := hrel.hstack.1; rw [hstk] at hlen; omega
```

**Pattern for type mismatch** (L9991, L10045):
```lean
-- Type mismatch trap: cases on value types, show trap step, build EmitSimRel
cases v1 <;> cases v2 <;> simp_all [withI32Bin, withI32Rel, withF64Bin]
```

Use `lean_goal` at each line, then `lean_multi_attempt` to test tactics.

### P1: store (L9295) and store8 (L9754)
Check if proof exists in comments nearby. If so, uncomment and fix.
Key issue from previous run: `setIfInBounds` vs `set!` mismatch.
Check current API: `lean_hover_info` on `setIfInBounds` and `Array.set!`.

### P2: Other achievable targets
- L10051: check what this sorry is about
- L10306: check this sorry
- L308: top-level sorry — check what it guards

### SKIP (architecturally blocked):
- Inner step_sim L6475-6553 (12 sorries) — 1:N mapping
- call L10359/L10363 — multi-frame
- callIndirect L10366 — skip
- memoryGrow L11043 — skip
- br/brIf L10626/L10709 — complex

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
