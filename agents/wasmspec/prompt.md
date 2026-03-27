# wasmspec — Close binOp trap cases + br/brIf

## CURRENT STATUS: 36 sorry lines (30 non-comment) in Wasm/Semantics.lean

## P0: binOp trap cases (MECHANICAL — 8 sorries)

Use `lean_goal` at each line, then `lean_multi_attempt` to test tactics.

**Stack underflow cases** (L9949, L9952, L10019, L10022):
The stack has fewer than 2 elements. The Wasm step should produce a trap.
```lean
-- Try these tactics:
simp_all [step?, pop2?, trapState, pushTrace]
-- or:
simp [withI32Bin, withI32Rel, withF64Bin, pop2?]; split <;> simp_all [trapState, pushTrace]
```

**Type mismatch cases** (L10008, L10062):
Both values are on the stack but types don't match for the operation.
```lean
-- Try:
cases v1 <;> cases v2 <;> simp_all [withI32Bin, withI32Rel, withF64Bin, trapState, pushTrace]
```

**Other binOp sorries** (L9454, L10068):
Use `lean_goal` to determine what's needed.

## P1: store/store8 (L308 area)
Check `lean_goal` at L308. If this is a top-level sorry guarding something, investigate what it needs.

## P2: call-related sorries (L10376, L10380, L10383)
Use `lean_goal` to check if any are mechanical.

## P3: br/brIf (L10643, L10726)
These involve label manipulation. Use `lean_goal` — if the label list is empty (hlabels_empty), these cases may be impossible to reach (use `contradiction` or `omega`).

## SKIP (architecturally blocked):
- Inner step_sim L6475-6553 (12 sorries) — 1:N mapping, needs redesign
- callIndirect (L10383) — complex
- memoryGrow (L11060) — complex
- L10323 — check first but likely blocked

## APPROACH
1. Start with P0 binOp cases — use lean_multi_attempt aggressively
2. After each 2-3 fixes, build to verify: `lake build VerifiedJS.Wasm.Semantics`
3. Move to P1-P3 only after P0 is done

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
