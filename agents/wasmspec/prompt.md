# wasmspec — Close binOp trap cases (8 mechanical sorries)

## STATUS: 27 Wasm sorry tokens. Overall project: 99→58 (-41). CC made huge progress. Now Wasm needs to contribute.

## P0: binOp trap cases — THESE ARE MECHANICAL, CLOSE THEM NOW

Use `lean_goal` at each line, then `lean_multi_attempt` aggressively.

**Stack underflow (4 sorries):**
- L9953: withI32Bin/withI32Rel/withF64Bin stack underflow → trap
- L9956: only 1 element → trap
- L10023: same pattern (second binOp group)
- L10026: same pattern

```lean
-- Try these in lean_multi_attempt:
["simp_all [step?, pop2?, trapState, pushTrace]",
 "simp [withI32Bin, pop2?]; split <;> simp_all [trapState, pushTrace]",
 "simp [withF64Bin, pop2?]; split <;> simp_all [trapState, pushTrace]",
 "omega"]
```

**Type mismatch (2 sorries):**
- L10012: both values on stack, types don't match
- L10066: same pattern

```lean
-- Try:
["cases v1 <;> cases v2 <;> simp_all [withI32Bin, withI32Rel, withF64Bin, trapState, pushTrace]",
 "simp_all [withI32Bin, withI32Rel, withF64Bin]; split <;> simp_all [trapState, pushTrace]"]
```

**Other binOp (2 sorries):**
- L10072: Use `lean_goal` first
- L10327: Use `lean_goal` first

## P1: store/store8 (L308)
`lean_goal` at L308 to understand what's needed. This is a top-level sorry — could unlock structural progress.

## P2: call-related (L10380, L10384)
`lean_goal` at each. If mechanical, close them.

## P3: br/brIf (L10647, L10730)
Label manipulation. Use `lean_goal` — if labels list is empty, use `contradiction` or `omega`.

## SKIP (architecturally blocked):
- Inner step_sim L6475-6553 (12 sorries) — 1:N mapping, needs redesign
- callIndirect (L10387) — complex
- memoryGrow (L11064) — complex

## APPROACH
1. Start with P0 — use lean_multi_attempt on all 8 binOp cases
2. Build after every 2-3 fixes: `lake build VerifiedJS.Wasm.Semantics`
3. Move to P1-P3 only after P0 is done

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
