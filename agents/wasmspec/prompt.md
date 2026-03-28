# wasmspec — STOP DECOMPOSING. START CLOSING.

## STATUS: Wasm sorry count went UP from 24→27. That is WRONG DIRECTION.

You have been decomposing monolithic sorries into sub-cases, which creates MORE sorry tokens. That was fine initially but now you need to CLOSE cases, not open more.

## P0: binOp cases — 6 mechanical sorries at L10045, L10056, L10059, L10099, L10105, L10360

These are ALL the same pattern: stack underflow or type mismatch → trap.

Use `lean_goal` at each, then `lean_multi_attempt`:
```
["simp_all [step?, pop2?, trapState, pushTrace]",
 "simp [withI32Bin, pop2?]; split <;> simp_all [trapState, pushTrace]",
 "cases v1 <;> cases v2 <;> simp_all [withI32Bin, withI32Rel, withF64Bin, trapState, pushTrace]",
 "simp [withF64Bin, pop2?]; split <;> simp_all [trapState, pushTrace]"]
```

After each fix, BUILD: `lake build VerifiedJS.Wasm.Semantics`

## P1: call (L10413, L10417) — 2 sorries

`lean_goal` at each. If mechanical, close them.

## P2: br/brIf (L10680, L10763) — 2 sorries

Label manipulation. `lean_goal` first. Try `contradiction` or `omega` if labels list is empty.

## SKIP (do NOT touch — architecturally blocked):
- Inner step_sim L6475-6553 (12 sorries)
- callIndirect (L10420)
- memoryGrow (L11097)
- L308 (top-level)

## RULES:
1. Build after EVERY fix
2. If it doesn't compile, REVERT immediately
3. Do NOT add more sorry tokens
4. Target: close at least 4 of the 6 binOp cases this run

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
