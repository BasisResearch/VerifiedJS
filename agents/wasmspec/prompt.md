# wasmspec — FIX BUILD FIRST, THEN CLOSE SORRIES

## URGENT: BUILD IS BROKEN — FIX IMMEDIATELY

Error at L9956: `don't know how to synthesize placeholder for argument 'msg'`

The `TraceEvent.trap _` at L9956 can't infer the message because it's inside `all_goals` applying to 9 different binOp operations, each with a different trap message (e.g., "type mismatch in i32.add", "type mismatch in i32.sub", etc.).

**FIX**: Replace lines 9955-9967 (the `| [] =>` arm with the `have hw` proof) with:
```lean
                | [] =>
                  sorry -- binOp stack underflow empty: trap msg depends on op, needs per-case proof
```

This restores the sorry that was there before your proof attempt. BUILD IMMEDIATELY after this fix.

The problem is that `all_goals` can't use a unified `have hw` statement when the trap message varies per case. You need EITHER:
1. Split the `all_goals` into per-operation cases, each with the right message, OR
2. Use `obtain ⟨msg, hw⟩ := ...` to existentially bind the message

## STATUS: Wasm sorry count went UP from 24→27. WRONG DIRECTION.

## P0: Fix the build (above)

## P1: Close binOp sorries at L10045, L10056, L10059, L10099, L10105, L10360

Use `lean_goal` at each, then `lean_multi_attempt`:
```
["simp_all [step?, pop2?, trapState, pushTrace]",
 "simp [withI32Bin, pop2?]; split <;> simp_all [trapState, pushTrace]",
 "cases v1 <;> cases v2 <;> simp_all [withI32Bin, withI32Rel, withF64Bin, trapState, pushTrace]",
 "simp [withF64Bin, pop2?]; split <;> simp_all [trapState, pushTrace]"]
```

## P2: call (L10413, L10417), br/brIf (L10680, L10763)

## SKIP: Inner step_sim L6475-6553, callIndirect, memoryGrow, L308

## RULES:
1. FIX BUILD FIRST
2. Build after EVERY fix
3. If it doesn't compile, REVERT immediately
4. Do NOT add more sorry tokens

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
